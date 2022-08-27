# This file is part of the paper "Irreducible Contact Curves via graph stratification" by Giosuè Muratore
# The result of the paper are obtained using the number of contact curves given in the paper:
# "Enumeration of Contact Curves via Torus Actions" (same author), and removing the number of 
# reducible one using the following code:
# include("Counting_Reducibles_Contact_Curves.jl")
# count_curves(3,3)
# count_curves(3,4)
# count_curves(3,5)
# count_curves(5,2)

using Combinatorics
using Graphs

import Graphs.Experimental

function get_Smooth(n::Int64, deg::Int64, ex::Dict)::Int64

    dims = [count(i -> ex[i] == d-1, keys(ex)) for d in 1:n+1]
    
    # if there is some H^0, return 0
    if dims[1] != 0 return 0 end

    # if the dimension does not match, return 0
    if ((n-1)*deg + n-2 + length(keys(ex))) != sum(d -> (d-1)*dims[d], eachindex(dims))
        return 0
    end

    if n == 3
        if deg == 1
            if dims[3:4] == [1, 1]
                return 1
            end
            if dims[3:4] == [3, 0]
                return 2
            end
            return 0
        end
        
        if deg == 2
            return 0
        end
        if deg == 3
            if dims[3:4] == [1, 3]
                return 3*(3^dims[2])
            end
            if dims[3:4] == [3, 2]
                return 18*(3^dims[2])
            end
            if dims[3:4] == [5, 1]
                return 132*(3^dims[2])
            end
            if dims[3:4] == [7, 0]
                return 1080*(3^dims[2])
            end
            return 0
        end
        if deg == 4
            if dims[3:4] == [1, 4]
                return 16*(deg^dims[2])
            end
            if dims[3:4] == [3, 3]
                return 128*(deg^dims[2])
            end
            if dims[3:4] == [5, 2]
                return 1216*(deg^dims[2])
            end
            if dims[3:4] == [7, 1]
                return 12800*(deg^dims[2])
            end
            if dims[3:4] == [9, 0]
                return 145664*(deg^dims[2])
            end
        end
    end

    if n==5
        if deg == 1
            if dims[3:6] == [7, 0, 0, 0] 
                return 14
            end
            if dims[3:6] == [5, 1, 0, 0] 
                return 9
            end
            if dims[3:6] == [4, 0, 1, 0] 
                return 4
            end
            if dims[3:6] == [3, 2, 0, 0]
                return 6
            end
            if dims[3:6] == [2, 1, 1, 0]
                return 3
            end
            if dims[3:6] == [1, 3, 0, 0]
                return 4
            end
            if dims[3:6] == [1, 1, 0, 1]
                return 1
            end
            if dims[3:6] == [1, 0, 2, 0]
                return 2
            end
            if dims[3:6] == [0, 2, 1, 0]
                return 2
            end
            if dims[3:6] == [0, 0, 1, 1]
                return 1
            end
            return 0
        end
    end
    
    try
        exs = "[ "
        for m in keys(ex)
            exs *= string(ex[m])*" "
        end
        # exs[end] = ']'
        exs *= "]"
        error(string("Value missing: degree = ",deg,", exponents = ",exs))
    catch e
        printstyled(stderr,"ERROR: ", bold=true, color=:red)
        printstyled(stderr,sprint(showerror,e), color=:light_red)
        println(stderr)
        return 0
    end
    return 0
end

function Red_rec(n::Int64, g::Graph, degs::Vector{Int64}, mark::Dict, ex::Dict)::Int64

    if nv(g) == 1
        return get_Smooth(n, degs[1], ex)
    end
    
    ans = 0
    vert_rem = 0
    old_powered_vert = 0
    new_powered_vert = 0
    for v in vertices(g)
        if length(all_neighbors(g,v)) == 1
            vert_rem = copy(v)
            old_powered_vert = all_neighbors(g,v)[1]
            break
        end
    end

    sg, vmap = induced_subgraph(g, [i for i in vertices(g) if i!=vert_rem])
    
    for v in vertices(sg)
        if vmap[v] == old_powered_vert
            new_powered_vert = v
            break
        end
        
    end

    new_degs = Vector{Int64}(undef, nv(sg))
    new_mark = Dict()
    new_ex = Dict()
    ex_vert_rem = Dict()
    
    for m in keys(mark)
        if mark[m] == vert_rem
            ex_vert_rem[m] = ex[m]
            continue
        end

        for v in vertices(sg)
            if vmap[v] == mark[m]
                new_mark[m] = v
                break
            end
        end

        new_ex[m] = ex[m]
    end

    added_mark = maximum(keys(mark)) + 1
    new_mark[added_mark] = new_powered_vert

    for v in vertices(sg)
        new_degs[v] = degs[vmap[v]]
    end

    for j in 1:(n-1)
        ex_vert_rem[added_mark] = n-j
        s = get_Smooth(n, degs[vert_rem], ex_vert_rem)
        s == 0 && continue        
        new_ex[added_mark] = j
        ans += Red_rec(n, sg, new_degs, new_mark, new_ex)*s
        break
    end

    return ans

end

function Count_reducible_contact(n::Int64, d::Int64, ex_v::Vector{Int64})::Int64

    n_mark = length(ex_v)
    ex = Dict(1:n_mark .=> ex_v)

    local ans = 0   #::Vector{Int64} = [0 for _ in 1:Threads.nthreads()]
    local ans_g = 0 #::Vector{Int64} = [0 for _ in 1:Threads.nthreads()] Threads.@threads 

    for n_vert in 2:d
        for g in TreeIt(n_vert) 
            ans_g = 0
            for p in partitions(d, nv(g))
                if n == 3 && (2 in p) continue end
                for mark_v in Base.Iterators.product(repeat([1:nv(g)], n_mark)...)
                    mark = Dict(1:n_mark .=> mark_v)
                    for degs in unique(permutations(p))
                        ans_g += Red_rec(n, g, degs, mark, ex)
                    end
                end
            end
            ans += div(ans_g, Graphs.Experimental.count_isomorph(g, g))
        end
    end

    return ans

end

function count_curves(n::Int64, deg::Int64)
    println("Number of reducibles contact curves of degree ", deg, " in P",n)
    max = (n-1)*deg + n-2
    number = n-1
    y = []

    for x in Base.Iterators.product(repeat([0:max], number)...)
        if sum(i -> (i+1)*x[i],1:number) != max + sum(x) continue end
        push!(y,x)
    end
    
    for x in reverse(sort(y))
        expon = vcat([[j+1 for _ in 1:x[j]] for j in 1:number]...)
        println(x, ": ", Count_reducible_contact(n, deg, expon))
    end
end

# This is an implementation of the algorithm to generate all trees on n vertices up to 
# isomorphism. The algorithm is described in the paper 
# CONSTANT TIME GENERATION OF FREE TREES*
# ROBERT ALAN WRIGHTS’, BRUCE RICHMONDT, ANDREW ODLYZKO AND BRENDAN D. MCKAY
#
# written by Csaba Schneider, contribution from Giosuè Muratore

struct TreeIt
    n_vert::Int64
end

function Base.eltype(::Type{TreeIt})
    SimpleGraph{Int64}
end

function Base.iterate( TI::TreeIt, ggd::Dict{Any,Any} = Dict() )::Union{Nothing, Tuple{SimpleGraph{Int64}, Dict{Any,Any}}}

    if isempty(ggd) #first iteration
        
        if TI.n_vert < 4
            #L = [ 1:2; 2:TI.n_vert-2+1 ];
            #return LevelSequenceToLightGraph( L ), Dict('q' => 0)
            return StarGraph(TI.n_vert), Dict('q' => 0)
        end

        n = TI.n_vert
        k = n÷2 + 1
        L = [ 1:k; 2:n-k+1 ];
        W = [ 0:k-1; 1:n-1]
        p, q, h1, h2, r =  n, n-1, k, n, k
        
        if isodd( n ) 
            c = Inf
        else 
            c = Float64(n+1)
        end 

        return LevelSequenceToLightGraph( L ), Dict( 'L' => L, 'W' => W, 'n' => n, 'p' => p, 'q' => q, "h1" => h1, "h2" => h2, 'c' => c, 'r' => r )
    end

    if ggd['q'] == 0 #last iteration
        return nothing
    end

    # next
    L = ggd['L']; W = ggd['W']; n = ggd['n']; p = ggd['p']; q = ggd['q'] 
    h1 = ggd["h1"]; h2 = ggd["h2"]; c = ggd['c']; r = ggd['r']

    l = L; w = W

    fixit = false

    if c == n+1 || p == h2 && (l[h1] == l[h2]+1 && n-h2>r-h1 ||
            l[h1] == l[h2] && n-h2+1 < r - h1)  
        if l[r] > 3 
            p = r;  q = w[r]
            if h1 == r 
                h1 = h1 - 1
            end 
            fixit = true
        else 
            p = r; r = r-1; q = 2
        end
    end
    
    needr = false; needc = false; needh2 = false
    if p <= h1 h1 = p - 1; end
    if p <= r 
        needr = true
    elseif p <= h2 
        needh2 = true 
    elseif l[h2] == l[h1] - 1 && n - h2 == r - h1 
        if p <= c needc = true end
    else 
        c = Inf
    end

    oldp = p; δ = q - p; oldlq = l[q]; oldwq = w[q]; p = Inf
    
    for i in oldp:n
        l[i] = l[i+δ]
        if l[i] == 2 
            w[i] = 1
        else
            p = i
            if l[i] == oldlq 
                q = oldwq
            else 
                q = w[i+δ] - δ
            end
            w[i] = q
        end
    
        if needr && l[i] == 2 
            needr = false; needh2 = true; r = i - 1
        end
        
        if needh2 && l[i] <= l[i-1] && i > r + 1 
            needh2 = false; h2 = i - 1
            if l[h2] == l[h1] - 1 && n - h2 == r - h1 
                needc = true
            else 
                c = Inf
            end
        end
        
        if needc 
            if l[i] != l[h1-h2+i] - 1
                needc = false; c = i
            else 
                c = i+1
            end
        end
    end

    if fixit 
        r = n-h1+1
        for i in (r+1):n 
            l[i] = i-r+1; w[i] = i-1
        end
        w[r+1] = 1; h2 = n; p = n; q = p-1; c = Inf
    else
        if p == Inf 
            if l[oldp-1] != 2 
                p = oldp - 1
            else 
                p = oldp - 2
            end
            q = w[p]
        end

        if needh2 
            h2 = n
            if l[h2] == l[h1] - 1 && h1 == r 
                c = n + 1
            else 
                c = Inf
            end
        end
    end

    return LevelSequenceToLightGraph( l ), Dict( 'L' => L, 'W' => W, 'n' => n, 'p' => p, 'q' => q, "h1" => h1, "h2" => h2, 'c' => c, 'r' => r )
end

function LevelSequenceToLightGraph( seq::Vector{Int64} )::SimpleGraph{Int64}

    edges = Dict{Int64,Int64}()
    # root = 1
    # current_level = 2
    current_root = 1
    for i in 2:length( seq )
        if seq[i] == seq[i-1]+1 
            push!( edges, i => current_root )
            current_root = i
        else 
            for i in 1:seq[i-1]-seq[i]+1
                current_root = edges[current_root]
            end 
            push!( edges, i => current_root )
            current_root = i
        end
    end

    return SimpleGraph( Edge.( [ (i,edges[i] ) for i in keys( edges )]))
end

welcolme = raw"""
This file is part of the paper "Irreducible Contact Curves via graph stratification" by Giosuè Muratore
The result of the paper are obtained using the number of contact curves given in the paper:
"Enumeration of Contact Curves via Torus Actions" (same author), and removing the number of 
reducible one using the following code:
include("Counting_Reducibles_Contact_Curves.jl")
count_curves(3,3)
count_curves(3,4)
count_curves(3,5)
count_curves(5,2)
"""

println(welcolme);