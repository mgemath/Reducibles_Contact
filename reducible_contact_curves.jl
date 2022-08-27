using Combinatorics
using Graphs

import Graphs.Experimental

include("my_trees_it.jl")

function get_Smooth(n::Int64, deg::Int64, ex::Dict)

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

function Red_rec(n::Int64, g::Graph, degs::Vector{Int64}, mark::Dict, ex::Dict)

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
        end
    
        return ans
    
end

function Count_reducible_contact(n::Int64, d::Int64, ex_v::Vector{Int64})
    
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

function m_Count_reducible_contact(n::Int64, d::Int64, ex_v::Vector{Int64})
    
    n_mark = length(ex_v)
    ex = Dict(1:n_mark .=> ex_v)
    
    local ans::Vector{Int64} = [0 for _ in 1:Threads.nthreads()]
    # local ans_g=0#::Vector{Int64} = [0 for _ in 1:Threads.nthreads()]

    for n_vert in 2:d
        for g in TreeIt(n_vert) 
            for p in partitions(d, nv(g))
                if n == 3 && (2 in p) continue end
                for degs in unique(permutations(p))
                    local vec_rel(u,v) = (degs[u] == degs[v])
                    Threads.@threads for mark_v in collect(Base.Iterators.product(repeat([1:nv(g)], n_mark)...))
                        local ans_g = 0
                        local mark = Dict(1:n_mark .=> mark_v)
                        ans_g += Red_rec(n, g, degs, mark, ex)
                        
                        ans_g[Threads.threadid()] = div(ans_g[Threads.threadid()], Graphs.Experimental.count_isomorph(g, g, vertex_relation = vec_rel)) #
                        ans[Threads.threadid()] += ans_g[Threads.threadid()]
                end
                end
            end 
        end
    end

    return sum(ans)
    
end