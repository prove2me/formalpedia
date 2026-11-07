-- Prove2me | Definitions.Def_VDCyclePack_IsMCycle
-- name    : VDCyclePack_IsMCycle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:32.183247+00:00
-- url     : https://prove2.me/theorems/0a1703d0-58f4-45df-9034-e374aa8fc3f5
-- title:
--   Cycle of an auxiliary multigraph
-- statement:
--   A **cycle** of a multigraph is given by distinct vertices $v_0,\dots,v_{k-1}$ ($k\ge1$) and distinct edges $e_0,\dots,e_{k-1}$ with $e_i$ joining $v_i$ and $v_{i+1 \bmod k}$. For $k=1$ it is a loop (a cycle of length one), for $k=2$ two parallel edges (length two), and for $k\ge3$ an ordinary cycle. Its vertex set is $\{v_0,\dots,v_{k-1}\}$.
--
--   **Formalization Note** A vertex list and an edge list; vertex-disjointness of cycles is disjointness of their vertex lists.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 3, p.10

import Mathlib

namespace VDCyclePack

/-- **Cycle of an auxiliary multigraph.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 3, p.10: "Auxiliary multigraphs may have loops and parallel edges. A loop
forms a cycle of length one ...; two parallel edges form a cycle of length two."

`IsMCycle ends vs es` says the vertex list `vs = [v₀, …, v_{k−1}]` (`k ≥ 1`) has no repetition, the
edge list `es = [e₀, …, e_{k−1}]` has the same length and no repetition, and `eᵢ` joins `vᵢ` and
`v_{i+1 mod k}`. For `k = 1` this is a loop, for `k = 2` two parallel edges, for `k ≥ 3` an ordinary
cycle. The vertex set of the cycle is the set of entries of `vs`.

**Formalization Note.** A cycle is given by a cyclic vertex sequence and its edges, as in the
paper; vertex-disjointness of cycles is disjointness of their vertex lists. -/
def IsMCycle {W E : Type*} (ends : E → Sym2 W) (vs : List W) (es : List E) : Prop :=
  1 ≤ vs.length ∧ es.length = vs.length ∧ vs.Nodup ∧ es.Nodup ∧
    ∀ (i : ℕ) (hi : i < vs.length) (he : i < es.length),
      ends es[i] = s(vs[i], vs[(i + 1) % vs.length]'(Nat.mod_lt _ (by omega)))

end VDCyclePack


