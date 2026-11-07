-- Prove2me | Definitions.Def_VDCyclePack_WeightedFamily
-- name    : VDCyclePack_WeightedFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:48.324441+00:00
-- url     : https://prove2.me/theorems/2622e66e-5f35-40f7-b09a-3ef5a126a0fb
-- title:
--   A family of cycles with positive weights and loads at most one
-- statement:
--   A finite family $S$ of subgraphs with weights $x$ is a **weighted family** if every $C\in S$ is a cycle with $x_C>0$ and
--   $$
--   \sum_{C\in S,\ v\in V(C)} x_C\le 1\qquad\text{for every vertex } v .
--   $$
--   This is the input of Theorem 4.2.
--
--   **Formalization Note** Weights are real numbers; the paper's rational weights are a special case. Only the values of $x$ on $S$ are read.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 4.2, p.12

import Mathlib
import Definitions.Def_VDCyclePack_IsCycleSub

namespace VDCyclePack

open Classical in
/-- **A family of cycles with positive weights and loads at most one.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Theorem 4.2, p.12: "Let S be an explicitly given family of cycles in G with positive
rational weights (x_C)_{C∈S} such that Σ_{C∈S, v∈V(C)} x_C ≤ 1 for every v ∈ V(G)".

`WeightedFamily S x` says every member of `S` is a cycle with `x C > 0`, and for every vertex `v`
the weights of the members through `v` sum to at most one.

**Formalization Note.** Weights are real numbers here; the rational weights of the paper are a
special case. Only the values of `x` on `S` are read. -/
def WeightedFamily {V : Type*} {G : SimpleGraph V} (S : Finset G.Subgraph) (x : G.Subgraph → ℝ) :
    Prop :=
  (∀ C ∈ S, IsCycleSub C ∧ 0 < x C) ∧ ∀ v : V, ∑ C ∈ S.filter (fun C => v ∈ C.verts), x C ≤ 1

end VDCyclePack


