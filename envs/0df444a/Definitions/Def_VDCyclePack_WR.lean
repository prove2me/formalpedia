-- Prove2me | Definitions.Def_VDCyclePack_WR
-- name    : VDCyclePack_WR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:14.304648+00:00
-- url     : https://prove2.me/theorems/d61d0d13-c9ab-4530-a23d-b254a6d648e7
-- title:
--   $W_R$: total weight of intersecting pairs
-- statement:
--   For a family $R$ of cycles with weights $x$,
--   $$
--   W_R=\sum_{\{C,C'\}\subseteq R,\ C\ne C',\ V(C)\cap V(C')\neq\emptyset} x_C\,x_{C'},
--   $$
--   each unordered pair of distinct intersecting cycles counted once.
--
--   It enters the weighted-average bound (2) and is bounded by Lemma 5.1.
--
--   **Formalization Note** Computed as one half of the sum over ordered pairs of distinct members.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 5.1, p.15

import Mathlib

namespace VDCyclePack

open Classical in
/-- **W_R: the total weight of intersecting pairs.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 5.1, p.15: "W_R = Σ_{{C,C′}⊆R, C≠C′, V(C)∩V(C′)≠∅} x_C x_{C′}. Each unordered pair of
distinct intersecting cycles contributes once to W_R."

`WR R x` is half the sum of `x C · x C′` over ordered pairs `(C, C′)` of distinct members of `R`
sharing a vertex.

**Formalization Note.** Each unordered pair appears twice among the ordered pairs (`offDiag`), so
the factor `1/2` makes it count once, as in the paper. -/
noncomputable def WR {V : Type*} {G : SimpleGraph V} (R : Finset G.Subgraph) (x : G.Subgraph → ℝ) :
    ℝ :=
  (1 / 2 : ℝ) * ∑ p ∈ R.offDiag.filter (fun p => (p.1.verts ∩ p.2.verts).Nonempty),
    x p.1 * x p.2

end VDCyclePack


