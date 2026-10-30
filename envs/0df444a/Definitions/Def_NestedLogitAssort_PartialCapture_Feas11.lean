-- Prove2me | Definitions.Def_NestedLogitAssort_PartialCapture_Feas11
-- name    : NestedLogitAssort_PartialCapture_Feas11
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:42:41.951926+00:00
-- url     : https://prove2.me/theorems/e4c5b779-db40-4ba4-9b1e-71c6ac8fba2e
-- title:
--   Feasibility in the continuous knapsack (11)
-- statement:
--   For a nest $i$ and a capacity $\epsilon$, the continuous knapsack problem (11) is
--
--   $$
--   \hat K_i(\epsilon)=\max\Bigl\{\sum_{j\in N}r_{ij}v_{ij}z_{j}\ :\ \sum_{j\in N}v_{ij}z_{j}\le\epsilon,\ 0\le z_{j}\le\mathbf 1(v_{ij}\le\epsilon)\ \forall j\in N\Bigr\}.
--   $$
--
--   A vector $z\in\mathbb R^N$ is feasible for (11) when it satisfies the capacity constraint and the bounds; a product whose weight exceeds $\epsilon$ must get $z_j=0$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (11), p. 23

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_Instance

namespace NestedLogitAssort.PartialCapture

/-- **Feasibility in the continuous knapsack problem (11).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (11), p. 23:
`K̂_i(ϵ_i) = max { ∑_{j ∈ N} r_{ij} v_{ij} z_{ij} : ∑_{j ∈ N} v_{ij} z_{ij} ≤ ϵ_i,
0 ≤ z_{ij} ≤ 1(v_{ij} ≤ ϵ_i) ∀ j ∈ N }`.

`Feas11 I i ε z` says that `z` satisfies the constraints of (11) in nest `i` with capacity `ε`. -/
def Feas11 {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (ε : ℝ) (z : Fin n → ℝ) : Prop :=
  ∑ j, I.v i j * z j ≤ ε ∧ ∀ j, 0 ≤ z j ∧ z j ≤ (if I.v i j ≤ ε then 1 else 0)

end NestedLogitAssort.PartialCapture


