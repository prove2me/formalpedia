-- Prove2me | Definitions.Def_NestedLogitAssort_PartialCapture_Khat
-- name    : NestedLogitAssort_PartialCapture_Khat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:45:27.911117+00:00
-- url     : https://prove2.me/theorems/fb0b241c-bf4b-4346-ab65-6635bcf32252
-- title:
--   Continuous knapsack value $\hat K_i(\epsilon_i)$
-- statement:
--   For a nest $i$ and a capacity $\epsilon$,
--
--   $$
--   \hat K_i(\epsilon)=\max\Bigl\{\sum_{j\in N}r_{ij}v_{ij}z_{j}\ :\ \sum_{j\in N}v_{ij}z_{j}\le\epsilon,\ 0\le z_{j}\le\mathbf 1(v_{ij}\le\epsilon)\ \forall j\in N\Bigr\},
--   $$
--
--   the value of the continuous relaxation (11) of the knapsack problem (9).
--
--   **Formalization Note** The maximum is a supremum; for $\epsilon\ge 0$ the feasible set is a nonempty compact polytope, so the supremum is attained. Capacities $\epsilon<0$ are never used.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (11), p. 23

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_Feas11

namespace NestedLogitAssort.PartialCapture

/-- **The continuous knapsack value `K̂_i(ϵ_i)`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (11), p. 23:
`K̂_i(ϵ_i) = max { ∑_{j ∈ N} r_{ij} v_{ij} z_{ij} : ∑_{j ∈ N} v_{ij} z_{ij} ≤ ϵ_i,
0 ≤ z_{ij} ≤ 1(v_{ij} ≤ ϵ_i) ∀ j ∈ N }`.

**Formalization Note.** For `ϵ ≥ 0` the feasible set is a nonempty (it contains `z = 0`) compact
polytope, so the set of values is nonempty and bounded and `sSup` is the maximum. For `ϵ < 0`
(never used) the value is a junk value. -/
noncomputable def Khat {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (ε : ℝ) : ℝ :=
  sSup {s : ℝ | ∃ z : Fin n → ℝ, Feas11 I i ε z ∧ s = ∑ j, I.r i j * I.v i j * z j}

end NestedLogitAssort.PartialCapture


