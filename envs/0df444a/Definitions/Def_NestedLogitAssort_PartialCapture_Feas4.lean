-- Prove2me | Definitions.Def_NestedLogitAssort_PartialCapture_Feas4
-- name    : NestedLogitAssort_PartialCapture_Feas4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:41:08.015518+00:00
-- url     : https://prove2.me/theorems/2e0e9d01-58e7-4568-9fdc-6c315a4cc74c
-- title:
--   Feasibility in the restricted linear program (4)
-- statement:
--   Given, for every nest $i$, a collection $\mathcal C_i$ of candidate assortments $\{A_{it}:t\in\mathcal T_i\}$, problem (4) is
--
--   $$
--   \min\ x\quad\text{s.t.}\quad v_0x\ge\sum_{i\in M}y_i,\qquad y_i\ge V_i(S_i)^{\gamma_i}\bigl(R_i(S_i)-x\bigr)\quad\forall\,S_i\in\mathcal C_i,\ i\in M.
--   $$
--
--   A pair $(x,y)$ is feasible for (4) when it satisfies both sets of constraints. Problem (4) keeps only some of the constraints of (3).
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (4), p. 12

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_T

namespace NestedLogitAssort.PartialCapture

/-- **Feasibility in the restricted linear program (4).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (4), p. 12:
`min x` s.t. `v_0 x ≥ ∑_{i ∈ M} y_i`, `y_i ≥ V_i(S_i)^{γ_i}(R_i(S_i) − x)` for all
`S_i ∈ {A_{it} : t ∈ T_i}`, `i ∈ M`.

The collection of candidate assortments `{A_{it} : t ∈ T_i}` of nest `i` is `C i`. -/
def Feas4 {M : Type*} [Fintype M] {n : ℕ} (I : Instance M n) (C : M → Set (Finset (Fin n)))
    (x : ℝ) (y : M → ℝ) : Prop :=
  ∑ i, y i ≤ I.v0 * x ∧ ∀ i, ∀ S ∈ C i, T I i S x ≤ y i

end NestedLogitAssort.PartialCapture


