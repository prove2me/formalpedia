-- Prove2me | Definitions.Def_NestedLogitAssort_DeltaGrid_Feas3
-- name    : NestedLogitAssort_DeltaGrid_Feas3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:03:40.772234+00:00
-- url     : https://prove2.me/theorems/a2dc43eb-eafe-4c7b-9287-633d1bb3508a
-- title:
--   Feasibility in the linear program (3)
-- statement:
--   The linear program (3) is
--
--   $$
--   \min\ x\quad\text{s.t.}\quad v_0\,x\ge\sum_{i\in M}y_i,\qquad y_i\ge V_i(S_i)^{\gamma_i}\bigl(R_i(S_i)-x\bigr)\ \ \text{for all } S_i\subseteq N,\ i\in M .
--   $$
--
--   A pair $(x,y)$ with $y=(y_i)_{i\in M}$ is feasible for (3) when it satisfies both sets of constraints; the assortments $S_i$ range over all subsets of $N$, including $\emptyset$ and $N$. The optimal value of (3) is the optimal expected revenue of the assortment problem (2).
--
--   **Formalization Note** Only feasibility is encoded; the objective is not needed here.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (3), p. 11

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_T

namespace NestedLogitAssort.DeltaGrid

/-- **Feasibility in the linear program (3).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (3), p. 11:
`min x` s.t. `v_0 x ≥ ∑_{i ∈ M} y_i`, `y_i ≥ V_i(S_i)^{γ_i}(R_i(S_i) − x)` for all `S_i ⊂ N`, `i ∈ M`.

`Feas3 I x y` says that `(x, y)` satisfies both sets of constraints; `S_i` ranges over all subsets
of `N`, including `∅` and `N`.

**Formalization Note.** Only feasibility is encoded; the objective `min x` is not needed by the
theorems of this mission. -/
def Feas3 {M : Type*} [Fintype M] {n : ℕ} (I : Instance M n) (x : ℝ) (y : M → ℝ) : Prop :=
  ∑ i, y i ≤ I.v0 * x ∧ ∀ (i : M) (S : Finset (Fin n)), T I i S x ≤ y i

end NestedLogitAssort.DeltaGrid


