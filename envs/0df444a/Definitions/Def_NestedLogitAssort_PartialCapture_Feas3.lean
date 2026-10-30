-- Prove2me | Definitions.Def_NestedLogitAssort_PartialCapture_Feas3
-- name    : NestedLogitAssort_PartialCapture_Feas3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:40:16.290157+00:00
-- url     : https://prove2.me/theorems/40e9794c-a8da-4fa9-8345-daa12beef5b4
-- title:
--   Feasibility in the linear program (3)
-- statement:
--   The assortment problem is equivalent to the linear program (3):
--
--   $$
--   \min\ x\quad\text{s.t.}\quad v_0x\ge\sum_{i\in M}y_i,\qquad y_i\ge V_i(S_i)^{\gamma_i}\bigl(R_i(S_i)-x\bigr)\quad\forall\,S_i\subseteq N,\ i\in M.
--   $$
--
--   A pair $(x,y)$ with $x\in\mathbb R$ and $y\in\mathbb R^M$ is feasible for (3) when it satisfies both sets of constraints, for every subset $S_i$ of $N$ (including $\emptyset$ and $N$).
--
--   **Formalization Note** Only feasibility is encoded; the objective is not needed.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (3), p. 11

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_T

namespace NestedLogitAssort.PartialCapture

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

end NestedLogitAssort.PartialCapture


