-- Prove2me | Definitions.Def_NestedLogitAssort_General_IsOpt4
-- name    : NestedLogitAssort_General_IsOpt4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:42:44.954792+00:00
-- url     : https://prove2.me/theorems/69d0f683-d036-4fdd-a063-dcfcfea813b0
-- title:
--   Optimal solution of problem (4)
-- statement:
--   A pair $(x,y)$ is an optimal solution of the minimization problem (4) with candidate collections $(\mathcal C_i)_{i\in M}$ when it is feasible for (4) and every feasible pair $(x',y')$ has $x\le x'$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (4), p. 12

import Mathlib
import Definitions.Def_NestedLogitAssort_General_Feas4

namespace NestedLogitAssort.General

/-- **Optimal solution to problem (4).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (4), p. 12: `(x, y)` is an optimal solution of the minimization problem (4) with
candidate collections `C` when it is feasible and no feasible point has a smaller `x`. -/
def IsOpt4 {M : Type*} [Fintype M] {n : ℕ} (I : Instance M n) (C : M → Set (Finset (Fin n)))
    (x : ℝ) (y : M → ℝ) : Prop :=
  Feas4 I C x y ∧ ∀ (x' : ℝ) (y' : M → ℝ), Feas4 I C x' y' → x ≤ x'

end NestedLogitAssort.General


