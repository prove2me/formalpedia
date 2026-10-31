-- Prove2me | Definitions.Def_RecursiveStopping_Finite_InA
-- name    : RecursiveStopping_Finite_InA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:42:09.91304+00:00
-- url     : https://prove2.me/theorems/d860453a-ec16-4ea6-bf8b-76cf1d14461d
-- title:
--   The finite-horizon space $\mathcal A_d$
-- statement:
--   A function $f:\mathbb R\times\mathbb R^{m}\to\mathbb R$ belongs to the finite-horizon $\mathcal A_d$ when it is continuous on $[0,T]\times\mathbb R^{d-1}$, non-negative there, and $\|f\|_{\mathcal A_d}<\infty$ (finite-horizon weighted norm). Values outside $[0,T]\times\mathbb R^{d-1}$ are irrelevant.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, §2.2, p.10

import Mathlib
import Definitions.Def_RecursiveStopping_Finite_wnorm

open scoped NNReal ENNReal

namespace RecursiveStopping.Finite

/-- The finite-horizon space `A_d` of Colaneri & De Angelis, arXiv:1905.02650v4, p.10:
"Functions `f ∈ A_d` are continuous from `[0, T] × ℝ^{d−1}` to `ℝ_+`" with finite norm
`∥f∥_{A_d}` (`wnorm`). `InA T f` holds when `f` is continuous on `[0, T] × ℝ^m`, non-negative
there, and `wnorm T f < ∞`. -/
def InA {m : ℕ} (T : ℝ) (f : ℝ × EuclideanSpace ℝ (Fin m) → ℝ) : Prop :=
  ContinuousOn f (Dom m T) ∧ (∀ z ∈ Dom m T, 0 ≤ f z) ∧ wnorm T f < ⊤

end RecursiveStopping.Finite


