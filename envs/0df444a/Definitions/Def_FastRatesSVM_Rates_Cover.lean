-- Prove2me | Definitions.Def_FastRatesSVM_Rates_Cover
-- name    : FastRatesSVM_Rates_Cover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:44.702111+00:00
-- url     : https://prove2.me/theorems/6162048a-3a5a-4fde-b82e-c0d07c8f5958
-- title:
--   Empirical L2 covering numbers of Gaussian RKHS balls
-- statement:
--   The empirical $L_2$ seminorm of a function $f$ at inputs $x_1,\ldots,x_n$ is
--   $$
--   \|f\|_{L_2(T_X)}=
--   \left(\frac1n\sum_{i=1}^{n}|f(x_i)|^2\right)^{1/2}.
--   $$
--   The covering number of a function class is the least positive integer $m$ for which $m$ arbitrary function-valued centers cover the class in this seminorm at radius $\varepsilon$; it is infinite if no finite cover exists. The Gaussian RKHS unit ball consists of restrictions with squared norm at most one.
--
--   This is the entropy object of Theorem 2.1. **Formalization Note** Centers range over all functions, as centers in the ambient empirical $L_2$ space do. The number is extended-valued to represent the absence of a finite cover.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 5, covering number definition and (4)

import Definitions.Def_FastRatesSVM_Rates_RKHS

namespace FastRatesSVM.Rates

/-- The empirical L2 seminorm on input coordinates of a sample. -/
noncomputable def empiricalL2 {d n : ℕ} (xs : Fin n → E d)
    (f : E d → ℝ) : ℝ :=
  Real.sqrt ((∑ i, (f (xs i)) ^ 2) / (n : ℝ))

/-- Covering number with arbitrary function-valued centers, as in §2.2.
The infimum is `⊤` if no finite cover exists. -/
noncomputable def empiricalCoverNumber {d n : ℕ} (A : Set (E d → ℝ))
    (xs : Fin n → E d) (ε : ℝ) : ENNReal := by
  classical
  exact ⨅ (m : ℕ) (_hm : 0 < m) (centers : Fin m → E d → ℝ),
    if (∀ f ∈ A, ∃ j : Fin m, empiricalL2 xs (fun x => f x - centers j x) ≤ ε)
    then (m : ENNReal) else ⊤

noncomputable def gaussianUnitBall {d : ℕ} (S : Set (E d)) (σ : ℝ) :
    Set (E d → ℝ) :=
  {f | rkhsNormSq (gaussian σ) S f ≤ 1}

end FastRatesSVM.Rates


