-- Prove2me | Definitions.Def_LG2021_GaussianEstimators
-- name    : LG2021_GaussianEstimators
-- status  : Definition
-- author  : @sim2000dg
-- created : 2026-11-14T15:07:32.461109+00:00
-- url     : https://prove2.me/theorems/58f6df5c-4d0d-4461-9175-47105b869696
-- title:
--   Gaussian estimators and explicit confidence parameters
-- statement:
--   Concrete Gaussian likelihood-ratio estimators and confidence base A=10^6(d+1)(D+1)(n+1), L=32 log A. These are definitions; their mathematical properties are proved separately.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th Conference on Learning Theory (COLT 2021), Proceedings of Machine Learning Research 134:2938–2964, 2021, Lemma 5 and Appendix E. Separation argument adapted for formalization.

import Definitions.Def_LG2021_GaussianSeparation

/-!
Concrete likelihood-ratio estimators from Lattimore–György (COLT 2021), Section 4.
Its radial condition is also used to guard feasible loss queries.
-/

noncomputable section

namespace LG2021.Concentration

/-- Density ratio of the contracted, translated standard Gaussian to the standard Gaussian. -/
def likelihoodRatio {d : ℕ} (lambda : ℝ) (z x : Space d) : ℝ :=
  Real.exp (‖x‖ ^ 2 / 2 - ‖x - lambda • z‖ ^ 2 / (2 * (1 - lambda) ^ 2)) /
    (1 - lambda) ^ d

/-- The common truncation in the scalar and gradient estimators. -/
def truncation {d : ℕ} (lambda r : ℝ) (z x : Space d) : ℝ :=
  if likelihoodRatio lambda z x ≤ Real.exp 1 / (1 - lambda) ^ d ∧
    ‖x‖ ≤ r / (d : ℝ) then 1 else 0

/-- Multiplier of a noisy loss observation in the scalar surrogate estimator. -/
def scalarCoefficient {d : ℕ} (lambda r : ℝ) (z x : Space d) : ℝ :=
  (1 - 1 / lambda + likelihoodRatio lambda z x / lambda) * truncation lambda r z x

/-- Vector multiplier of a noisy observation in the surrogate-gradient estimator. -/
def gradientCoefficient {d : ℕ} (lambda r : ℝ) (z x : Space d) : Space d :=
  (likelihoodRatio lambda z x * truncation lambda r z x / (1 - lambda) ^ 2) •
    (x - lambda • z)

/-- The gradient multiplier tested against a fixed direction. -/
def directionalGradientCoefficient {d : ℕ} (lambda r : ℝ)
    (z η x : Space d) : ℝ :=
  inner ℝ (gradientCoefficient lambda r z x) η

/-- An explicit confidence base for the fixed-dimensional corollary. -/
def parameterBase (d : ℕ) (D : ℝ) (n : ℕ) : ℝ :=
  10 ^ 6 * ((d : ℝ) + 1) * (D + 1) * ((n : ℝ) + 1)

/-- An explicit logarithmic confidence parameter, avoiding an implicit root selection. -/
def parameterLog (d : ℕ) (D : ℝ) (n : ℕ) : ℝ :=
  32 * Real.log (parameterBase d D n)

end LG2021.Concentration


