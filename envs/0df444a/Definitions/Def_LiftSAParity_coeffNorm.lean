-- Prove2me | Definitions.Def_LiftSAParity_coeffNorm
-- name    : LiftSAParity_coeffNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:32.219198+00:00
-- url     : https://prove2.me/theorems/5ebbc63d-d629-4711-bdc4-8eb1da0bf410
-- title:
--   Coefficient size of a polynomial
-- statement:
--   The **coefficient size** of a real polynomial $p$ is the sum of the magnitudes of its coefficients,
--   $$\|p\|=\sum_{m}|\mathrm{coeff}_m(p)| .$$
--   The coefficient size of a refutation is the sum of these quantities over all of its multipliers $q_p$ and its nonnegative part $h_\alpha$; this is the size measure of unary Sherali–Adams (uSA(⊕)).
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §3, p.9

import Mathlib

namespace LiftSAParity

/-- The **coefficient size** of one polynomial (de Rezende–Engström–Shekhovtsov, *Lifting
Sherali-Adams Degree to Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…),
§3, p.9): the sum of the magnitudes of the coefficients of its monomials, `∑_m |coeff_m(p)|`. -/
noncomputable def coeffNorm {σ : Type*} (p : MvPolynomial σ ℝ) : ℝ :=
  ∑ m ∈ p.support, |p.coeff m|

end LiftSAParity


