-- Prove2me | Definitions.Def_Zeta5_SourceValue
-- name    : Zeta5_SourceValue
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-01T10:32:44.598563+00:00
-- url     : https://prove2.me/theorems/4ec235b3-ce80-44d9-8501-e32b08c8c7f3
-- title:
--   Zeta5: real series and the complex Riemann zeta value
-- statement:
--   Define the real number
--   $$z_5=\sum_{n=0}^{\infty}\frac1{n^5}.$$
--   The term at $n=0$ is zero under the total division convention. The module includes the source's short identification
--   $$\operatorname{riemannZeta}(5)=(z_5:\mathbb C).$$
--   This connects the real-valued polynomial construction to the existing platform goal stated using Mathlib's complex Riemann zeta function. The identification follows from Mathlib's series formula at integer arguments greater than one.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Zeta5.lean#L1-L20

import Mathlib

/-!
# `ζ(5)` as a real number
-/

namespace Apery

/-- `ζ(5)` as a real number. -/
noncomputable def zeta5 : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ 5

/-- Mathlib's `riemannZeta 5` is the real number `zeta5`. -/
theorem riemannZeta_five : riemannZeta 5 = (zeta5 : ℂ) := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := 5) (by norm_num)
  rw [Nat.cast_ofNat] at h
  rw [h, zeta5, Complex.ofReal_tsum]
  push_cast
  rfl

end Apery


