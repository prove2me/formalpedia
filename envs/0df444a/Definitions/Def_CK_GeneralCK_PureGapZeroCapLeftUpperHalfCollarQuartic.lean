-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarQuartic
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarQuartic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:50:45.684993+00:00
-- url     : https://prove2.me/theorems/2982a6c3-fb90-47d4-8a22-914c54121664
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarQuartic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarQuartic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarQuartic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperHalfCollarQuartic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperHalfCollarQuartic.lean)

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperRadialReduction

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperHalfCollarQuartic =====
section

/-!
The proposed half-collar quartic coefficient for the exact left-upper cap
value. The polynomial bound below is elementary. The actual analytic
order-six remainder is an explicit premise of the conditional adapter;
it is not supplied or inferred by this file.
-/

namespace GeneralCK

def leftUpperQuarticNumerator (L lambda : ℝ) : ℝ :=
  (10 * L - 3) * lambda ^ 4 +
    (18 - 20 * L) * lambda ^ 2 + (3 - 2 * L)

noncomputable def leftUpperQuarticCoefficient (L lambda : ℝ) : ℝ :=
  leftUpperQuarticNumerator L lambda / (3 * L ^ 2)

theorem leftUpperQuarticCoefficient_lower {L lambda : ℝ}
    (hLlo : (3 / 5 : ℝ) ≤ L) (hLhi : L ≤ 4 / 5) :
    (35 / 48 : ℝ) ≤ leftUpperQuarticCoefficient L lambda := by
  have hLpos : 0 < L := by linarith
  have hfour : 0 ≤ 10 * L - 3 := by linarith
  have htwo : 0 ≤ 18 - 20 * L := by linarith
  have hconst : (7 / 5 : ℝ) ≤ 3 - 2 * L := by linarith
  have hprodFour : 0 ≤ (10 * L - 3) * lambda ^ 4 :=
    mul_nonneg hfour (by positivity)
  have hprodTwo : 0 ≤ (18 - 20 * L) * lambda ^ 2 :=
    mul_nonneg htwo (sq_nonneg lambda)
  have hnum : (7 / 5 : ℝ) ≤ leftUpperQuarticNumerator L lambda := by
    dsimp [leftUpperQuarticNumerator]
    linarith
  have hLsq : L ^ 2 ≤ (4 / 5 : ℝ) ^ 2 := by
    have hprod : 0 ≤ (4 / 5 - L) * (4 / 5 + L) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have htarget : (35 / 48 : ℝ) * (3 * L ^ 2) ≤ 7 / 5 := by
    nlinarith [hLsq]
  have hden : 0 < 3 * L ^ 2 := by positivity
  unfold leftUpperQuarticCoefficient
  exact (le_div_iff₀ hden).2 (htarget.trans hnum)

theorem leftUpperQuarticCoefficient_actual_lower (lambda : ℝ) :
    (35 / 48 : ℝ) ≤ leftUpperQuarticCoefficient (Real.log 2) lambda :=
  leftUpperQuarticCoefficient_lower
    (by linarith [Real.log_two_gt_d9])
    (by linarith [Real.log_two_lt_d9])

/-- Conditional half-collar transfer. The premise `hrem` is the missing
uniform lower order-six remainder bound for the *actual* canonical gap. -/
theorem leftUpper_halfCollar_nonneg_of_remainder
    {z delta lambda C : ℝ}
    (hz : 0 < z) (hzdelta : z ≤ delta)
    (hC : 0 ≤ C) (hCdelta : C * delta ^ 2 ≤ 35 / 48)
    (hrem : z ^ 4 * leftUpperQuarticCoefficient (Real.log 2) lambda -
      C * z ^ 6 ≤
      canonicalPureGap (1 / 2 - z) (1 / 2)
        (H (1 / 2 - z)) (H (1 / 2 - lambda * z))) :
    0 ≤ canonicalPureGap (1 / 2 - z) (1 / 2)
      (H (1 / 2 - z)) (H (1 / 2 - lambda * z)) := by
  have hdelta : 0 ≤ delta := by linarith
  have hzsquared : z ^ 2 ≤ delta ^ 2 := by
    have hprod : 0 ≤ (delta - z) * (delta + z) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hCz : C * z ^ 2 ≤ 35 / 48 :=
    (mul_le_mul_of_nonneg_left hzsquared hC).trans hCdelta
  have hP : (35 / 48 : ℝ) ≤
      leftUpperQuarticCoefficient (Real.log 2) lambda :=
    leftUpperQuarticCoefficient_actual_lower lambda
  have hcoef : 0 ≤ leftUpperQuarticCoefficient (Real.log 2) lambda - C * z ^ 2 := by
    linarith
  calc
    0 ≤ z ^ 4 *
        (leftUpperQuarticCoefficient (Real.log 2) lambda - C * z ^ 2) :=
      mul_nonneg (pow_nonneg hz.le _) hcoef
    _ = z ^ 4 * leftUpperQuarticCoefficient (Real.log 2) lambda - C * z ^ 6 := by
      ring
    _ ≤ canonicalPureGap (1 / 2 - z) (1 / 2)
          (H (1 / 2 - z)) (H (1 / 2 - lambda * z)) := hrem

#print axioms leftUpperQuarticCoefficient_lower
#print axioms leftUpperQuarticCoefficient_actual_lower
#print axioms leftUpper_halfCollar_nonneg_of_remainder

end GeneralCK

end


