-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularDyadicEvaluator
-- name    : CK_GeneralCK_Certificates_E8TAxisRegularDyadicEvaluator
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:49:24.149338+00:00
-- url     : https://prove2.me/theorems/620f2506-e995-4206-81f3-ccf7ccf3a0f4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisRegularDyadicEvaluator` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisRegularDyadicEvaluator` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisRegularDyadicEvaluator` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisRegularDyadicEvaluator (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisRegularDyadicEvaluator.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularSourceBounds
import Definitions.Def_CK_GeneralCK_Certificates_DyadicFastLog

-- ===== source module GeneralCK.Certificates.E8TAxisRegularDyadicEvaluator =====
section

/-!
# Checked dyadic evaluation of the regular inverse source polynomial

All coefficients and errors are exact rationals from the proved source
enclosures. Dyadic operations round outward; the final inflation includes
both the order-17 analytic remainder and the coefficient uncertainty.
-/

namespace GeneralCK.Certificates.E8TAxisRegularDyadicEvaluator

open Set Metric GeneralCK DyadicInterval
open E8OriginRealTaylorTransfer E8OriginRemainder E8AnalyticCoefficientBoxes
open E8TAxisRegularSourceBounds E8TAxisRegularGermJet E8TauInverseContraction

def ratBox (p : ℕ) (q : ℚ) : DyadicInterval p :=
  DyadicFastLog.fraction p q.num q.den

theorem ratBox_sound (p : ℕ) (q : ℚ) : (ratBox p q).Contains (q : ℝ) := by
  simpa only [ratBox, Rat.cast_def, Int.cast_natCast] using
    DyadicFastLog.fraction_sound p q.num
      (show (0 : ℤ) < q.den by exact_mod_cast q.den_pos)

def rationalHull (p : ℕ) (lo hi : ℚ) : DyadicInterval p :=
  ⟨(ratBox p lo).lo, (ratBox p hi).hi⟩

theorem rationalHull_sound (p : ℕ) {lo hi : ℚ} {y : ℝ}
    (hy : y ∈ Icc (lo : ℝ) (hi : ℝ)) : (rationalHull p lo hi).Contains y := by
  have hl := (ratBox_sound p lo).1
  have hu := (ratBox_sound p hi).2
  exact ⟨hl.trans (mul_le_mul_of_nonneg_left hy.1 (scale_cast_pos p).le),
    (mul_le_mul_of_nonneg_left hy.2 (scale_cast_pos p).le).trans hu⟩

def powBox {p : ℕ} (box : DyadicInterval p) : ℕ → DyadicInterval p
  | 0 => ofInt p 1
  | n + 1 => (powBox box n).mul box

theorem powBox_sound {p : ℕ} {box : DyadicInterval p} {y : ℝ}
    (hy : box.Contains y) (n : ℕ) : (powBox box n).Contains (y ^ n) := by
  induction n with
  | zero => simpa [powBox] using ofInt_sound p 1
  | succ n ih => simpa [powBox, pow_succ] using mul_sound ih hy

def polynomialBox {p : ℕ} (coeff : ℕ → ℚ) (box : DyadicInterval p) :
    ℕ → DyadicInterval p
  | 0 => ofInt p 0
  | n + 1 => (polynomialBox coeff box n).add
      ((ratBox p (coeff n)).mul (powBox box n))

theorem polynomialBox_sound {p : ℕ} (coeff : ℕ → ℚ)
    {box : DyadicInterval p} {y : ℝ} (hy : box.Contains y) (n : ℕ) :
    (polynomialBox coeff box n).Contains
      (∑ k ∈ Finset.range n, (coeff k : ℝ) * y ^ k) := by
  induction n with
  | zero => simpa [polynomialBox] using ofInt_sound p 0
  | succ n ih =>
      simpa only [polynomialBox, Finset.sum_range_succ] using
        add_sound ih (mul_sound (ratBox_sound p (coeff n)) (powBox_sound hy n))

def sourceCoeff (j k : ℕ) : ℚ :=
  ((k + j).factorial : ℚ) / k.factorial * sourceCenter (k + j)

def errorCoeff (j k : ℕ) : ℚ :=
  ((k + j).factorial : ℚ) / k.factorial * sourceHalfWidth (k + j)

def sourceBox {p : ℕ} (j : ℕ) (box : DyadicInterval p) : DyadicInterval p :=
  polynomialBox (sourceCoeff j) box (16 - j)

def coefficientErrorBox {p : ℕ} (j : ℕ) (box : DyadicInterval p) : DyadicInterval p :=
  polynomialBox (errorCoeff j) box (16 - j)

def completeErrorBox {p : ℕ} (j : ℕ) (box : DyadicInterval p) : DyadicInterval p :=
  ((ratBox p (q17AbsBound / (17 - j).factorial)).mul (powBox box (17 - j))).add
    (coefficientErrorBox j box)

theorem sourceBox_sound {p : ℕ} (j : ℕ) {box : DyadicInterval p} {y : ℝ}
    (hy : box.Contains y) : (sourceBox j box).Contains (qSourceTaylorDerivative j y) := by
  simpa only [sourceBox, sourceCoeff, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
    qSourceTaylorDerivative] using polynomialBox_sound (sourceCoeff j) hy (16 - j)

theorem coefficientErrorBox_sound {p : ℕ} (j : ℕ) {box : DyadicInterval p} {y : ℝ}
    (hy : box.Contains y) :
    (coefficientErrorBox j box).Contains (qSourceDerivativeError j y) := by
  simpa only [coefficientErrorBox, errorCoeff, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
    qSourceDerivativeError] using polynomialBox_sound (errorCoeff j) hy (16 - j)

theorem completeErrorBox_sound {p : ℕ} (j : ℕ) {box : DyadicInterval p} {y : ℝ}
    (hy : box.Contains y) :
    (completeErrorBox j box).Contains
      ((q17AbsBound : ℝ) * y ^ (17 - j) / (17 - j).factorial +
        qSourceDerivativeError j y) := by
  have h := add_sound
    (mul_sound (ratBox_sound p (q17AbsBound / (17 - j).factorial))
      (powBox_sound hy (17 - j))) (coefficientErrorBox_sound j hy)
  simpa only [completeErrorBox, Rat.cast_div, Rat.cast_natCast,
    div_mul_eq_mul_div] using h

def inflate {p : ℕ} (center error : DyadicInterval p) : DyadicInterval p :=
  ⟨center.lo - error.hi, center.hi + error.hi⟩

theorem inflate_sound {p : ℕ} {center error : DyadicInterval p} {c e y : ℝ}
    (hc : center.Contains c) (he : error.Contains e) (hy : ‖y - c‖ ≤ e) :
    (inflate center error).Contains y := by
  rw [Real.norm_eq_abs, abs_le] at hy
  have hlo := mul_le_mul_of_nonneg_left hy.1 (scale_cast_pos p).le
  have hhi := mul_le_mul_of_nonneg_left hy.2 (scale_cast_pos p).le
  dsimp only [inflate, Contains]
  push_cast
  constructor <;> nlinarith [hc.1, hc.2, he.2]

def regularComponentBox {p : ℕ} (j : ℕ) (box : DyadicInterval p) : DyadicInterval p :=
  inflate (sourceBox j box) (completeErrorBox j box)

/-- Soundness of the executable dyadic evaluator for an actual regular jet
component, including at zero. -/
theorem regularComponentBox_sound
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder
      (closedBall 0 tauRadius))
    {p : ℕ} (j : ℕ) (hj : j ≤ 5) {box : DyadicInterval p} {y : ℝ}
    (hyBox : box.Contains y) (hy0 : 0 ≤ y) (hyUpper : y ≤ 4 / 25) :
    (regularComponentBox j box).Contains (component regularQJet j y) :=
  inflate_sound (sourceBox_sound j hyBox) (completeErrorBox_sound j hyBox)
    (regular_component_source_polynomial_le hLip j hj hy0 hyUpper)

def regularJetBox {p : ℕ} (box : DyadicInterval p) : DyadicJet5Enclosure p :=
  ⟨regularComponentBox 0 box, regularComponentBox 1 box,
   regularComponentBox 2 box, regularComponentBox 3 box,
   regularComponentBox 4 box, regularComponentBox 5 box⟩

/-- All six fields are evaluated from the source polynomial and the complete
analytic error expression; no derivative field is left as a premise. -/
theorem regularJetBox_sound
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder
      (closedBall 0 tauRadius))
    {p : ℕ} {box : DyadicInterval p} {y : ℝ}
    (hyBox : box.Contains y) (hy0 : 0 ≤ y) (hyUpper : y ≤ 4 / 25) :
    (regularJetBox box).Contains regularQJet y := by
  exact ⟨regularComponentBox_sound hLip 0 (by norm_num) hyBox hy0 hyUpper,
    regularComponentBox_sound hLip 1 (by norm_num) hyBox hy0 hyUpper,
    regularComponentBox_sound hLip 2 (by norm_num) hyBox hy0 hyUpper,
    regularComponentBox_sound hLip 3 (by norm_num) hyBox hy0 hyUpper,
    regularComponentBox_sound hLip 4 (by norm_num) hyBox hy0 hyUpper,
    regularComponentBox_sound hLip 5 (by norm_num) hyBox hy0 hyUpper⟩

end GeneralCK.Certificates.E8TAxisRegularDyadicEvaluator

#print axioms GeneralCK.Certificates.E8TAxisRegularDyadicEvaluator.sourceBox_sound
#print axioms GeneralCK.Certificates.E8TAxisRegularDyadicEvaluator.completeErrorBox_sound
#print axioms GeneralCK.Certificates.E8TAxisRegularDyadicEvaluator.regularComponentBox_sound
#print axioms GeneralCK.Certificates.E8TAxisRegularDyadicEvaluator.regularJetBox_sound

end


