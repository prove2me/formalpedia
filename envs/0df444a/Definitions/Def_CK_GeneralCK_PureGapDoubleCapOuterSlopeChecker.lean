-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapOuterSlopeChecker
-- name    : CK_GeneralCK_PureGapDoubleCapOuterSlopeChecker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:36:40.075882+00:00
-- url     : https://prove2.me/theorems/314c5aa4-4d68-4893-91ed-bc128ab7f167
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapOuterSlopeChecker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapOuterSlopeChecker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapOuterSlopeChecker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapOuterSlopeChecker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapOuterSlopeChecker.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapSlopeCertificate
import Definitions.Def_CK_GeneralCK_ReflectionRegularDifference_v2
import Definitions.Def_CK_GeneralCK_CorrectionHessianNatural

-- ===== source module GeneralCK.PureGapDoubleCapOuterSlopeChecker =====
section

/-!
# A cancellation-free outer slope expression for the canonical double cap

The sufficient slope inequality has a near cancellation between the radial
value and its first derivative.  In natural bias coordinates, that difference
is a single positive rational term.  The remaining inverse-entropy term can
be enclosed by the existing bias-entropy and logarithm checker.
-/

namespace GeneralCK
open Certificates.Reflection
open Reflection

noncomputable def doubleCapSlopeBiasExpression (y c : ℝ) : ℝ :=
  2 - 2 * y / ((1 - y ^ 2) * SmallMean.A y) +
    2 * c ^ 2 / ((1 - c ^ 2) * biasB c)

/-- A monotone rational enclosure for the cancellation-free expression.
All four nonlinear bounds are supplied by the existing reflection witnesses;
the final hypothesis is a rational endpoint check. -/
theorem doubleCapSlopeBiasExpression_nonneg_of_bounds
    {y c yHi aLo cLo bHi : ℝ}
    (hy0 : 0 ≤ y) (hyHi : y ≤ yHi) (hyHi1 : yHi < 1)
    (haLo : 0 < aLo) (ha : aLo ≤ SmallMean.A y)
    (hcLo0 : 0 ≤ cLo) (hcLo : cLo ≤ c) (hc1 : c < 1)
    (hb : 0 < biasB c) (hbHi : biasB c ≤ bHi)
    (hcheck : 0 ≤ 2 - 2 * yHi / ((1 - yHi ^ 2) * aLo) +
      2 * cLo ^ 2 / ((1 - cLo ^ 2) * bHi)) :
    0 ≤ doubleCapSlopeBiasExpression y c := by
  have hyHi0 : 0 ≤ yHi := hy0.trans hyHi
  have hgapY : 0 < 1 - y ^ 2 := by nlinarith
  have hgapYHi : 0 < 1 - yHi ^ 2 := by nlinarith
  have hAY : 0 < SmallMean.A y := haLo.trans_le ha
  have hDY : 0 < (1 - y ^ 2) * SmallMean.A y := mul_pos hgapY hAY
  have hDYLo : 0 < (1 - yHi ^ 2) * aLo := mul_pos hgapYHi haLo
  have hgapCY : 0 < 1 - c ^ 2 := by nlinarith
  have hcLo1 : cLo < 1 := hcLo.trans_lt hc1
  have hgapCLo : 0 < 1 - cLo ^ 2 := by nlinarith
  have hbHi0 : 0 < bHi := hb.trans_le hbHi
  have hDC : 0 < (1 - c ^ 2) * biasB c := mul_pos hgapCY hb
  have hDCHi : 0 < (1 - cLo ^ 2) * bHi := mul_pos hgapCLo hbHi0
  have hgapYOrder : 1 - yHi ^ 2 ≤ 1 - y ^ 2 := by nlinarith
  have hDYOrder : (1 - yHi ^ 2) * aLo ≤
      (1 - y ^ 2) * SmallMean.A y := by
    exact mul_le_mul hgapYOrder ha haLo.le hgapY.le
  have hgapCOrder : 1 - c ^ 2 ≤ 1 - cLo ^ 2 := by nlinarith
  have hDCOrder : (1 - c ^ 2) * biasB c ≤
      (1 - cLo ^ 2) * bHi := by
    exact mul_le_mul hgapCOrder hbHi hb.le hgapCLo.le
  have hneg : y / ((1 - y ^ 2) * SmallMean.A y) ≤
      yHi / ((1 - yHi ^ 2) * aLo) := by
    apply (div_le_div_iff₀ hDY hDYLo).2
    nlinarith [mul_le_mul_of_nonneg_left hDYOrder hyHi0,
      mul_le_mul_of_nonneg_right hyHi hDYLo.le]
  have hpos : cLo ^ 2 / ((1 - cLo ^ 2) * bHi) ≤
      c ^ 2 / ((1 - c ^ 2) * biasB c) := by
    apply (div_le_div_iff₀ hDCHi hDC).2
    have hsq : cLo ^ 2 ≤ c ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hDCOrder (sq_nonneg cLo),
      mul_le_mul_of_nonneg_right hsq hDCHi.le]
  have hneg2 := mul_le_mul_of_nonneg_left hneg
    (by norm_num : (0 : ℝ) ≤ 2)
  have hpos2 := mul_le_mul_of_nonneg_left hpos
    (by norm_num : (0 : ℝ) ≤ 2)
  unfold doubleCapSlopeBiasExpression
  simp only [div_eq_mul_inv] at hcheck hneg2 hpos2 ⊢
  nlinarith only [hcheck, hneg2, hpos2]

/-- The radial value/derivative cancellation is exact in the natural contact
bias.  The bias `c` is the regular contact at natural radius `r/log 2`. -/
theorem doubleCapRadialSlopeGain_bias {r : ℝ} (hr : 0 < r) :
    let c := regularContact (r / Real.log 2)
    r * e8Theta (r / 2) - F r 1 =
      2 * c ^ 2 / ((1 - c ^ 2) * biasB c) := by
  dsimp only
  let c := regularContact (r / Real.log 2)
  have harg : 0 < r / Real.log 2 := div_pos hr log_two_pos
  have hc : c = 1 - 2 * radialContact r 1 := by
    dsimp [c]
    rw [regularContact_pos_eq harg]
    have hinv : (r / Real.log 2)⁻¹ = Real.log 2 / r := by
      field_simp [hr.ne', log_two_pos.ne']
    rw [hinv]
    simpa only [mul_one] using
      (Reflection.biasContact_scaled_ratio hr.ne' (1 : ℝ))
  have hcm := regularContact_mem (r / Real.log 2)
  have hgap : 0 < 1 - c ^ 2 := by
    dsimp [c]
    nlinarith [hcm.1, hcm.2]
  have hB : 0 < biasB c := biasB_pos_wide (by simpa [c] using hcm.1)
    (by simpa [c] using hcm.2)
  have hF := Reflection.RegularDifference.FNat_eq_F hr.le
    (by norm_num : (0 : ℝ) < 1)
  have hFs := Correction.Natural.Fs_contact hr
    (by norm_num : (0 : ℝ) < 1)
  have hder := deriv_F_radius_eq_e8Theta hr
    (by norm_num : (0 : ℝ) < 1)
  have heq := regularContact_equation (r / Real.log 2)
  change c = (r / Real.log 2) * biasE c at heq
  rw [← hc] at hFs
  rw [hder] at hFs
  simp only [mul_one] at hFs
  unfold Correction.Natural.Fs at hFs
  unfold Reflection.RegularDifference.FNat at hF
  simp only [mul_one] at hF
  change 2 * SmallMean.A c +
      biasE c * c / (((1 - c ^ 2) / 4) * (2 * biasB c)) =
    Real.log 2 * e8Theta (r / 2) at hFs
  change 2 * r * SmallMean.A c = Real.log 2 * F r 1 at hF
  have hln : Real.log 2 ≠ 0 := log_two_pos.ne'
  have hden : (1 - c ^ 2) * biasB c ≠ 0 :=
    (mul_pos hgap hB).ne'
  field_simp [hln, hden, hgap.ne', hB.ne'] at hFs heq
  have hmul :
      ((1 - c ^ 2) * biasB c) * Real.log 2 *
        (r * e8Theta (r / 2) - F r 1) =
      2 * c ^ 2 * Real.log 2 := by
    linear_combination
      (-r / 2) * hFs +
      ((1 - c ^ 2) * biasB c) * hF -
      (2 * c) * heq
  have hzero : Real.log 2 *
      ((r * e8Theta (r / 2) - F r 1) *
        ((1 - c ^ 2) * biasB c) - 2 * c ^ 2) = 0 := by
    nlinarith [hmul]
  have hcross : (r * e8Theta (r / 2) - F r 1) *
      ((1 - c ^ 2) * biasB c) = 2 * c ^ 2 := by
    rcases mul_eq_zero.mp hzero with hl | hr
    · exact False.elim (hln hl)
    · linarith
  change r * e8Theta (r / 2) - F r 1 =
    2 * c ^ 2 / ((1 - c ^ 2) * biasB c)
  exact (eq_div_iff hden).2 hcross

/-- The entropy derivative's inverse factor has an exact bias expression. -/
theorem doubleCapEntropySlopeTerm_bias {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) :
    let y := 1 - 2 * entropyInverse h
    (1 - 2 * entropyInverse h) /
      (Real.log 2 * entropyInverse h * (1 - entropyInverse h) *
        J (entropyInverse h)) =
      2 * y / ((1 - y ^ 2) * SmallMean.A y) := by
  dsimp only
  let v := entropyInverse h
  let y := 1 - 2 * v
  have hv : 0 < v := entropyInverse_pos hh hh1.le
  have hvh : v < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hJ : 0 < J v := J_pos hv hvh
  have hA := Correction.Natural.A_probability v
  change 2 * SmallMean.A y = Real.log 2 * J v at hA
  have hy : 0 < y := by dsimp [y]; linarith
  have hy1 : y < 1 := by dsimp [y]; linarith
  have hgap : 0 < 1 - y ^ 2 := by nlinarith
  have hAy : 0 < SmallMean.A y := by
    have := SmallMean.A_lower hy.le hy1
    linarith
  have hden : (1 - y ^ 2) * SmallMean.A y ≠ 0 :=
    (mul_pos hgap hAy).ne'
  have hgapEq : 1 - y ^ 2 = 4 * v * (1 - v) := by
    dsimp [y]
    ring
  have hAEq : SmallMean.A y = Real.log 2 * J v / 2 := by
    linarith [hA]
  have hdenEq : (1 - y ^ 2) * SmallMean.A y =
      2 * (Real.log 2 * v * (1 - v) * J v) := by
    rw [hgapEq, hAEq]
    ring
  change y / (Real.log 2 * v * (1 - v) * J v) =
    2 * y / ((1 - y ^ 2) * SmallMean.A y)
  rw [hdenEq]
  have hbase : Real.log 2 * v * (1 - v) * J v ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero log_two_pos.ne' hv.ne'
      · exact (by linarith : 0 < 1 - v).ne'
    · exact hJ.ne'
  field_simp [hbase]

/-- Exact cancellation-free form of the sufficient first-derivative sign. -/
theorem four_add_deriv_phi_eq_slopeBias {m h : ℝ}
    (hm : 0 < m) (hmh : m < 1 / 2) (hh : 0 < h) (hh1 : h < 1) :
    let y := 1 - 2 * entropyInverse h
    let c := regularContact (((1 - 2 * m) / h) / Real.log 2)
    4 + deriv (phi m) h = doubleCapSlopeBiasExpression y c := by
  dsimp only
  let r := (1 - 2 * m) / h
  have hr : 0 < r := div_pos (by linarith) hh
  have hbase := four_add_deriv_phi_eq_slopeFormula hm hmh hh hh1
  have hrad := doubleCapRadialSlopeGain_bias hr
  have hent := doubleCapEntropySlopeTerm_bias hh hh1
  dsimp only at hrad hent
  unfold doubleCapSlopeBiasExpression
  change r * e8Theta (r / 2) - F r 1 = _ at hrad
  change (1 - 2 * entropyInverse h) /
    (Real.log 2 * entropyInverse h * (1 - entropyInverse h) *
      J (entropyInverse h)) = _ at hent
  dsimp [r] at hrad
  linarith

/-- A small cell contract for the low or high slope tail.  The checker only
needs enclosures of the inverse-entropy bias, its `A`, the regular contact,
and its `biasB`, followed by a rational positivity test.  The exact bias
expression above promotes any such certificate to the actual slope sign. -/
structure DoubleCapOuterSlopeBiasCellCertificate
    (mLo mHi yHi aLo cLo bHi : ℝ) (floor : ℝ → ℝ) : Prop where
  domain : 0 < mLo ∧ mLo ≤ mHi ∧ mHi < 1 / 2
  yHi_lt_one : yHi < 1
  aLo_pos : 0 < aLo
  cLo_nonneg : 0 ≤ cLo
  bHi_pos : 0 < bHi
  rational_check : 0 ≤ 2 - 2 * yHi / ((1 - yHi ^ 2) * aLo) +
    2 * cLo ^ 2 / ((1 - cLo ^ 2) * bHi)
  floor_pos : ∀ m, mLo ≤ m → m ≤ mHi → 0 < floor m
  floor_lt_one : ∀ m, mLo ≤ m → m ≤ mHi → floor m < 1
  inverse_bias_upper : ∀ m, mLo ≤ m → m ≤ mHi →
    1 - 2 * entropyInverse (floor m) ≤ yHi
  inverse_A_lower : ∀ m, mLo ≤ m → m ≤ mHi →
    aLo ≤ SmallMean.A (1 - 2 * entropyInverse (floor m))
  contact_lower : ∀ m, mLo ≤ m → m ≤ mHi →
    cLo ≤ regularContact (((1 - 2 * m) / floor m) / Real.log 2)
  contact_B_upper : ∀ m, mLo ≤ m → m ≤ mHi →
    biasB (regularContact (((1 - 2 * m) / floor m) / Real.log 2)) ≤ bHi

theorem doubleCapOuterSlopeBiasCellCertificate_sound
    {mLo mHi yHi aLo cLo bHi : ℝ} {floor : ℝ → ℝ}
    (cert : DoubleCapOuterSlopeBiasCellCertificate
      mLo mHi yHi aLo cLo bHi floor)
    {m : ℝ} (hmLo : mLo ≤ m) (hmHi : m ≤ mHi) :
    -4 ≤ deriv (phi m) (floor m) := by
  have hm : 0 < m := cert.domain.1.trans_le hmLo
  have hmh : m < 1 / 2 := hmHi.trans_lt cert.domain.2.2
  have hh := cert.floor_pos m hmLo hmHi
  have hh1 := cert.floor_lt_one m hmLo hmHi
  have heq := four_add_deriv_phi_eq_slopeBias hm hmh hh hh1
  let y := 1 - 2 * entropyInverse (floor m)
  let c := regularContact (((1 - 2 * m) / floor m) / Real.log 2)
  have hy0 : 0 ≤ y := by
    dsimp [y]
    linarith [entropyInverse_lt_half hh.le hh1]
  have hc1 : c < 1 := (regularContact_mem _).2
  have hB : 0 < biasB c :=
    biasB_pos_wide (regularContact_mem _).1 hc1
  have hs : 0 ≤ doubleCapSlopeBiasExpression y c :=
    doubleCapSlopeBiasExpression_nonneg_of_bounds hy0
      (cert.inverse_bias_upper m hmLo hmHi) cert.yHi_lt_one
      cert.aLo_pos (cert.inverse_A_lower m hmLo hmHi)
      cert.cLo_nonneg (cert.contact_lower m hmLo hmHi)
      hc1 hB (cert.contact_B_upper m hmLo hmHi)
      cert.rational_check
  dsimp only at heq
  linarith

/-- A bounded low-tail pilot.  Its numerical constants come from an
outward-rounded Fraction preflight; the four witness fields remain explicit
until checked Lean endpoint enclosures have been emitted. -/
def DoubleCapOuterLowPilotCertificate : Prop :=
  DoubleCapOuterSlopeBiasCellCertificate
    (199 / 1000) (1 / 5)
    (789847 / 1000000) (2140014751 / 2000000000)
    (720787 / 1000000) (2123050721 / 2000000000)
    (fun m => H (2 * m) / 2)

theorem doubleCapLowSlopeResidual_nonneg_on_outer_pilot
    (cert : DoubleCapOuterLowPilotCertificate) :
    ∀ m, 199 / 1000 ≤ m → m ≤ 1 / 5 →
      0 ≤ doubleCapLowSlopeResidual m := by
  intro m hmLo hmHi
  have hs := doubleCapOuterSlopeBiasCellCertificate_sound cert hmLo hmHi
  have hm : 0 < m := by linarith
  have hmh : m < 1 / 2 := by linarith
  have hh := cert.floor_pos m hmLo hmHi
  have hh1 := cert.floor_lt_one m hmLo hmHi
  have heq := four_add_deriv_phi_eq_slopeFormula hm hmh hh hh1
  unfold doubleCapLowSlopeResidual
  dsimp only at heq ⊢
  linarith

/-- A narrow high-tail pilot; the weaker margin requires a shorter first
cell than on the low branch.  All witness bounds are still explicit. -/
def DoubleCapOuterHighPilotCertificate : Prop :=
  DoubleCapOuterSlopeBiasCellCertificate
    (2 / 5) (4001 / 10000)
    (142433 / 500000) (585306431 / 2000000000)
    (205841 / 1000000) (357420833 / 500000000)
    (fun m => (1 + H (2 * m - 1 / 2)) / 2)

theorem doubleCapHighSlopeResidual_nonneg_on_outer_pilot
    (cert : DoubleCapOuterHighPilotCertificate) :
    ∀ m, 2 / 5 ≤ m → m ≤ 4001 / 10000 →
      0 ≤ doubleCapHighSlopeResidual m := by
  intro m hmLo hmHi
  have hs := doubleCapOuterSlopeBiasCellCertificate_sound cert hmLo hmHi
  have hm : 0 < m := by linarith
  have hmh : m < 1 / 2 := by linarith
  have hh := cert.floor_pos m hmLo hmHi
  have hh1 := cert.floor_lt_one m hmLo hmHi
  have heq := four_add_deriv_phi_eq_slopeFormula hm hmh hh hh1
  unfold doubleCapHighSlopeResidual
  dsimp only at heq ⊢
  linarith

/- The outer tails still require checked enclosures of the two bias terms;
this module proves the exact expression and its sound promotion, without
asserting their signs. -/

#print axioms doubleCapRadialSlopeGain_bias
#print axioms doubleCapEntropySlopeTerm_bias
#print axioms four_add_deriv_phi_eq_slopeBias
#print axioms doubleCapSlopeBiasExpression_nonneg_of_bounds
#print axioms doubleCapOuterSlopeBiasCellCertificate_sound
#print axioms doubleCapLowSlopeResidual_nonneg_on_outer_pilot
#print axioms doubleCapHighSlopeResidual_nonneg_on_outer_pilot

end GeneralCK

end


