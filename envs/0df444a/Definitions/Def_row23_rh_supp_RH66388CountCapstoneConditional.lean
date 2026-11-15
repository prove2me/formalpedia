-- Prove2me | Definitions.Def_row23_rh_supp_RH66388CountCapstoneConditional
-- name    : row23_rh_supp_RH66388CountCapstoneConditional
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:00:39.06381+00:00
-- url     : https://prove2.me/theorems/f76086d5-ae1b-4c25-9a97-a87a27d2048f
-- title:
--   Row 23 RH support: RH66388CountCapstoneConditional
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388CountScalar
import Definitions.Def_row23_rh_supp_RH66388LineZeroLowerBound
import Theorems.Thm_RS5_BandZeros_hLine
import Theorems.Thm_Arb4_Q_cv_frac
import Theorems.Thm_Arb4_Q_cv_nat
import Theorems.Thm_Arb4_k6side_of_B
import Theorems.Thm_BandGlue_BandData_CapGeom_of_sqrt
import Theorems.Thm_H11K_boxCert_of_parts_sharp
import Theorems.Thm_H11K_validS_of_B
import Theorems.Thm_ZeroFreeBridge_dlvpRateC_lower
import Theorems.Thm_ZetaZeroConfinement_zero_in_band
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Complex Arb4 Arb4.Q
namespace RH66388Count

def center : ℂ := ⟨1 / 2, 66509 / 2⟩
def radius : ℝ := Real.sqrt (4391315305 / 4)

theorem one_not_in_ball : (1 : ℂ) ∉ Metric.ball center radius := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold center radius
  intro hlt
  simp only [Complex.one_re, Complex.one_im] at hlt
  have hle : Real.sqrt (4391315305 / 4 : ℝ) ≤
      Real.sqrt (((1 : ℝ) - (1 / 2)) ^ 2 + ((0 : ℝ) - 66509 / 2) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num)
  linarith [hlt, hle]

def band : BandGlue.BandData :=
  ⟨121, 66388, 87295, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, center, radius, one_not_in_ball⟩

/-- The proposed count certifies a zero box once the stated boundary inputs are supplied. -/
theorem box_of_boundary_inputs
    (hslab1 : EdgeClearGlue.SlabClear (66388 : ℝ) ((66388 : ℝ) + 3 / 1000))
    (hslab0 : EdgeClearGlue.SlabClear ((121 : ℝ) - 5773 / 100000) 121)
    (hH1 : DiffractionCore.argChangeHoriz riemannZeta (66388 : ℝ) 2 (-1) ∈
      Set.Icc enclosure.L2.val enclosure.H2.val)
    (hH0 : DiffractionCore.argChangeHoriz riemannZeta (121 : ℝ) 2 (-1) ∈
      Set.Icc enclosure.L3.val enclosure.H3.val) :
    BandGlue.BoxCert (1 / 4000000) (3999999 / 4000000) 121 66388 := by
  have hc := scalar_check
  rw [Bool.and_eq_true] at hc
  have hT0 : band.T0 = (Q.ofNat 121).val := (Q.cv_nat 121).symm
  have hT1 : band.T1 = (Q.ofNat 66388).val := (Q.cv_nat 66388).symm
  have hcc : band.c = (⟨1 / 2, (Q.frac 66509 2).val⟩ : ℂ) := by
    rw [Q.cv_frac 66509 2]; rfl
  have hR : band.R = Real.sqrt (Q.frac 4391315305 4).val := by
    rw [Q.cv_frac 4391315305 4]; rfl
  have hG : band.CapGeom (5773 / 100000) (3 / 1000) :=
    BandGlue.BandData.CapGeom.of_sqrt 121 66388 (66509 / 2) (4391315305 / 4) rfl rfl rfl rfl
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine H11K.boxCert_of_parts_sharp band enclosure (show (121 : ℝ) ≤ 121 from le_rfl)
    (show (66388 : ℝ) ≤ 66388 from le_rfl)
    (H11K.validS_of_B _ _ _ _ _ enclosure hT0 hT1 hcc hR hc.1) hG
    ?_ hslab0 hslab1 (k6side_of_B _ H65K.Count121.G0 G1 enclosure hT0 hT1 hc.2) hH1 hH0
  exact RH66388NewBand.line_zero_lower_bound_121_66388.hLine

theorem log_bound : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 66388 := by
  have hlog : Real.log 66388 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 66388 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 66388 ≤ (1 / 4000000 : ℝ) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- RH in the new range, conditional on the explicitly stated prior-band and boundary certificates. -/
theorem segment_of_boundary_inputs
    (hslab1 : EdgeClearGlue.SlabClear (66388 : ℝ) ((66388 : ℝ) + 3 / 1000))
    (hslab0 : EdgeClearGlue.SlabClear ((121 : ℝ) - 5773 / 100000) 121)
    (hH1 : DiffractionCore.argChangeHoriz riemannZeta (66388 : ℝ) 2 (-1) ∈
      Set.Icc enclosure.L2.val enclosure.H2.val)
    (hH0 : DiffractionCore.argChangeHoriz riemannZeta (121 : ℝ) 2 (-1) ∈
      Set.Icc enclosure.L3.val enclosure.H3.val)
    (ρ : ℂ) (hz : riemannZeta ρ = 0) (him0 : 0 < ρ.im)
    (himA : (121 : ℝ) ≤ ρ.im) (himB : ρ.im ≤ 66388) : ρ.re = 1 / 2 := by
  have hγ : (55 / 16 : ℝ) ≤ |ρ.im| := by rw [abs_of_pos him0]; linarith
  obtain ⟨hlo, hhi⟩ := ZetaZeroConfinement.zero_in_band
    (1 / 4000000) 66388 log_bound (by norm_num) (by norm_num) hz him0 himB hγ
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  obtain ⟨d, hdlo, hdhi, hStmt, hInputs⟩ := box_of_boundary_inputs hslab1 hslab0 hH1 hH0
  exact hStmt hInputs.1 hInputs.2 ρ ⟨hlo, by linarith [hhi, hre_eq]⟩
    ⟨le_trans hdlo himA, le_trans himB hdhi⟩ hz

end RH66388Count
#print axioms RH66388Count.segment_of_boundary_inputs


