-- Prove2me | Definitions.Def_CK_CKLaneC2_Final
-- name    : CK_CKLaneC2_Final
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T08:48:34.217868+00:00
-- url     : https://prove2.me/theorems/e91e537d-890c-4722-8f82-218f52a412e9
-- title:
--   Courtade–Kumar proof module `CKLaneC2.Final` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2.Final` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2.Final` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2.Final (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2/Final.lean)

import Definitions.Def_CK_CKLaneC2_Cover
import Definitions.Def_CK_CKLaneC2_PointData
import Definitions.Def_CK_GeneralCK_LanePHMC_Chain

-- ===== source module CKLaneC2.Final =====
section
/-
Lane C2 — FINAL ASSEMBLY.

`halfMeanSlopeGap_certified` is exactly the body of P-HMC's `HalfMeanSlopeGapOnCompact`
(`GeneralCK.LanePHMC.Reduce`, source sha256 e275ce45…67ce, olean sha256 23e51c2c…8111 — rebuilt
byte-identically in this lane's consumer-consistent root).  It is proved from:
  * `slope_gap_of_comparison` (Structural, pure analysis),
  * `gfun` antitone on `[x₁, T]` (Cover: 51 kernel-checked cells; Bridge: transfer from `c` to `t`),
  * the point conditions at `c₁ = 69/5000` and `c_T = 23/25` (PointData, kernel-checked).
Then `halfMeanCurvatureNegative_certified : HalfMeanCurvatureNegative` via the P-HMC chain
`GeneralCK.LanePHMC.halfMeanCurvatureNegative_of_slopeGap` (with `e8LargeSStructureCertified`).
-/

set_option autoImplicit false

namespace CKLaneC2

open GeneralCK Set

theorem halfMeanSlopeGap_certified :
    ∀ x w : ℝ, 0 < x → 0 < w →
      e8Theta w = 2 * e8Theta x →
      e8Theta x ∈ Set.Icc (2 / 25 : ℝ) (63 / 20) →
      2 * deriv e8Theta x * (1 - x / w) < pureGapTheta0 := by
  intro x w hx hw hcouple hmem
  have hp1 : PtFacts cp0 := Pt.ok_sound pt1_ok
  have hpT : PtFacts coverPT := Pt.ok_sound ptT_ok
  have hc1 : (cp0.c : ℝ) = ((69 / 5000 : ℚ) : ℝ) := rfl
  have hcT : (coverPT.c : ℝ) = ((23 / 25 : ℚ) : ℝ) := rfl
  have h1T : (cp0.c : ℝ) ≤ (coverPT.c : ℝ) := by rw [hc1, hcT]; norm_num
  -- antitonicity of the comparison slope on [x₁, T]
  have hGanti : AntitoneOn Gf (Icc (cp0.c : ℝ) (coverPT.c : ℝ)) := by
    rw [hc1, hcT]; exact Gf_antitone_cover
  have hanti := gfun_antitone_of_Gf hp1.c_pos hpT.c_lt h1T hGanti
  set x₁ := E8AnalyticGerm.xParamReal (cp0.c : ℝ) with hx₁def
  set T := E8AnalyticGerm.xParamReal (coverPT.c : ℝ) with hTdef
  have hx₁ : 0 < x₁ := xParam_pos hp1.c_pos hp1.c_lt
  have hT0 : 0 < T := xParam_pos hpT.c_pos hpT.c_lt
  -- point conditions
  have hgT : 0 < gfun T := gfun_pos_of_chk hpT chk_NT
  have hU := tau_le_of_chk hp1 chk_tau1
  have hS2 := S2_of_chk hp1 chk_S2
  have hΘ1 : e8Theta x₁ < 2 / 25 := by
    have h := thetaParam_lt_of_chk hp1 chk_theta1
    rw [hx₁def, E8AnalyticGerm.e8Theta_xParamReal hp1.c_pos hp1.c_lt]
    have e : ((2 / 25 : ℚ) : ℝ) = 2 / 25 := by norm_num
    rw [e] at h
    exact h
  have hΘT : 63 / 10 < e8Theta T := by
    have h := thetaParam_gt_of_chk hpT chk_thetaT
    rw [hTdef, E8AnalyticGerm.e8Theta_xParamReal hpT.c_pos hpT.c_lt]
    have e : ((63 / 10 : ℚ) : ℝ) = 63 / 10 := by norm_num
    rw [e] at h
    exact h
  -- order facts from strict monotonicity of e8Theta
  have hmono := strictMonoOn_e8Theta_pos
  have hΘx : 0 < e8Theta x := e8Theta_pos hx
  have hx1x : x₁ ≤ x := by
    by_contra hlt
    have hlt' : x < x₁ := lt_of_not_ge hlt
    have := hmono (mem_Ioi.mpr hx) (mem_Ioi.mpr hx₁) hlt'
    linarith [hmem.1]
  have hxw : x < w := by
    by_contra hle
    have hle' : w ≤ x := le_of_not_gt hle
    have := hmono.monotoneOn (mem_Ioi.mpr hw) (mem_Ioi.mpr hx) hle'
    linarith
  have hwT : w ≤ T := by
    by_contra hlt
    have hlt' : T < w := lt_of_not_ge hlt
    have := hmono (mem_Ioi.mpr hT0) (mem_Ioi.mpr hw) hlt'
    linarith [hmem.2]
  have hd : 0 < deriv e8Theta x := deriv_e8Theta_pos hx
  have htheta := pureGapTheta0_pos
  rcases le_or_gt (2 * deriv e8Theta x) pureGapTheta0 with hsmall | hlarge
  · -- 2Θ'(x) ≤ θ0: the gap holds with no reference to w
    have hxw' : 0 < x / w := div_pos hx hw
    by_cases h1 : 1 - x / w ≤ 0
    · have : 2 * deriv e8Theta x * (1 - x / w) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
      linarith
    · have h1' : 0 < 1 - x / w := lt_of_not_ge h1
      calc 2 * deriv e8Theta x * (1 - x / w) ≤ pureGapTheta0 * (1 - x / w) :=
            mul_le_mul_of_nonneg_right hsmall h1'.le
        _ < pureGapTheta0 := by nlinarith
  · -- 2Θ'(x) > θ0: the arctan comparison
    have key := slope_gap_of_comparison hx₁ hanti hgT hU hS2 hx1x hxw hwT hcouple hlarge
    have e : 2 * deriv e8Theta x * (1 - x / w)
        = (2 * deriv e8Theta x * w - 2 * deriv e8Theta x * x) / w := by
      field_simp
    rw [e, div_lt_iff₀ hw]
    linarith

/-- The obligation named by P-HMC, discharged. -/
theorem halfMeanSlopeGapOnCompact_certified : GeneralCK.LanePHMC.HalfMeanSlopeGapOnCompact :=
  halfMeanSlopeGap_certified

/-- **Field 6** (`ProductionOwners.halfMeanCurvature`): unconditional. -/
theorem halfMeanCurvatureNegative_certified : HalfMeanCurvatureNegative :=
  GeneralCK.LanePHMC.halfMeanCurvatureNegative_of_slopeGap halfMeanSlopeGapOnCompact_certified

/-- The same term against the field type written out in full (gate "unfolded"). -/
example :
    ∀ a e f : ℝ, a < 1 / 2 → 0 < e → 0 < f →
      e < H a → f < H (1 / 2) →
      e8Theta ((1 / 2 - a) / e) =
        2 * e8Theta ((1 / 2 - a) / (e + f)) →
      deriv (deriv (halfMeanPureGapCurve a e f)) (1 / 2) < 0 :=
  halfMeanCurvatureNegative_certified

/- Positive control: these lines must appear in the compile log (an empty log is not evidence). -/
#check @halfMeanCurvatureNegative_certified
#print axioms halfMeanCurvatureNegative_certified

end CKLaneC2

end


