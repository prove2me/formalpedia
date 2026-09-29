-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8LocalContactContraction
-- name    : CK_GeneralCK_Certificates_E8LocalContactContraction
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T12:43:54.527217+00:00
-- url     : https://prove2.me/theorems/73c2c4d5-9865-447b-a462-373934406ee0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8LocalContactContraction` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8LocalContactContraction` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8LocalContactContraction` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8LocalContactContraction (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8LocalContactContraction.lean)

import Definitions.Def_CK_GeneralCK_ReflectionComplexGlobalAnalytic
import Definitions.Def_CK_GeneralCK_ReflectionComplexContactGerm

-- ===== source module GeneralCK.Certificates.E8LocalContactContraction =====
section

/-! A sharper contraction package on the contact disc actually reached for
`‖tau‖ ≤ 2/5`.  This is the analytic basis for locally centered E8 leaves. -/

namespace GeneralCK.Certificates.E8LocalContactContraction

open Set Function
open Reflection.ComplexEntropy Reflection.ComplexContactGerm
open Reflection.ComplexDiscElementary

theorem norm_entropyDeriv_le_two_fifths {c : ℂ}
    (hc : ‖c‖ ≤ (1 / 3 : ℝ)) : ‖entropyDeriv c‖ ≤ (2 / 5 : ℝ) := by
  have hc1 : ‖c‖ < (1 : ℝ) := hc.trans_lt (by norm_num)
  have hinv : (1 - ‖c‖)⁻¹ ≤ (3 / 2 : ℝ) := by
    rw [inv_le_comm₀ (sub_pos.mpr hc1) (by norm_num : (0 : ℝ) < 3 / 2)]
    linarith
  calc
    ‖entropyDeriv c‖ ≤ ‖c‖ + ‖c‖ ^ 3 / 3 +
        ‖c‖ ^ 5 * (1 - ‖c‖)⁻¹ / 5 := norm_entropyDeriv_le hc1
    _ ≤ (1 / 3 : ℝ) + (1 / 3 : ℝ) ^ 3 / 3 +
        (1 / 3 : ℝ) ^ 5 * (3 / 2) / 5 := by gcongr
    _ ≤ (2 / 5 : ℝ) := by norm_num

theorem entropyExt_lipschitzOnWith_two_fifths :
    LipschitzOnWith (2 / 5 : NNReal) entropyExt
      (Metric.closedBall 0 (1 / 3 : ℝ)) := by
  apply (convex_closedBall (0 : ℂ) (1 / 3 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
  · intro c hc
    have hc' : ‖c‖ ≤ (1 / 3 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hc
    exact (hasDerivAt_entropyExt (hc'.trans_lt (by norm_num))).differentiableAt
  · intro c hc
    have hc' : ‖c‖ ≤ (1 / 3 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hc
    rw [(hasDerivAt_entropyExt (hc'.trans_lt (by norm_num))).deriv]
    exact_mod_cast norm_entropyDeriv_le_two_fifths hc'

theorem norm_entropyExt_le_five_sixths {c : ℂ}
    (hc : c ∈ Metric.closedBall 0 (1 / 3 : ℝ)) :
    ‖entropyExt c‖ ≤ (5 / 6 : ℝ) := by
  have hzero : (0 : ℂ) ∈ Metric.closedBall 0 (1 / 3 : ℝ) := by simp
  have hlip := entropyExt_lipschitzOnWith_two_fifths.dist_le_mul c hc 0 hzero
  rw [entropyExt_zero, dist_eq_norm] at hlip
  have hc' : ‖c‖ ≤ (1 / 3 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hc
  have hlog : ‖(Real.log 2 : ℂ)‖ ≤ (7 / 10 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (by norm_num))]
    exact (Real.log_two_lt_d9.trans (by norm_num)).le
  have hlip' : ‖entropyExt c - (Real.log 2 : ℂ)‖ ≤
      (2 / 5 : ℝ) * ‖c‖ := by simpa [dist_eq_norm] using hlip
  calc
    ‖entropyExt c‖ ≤ ‖entropyExt c - (Real.log 2 : ℂ)‖ +
        ‖(Real.log 2 : ℂ)‖ := norm_le_norm_sub_add _ _
    _ ≤ (2 / 5 : ℝ) * ‖c‖ + (7 / 10 : ℝ) := add_le_add hlip' hlog
    _ ≤ (2 / 5 : ℝ) * (1 / 3) + (7 / 10 : ℝ) := by gcongr
    _ ≤ (5 / 6 : ℝ) := by norm_num

theorem contact_mapsTo_third {tau : ℂ} (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) :
    MapsTo (contactMap entropyExt tau)
      (Metric.closedBall 0 (1 / 3 : ℝ)) (Metric.closedBall 0 (1 / 3 : ℝ)) := by
  intro c hc
  simp only [Metric.mem_closedBall, dist_zero_right, contactMap]
  rw [norm_mul]
  calc
    ‖tau‖ * ‖entropyExt c‖ ≤ (2 / 5 : ℝ) * (5 / 6 : ℝ) :=
      mul_le_mul htau (norm_entropyExt_le_five_sixths hc) (norm_nonneg _) (by norm_num)
    _ = (1 / 3 : ℝ) := by norm_num

theorem contact_lipschitzOnWith_four_twentyfive {tau : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) :
    LipschitzOnWith (4 / 25 : NNReal) (contactMap entropyExt tau)
      (Metric.closedBall 0 (1 / 3 : ℝ)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro c hc d hd
  simp only [contactMap, dist_eq_norm, ← mul_sub]
  rw [norm_mul]
  have hE := entropyExt_lipschitzOnWith_two_fifths.dist_le_mul c hc d hd
  have hE' : ‖entropyExt c - entropyExt d‖ ≤
      (2 / 5 : ℝ) * ‖c - d‖ := by simpa [dist_eq_norm] using hE
  calc
    ‖tau‖ * ‖entropyExt c - entropyExt d‖ ≤
        (2 / 5 : ℝ) * ((2 / 5 : ℝ) * ‖c - d‖) :=
      mul_le_mul htau hE' (norm_nonneg _) (by norm_num)
    _ = (4 / 25 : ℝ) * ‖c - d‖ := by ring

private abbrev thirdDisc : Set ℂ := Metric.closedBall 0 (1 / 3 : ℝ)

private theorem contact_contracting_restrict {tau : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) :
    ContractingWith (4 / 25 : NNReal)
      ((contact_mapsTo_third htau).restrict
        (contactMap entropyExt tau) thirdDisc thirdDisc) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro c d
  exact (contact_lipschitzOnWith_four_twentyfive htau).dist_le_mul
    c c.property d d.property

theorem fixedPointOnDisc_mem_third {tau : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) :
    Reflection.ComplexGlobalAnalytic.fixedPointOnDisc tau ∈ thirdDisc := by
  have hcomplete : IsComplete thirdDisc := Metric.isClosed_closedBall.isComplete
  have hzero : (0 : ℂ) ∈ thirdDisc := by simp [thirdDisc]
  have hfinite := edist_ne_top (0 : ℂ) (contactMap entropyExt tau 0)
  rcases (contact_contracting_restrict htau).exists_fixedPoint'
      hcomplete (contact_mapsTo_third htau) hzero hfinite with
    ⟨c, hc, hfix, _hlim, _herror⟩
  have hcBig : c ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ) := by
    have hcNorm : ‖c‖ ≤ (1 / 3 : ℝ) := by
      simpa only [thirdDisc, Metric.mem_closedBall, dist_zero_right] using hc
    simpa only [Metric.mem_closedBall, dist_zero_right]
      using hcNorm.trans (by norm_num)
  have htauSeven : ‖tau‖ ≤ (7 / 10 : ℝ) := htau.trans (by norm_num)
  have heq : c = Reflection.ComplexFixedPoint.fixedPoint tau htauSeven :=
    Reflection.ComplexFixedPoint.eq_fixedPoint htauSeven hcBig hfix
  have hopen : ‖tau‖ < (7 / 10 : ℝ) := htau.trans_lt (by norm_num)
  rw [Reflection.ComplexGlobalAnalytic.fixedPointOnDisc_eq hopen, ← heq]
  exact hc

/-- A local residual turns directly into a certified distance to the chosen
fixed point, with loss only `1/(1-4/25) = 25/21`. -/
theorem fixedPointOnDisc_dist_le_residual {tau z : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) (hz : z ∈ thirdDisc) :
    dist (Reflection.ComplexGlobalAnalytic.fixedPointOnDisc tau) z ≤
      (25 / 21 : ℝ) * dist (contactMap entropyExt tau z) z := by
  let p := Reflection.ComplexGlobalAnalytic.fixedPointOnDisc tau
  have hp : p ∈ thirdDisc := fixedPointOnDisc_mem_third htau
  have hfix : contactMap entropyExt tau p = p := by
    have hopen : ‖tau‖ < (7 / 10 : ℝ) := htau.trans_lt (by norm_num)
    exact (Reflection.ComplexGlobalAnalytic.fixedPointOnDisc_fixed hopen).symm
  have hlip := (contact_lipschitzOnWith_four_twentyfive htau).dist_le_mul
    p hp z hz
  have htri : dist p z ≤ dist (contactMap entropyExt tau p)
      (contactMap entropyExt tau z) + dist (contactMap entropyExt tau z) z := by
    rw [hfix]
    exact dist_triangle _ _ _
  have hmain : dist p z ≤ (4 / 25 : ℝ) * dist p z +
      dist (contactMap entropyExt tau z) z := htri.trans
        (add_le_add hlip (le_refl _))
  dsimp [p] at hmain ⊢
  have hpz : 0 ≤ dist (Reflection.ComplexGlobalAnalytic.fixedPointOnDisc tau) z :=
    dist_nonneg
  have hr : 0 ≤ dist (contactMap entropyExt tau z) z := dist_nonneg
  nlinarith

end GeneralCK.Certificates.E8LocalContactContraction

end


