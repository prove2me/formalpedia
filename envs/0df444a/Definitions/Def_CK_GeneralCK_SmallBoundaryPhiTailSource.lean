-- Prove2me | Definitions.Def_CK_GeneralCK_SmallBoundaryPhiTailSource
-- name    : CK_GeneralCK_SmallBoundaryPhiTailSource
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:53:07.484254+00:00
-- url     : https://prove2.me/theorems/a41a528f-557a-4f82-9abb-a75909f17d08
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallBoundaryPhiTailSource` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallBoundaryPhiTailSource` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallBoundaryPhiTailSource` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallBoundaryPhiTailSource (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallBoundaryPhiTailSource.lean)

import Definitions.Def_CK_GeneralCK_SmallBoundaryPhiTailCoordinates
import Definitions.Def_CK_GeneralCK_SmallBoundaryPhiTailBox

-- ===== source module GeneralCK.SmallBoundaryPhiTailSource =====
section

namespace GeneralCK.SmallBoundaryPhiSchur

open Set Filter
open scoped Topology

set_option maxHeartbeats 4000000

private theorem coordinate_positivity {t : ℝ} (ht : 0 < t) (ht' : t < 1/2) :
    0 < 1-t ∧ 0 < tailZ t ∧ 0 < tailB t ∧
      0 < SmallBoundaryPhiTailBox.pFactor t (tailZ t) (tailB t) ∧
      0 < SmallBoundaryPhiTailBox.cFactor t (tailZ t) (tailB t) := by
  have ht1 : t < 1 := by linarith
  have hz := tailZ_pos ht ht1
  have hb : 0 < tailB t := lt_of_lt_of_le (by norm_num) (tailB_bounds ht ht1).1
  have hc : 0 < 1-t := by linarith
  refine ⟨hc,hz,hb,?_,?_⟩ <;>
    dsimp [SmallBoundaryPhiTailBox.pFactor,SmallBoundaryPhiTailBox.cFactor] <;> positivity

theorem actualA_eq_box {t : ℝ} (ht : 0 < t) (ht' : t < 1/2) :
    naturalA t = SmallBoundaryPhiTailBox.A t (tailZ t) (tailB t) := by
  obtain ⟨hc,hz,hb,hp,_⟩ := coordinate_positivity ht ht'
  have ht1 : t < 1 := by linarith
  have hk : Certificates.Mixed.kap t =
      (1+t*tailB t*tailZ t)/(2*tailZ t) := by
    unfold Certificates.Mixed.kap
    rw [Real.log_mul ht.ne' hc.ne', log_eq_tailZ ht ht1,
      log_complement_eq_tailB t ht.ne']
    field_simp [hz.ne']
    ring
  rw [naturalA, Certificates.Mixed.profile, hn_eq_tailCoordinates ht ht1, hk]
  dsimp [
    SmallBoundaryPhiTailBox.A, SmallBoundaryPhiTailBox.aNum, SmallBoundaryPhiTailBox.aDen,
    SmallBoundaryPhiTailBox.cFactor, SmallBoundaryPhiTailBox.pFactor]
  dsimp [SmallBoundaryPhiTailBox.pFactor] at hp
  field_simp [ht.ne', hc.ne', hz.ne', log_two_pos.ne', hp.ne']
  ring

theorem actualK_eq_box {t : ℝ} (ht : 0 < t) (ht' : t < 1/2) :
    naturalK t = SmallBoundaryPhiTailBox.K t (tailZ t) (tailB t) := by
  obtain ⟨hc,hz,hb,hp,_⟩ := coordinate_positivity ht ht'
  have ht1 : t < 1 := by linarith
  dsimp [naturalK, Certificates.Mixed.hn,
    SmallBoundaryPhiTailBox.K, SmallBoundaryPhiTailBox.kNum, SmallBoundaryPhiTailBox.kDen,
    SmallBoundaryPhiTailBox.cFactor, SmallBoundaryPhiTailBox.mFactor]
  rw [Real.log_div hc.ne' ht.ne', log_eq_tailZ ht ht1, log_complement_eq_tailB t ht.ne']
  field_simp [ht.ne', hc.ne', hz.ne']
  ring

theorem coordinate_mFactor_pos {t : ℝ} (ht : 0 < t) (ht' : t < 1/2) :
    0 < SmallBoundaryPhiTailBox.mFactor t (tailZ t) (tailB t) := by
  have ht1 : t < 1 := by linarith
  have hz := tailZ_pos ht ht1
  have hc : 1-t ≠ 0 := by linarith
  have hj := J_pos ht ht'
  have he : Real.log 2*J t=(1/tailZ t-t*tailB t) := by
    unfold J
    rw [Real.log_div hc ht.ne', log_eq_tailZ ht ht1,
      log_complement_eq_tailB t ht.ne']
    field_simp
    ring
  have hp := mul_pos hz (mul_pos log_two_pos hj)
  rw [he] at hp
  have hid : tailZ t*(1/tailZ t-t*tailB t)=
      SmallBoundaryPhiTailBox.mFactor t (tailZ t) (tailB t) := by
    dsimp [SmallBoundaryPhiTailBox.mFactor]
    field_simp [hz.ne']
  rwa [hid] at hp

theorem actual_difference_eq_box {t : ℝ} (ht : 0 < t) (ht' : t < 1/2) :
    naturalA t-naturalK t = t*SmallBoundaryPhiTailBox.differenceNum t (tailZ t) (tailB t) /
      SmallBoundaryPhiTailBox.differenceDen t (tailZ t) (tailB t) := by
  obtain ⟨hc,_,_,hp,_⟩ := coordinate_positivity ht ht'
  have hm := coordinate_mFactor_pos ht ht'
  rw [actualA_eq_box ht ht', actualK_eq_box ht ht',
    SmallBoundaryPhiTailBox.differenceNum_identity]
  dsimp [SmallBoundaryPhiTailBox.A, SmallBoundaryPhiTailBox.K,
    SmallBoundaryPhiTailBox.aDen, SmallBoundaryPhiTailBox.kDen,
    SmallBoundaryPhiTailBox.differenceDen]
  field_simp [hc.ne',hp.ne',hm.ne']

theorem hasDerivAt_boxA_curve {t : ℝ} (ht : 0 < t) (ht' : t < 1/2) :
    HasDerivAt (fun u => SmallBoundaryPhiTailBox.A u (tailZ u) (tailB u))
      (SmallBoundaryPhiTailBox.normalizedDerivative t (tailZ t) (tailB t)/t) t := by
  obtain ⟨hc,hz,hb,hp,hcF⟩ := coordinate_positivity ht ht'
  have ht1 : t < 1 := by linarith
  have hd := hasDerivAt_id t
  have hZ := hasDerivAt_tailZ ht ht1
  have hB := hasDerivAt_tailB ht ht1
  have hC := (((hd.const_sub 1).mul hB).mul hZ).const_add 1
  have hP := ((hd.mul hB).mul hZ).const_add 1
  have hT := (hd.const_mul 2).const_sub 1
  have hN := ((hC.pow 2).mul hT).mul (hP.sub ((hT.pow 2).mul hZ))
  have hD := ((hd.const_sub 1).pow 2).mul (hP.pow 3)
  have hAD := hN.div hD (by
    change (1-t)^2*(1+t*tailB t*tailZ t)^3 ≠ 0
    exact mul_ne_zero (pow_ne_zero _ hc.ne') (pow_ne_zero _ hp.ne'))
  convert! hAD using 1
  dsimp [SmallBoundaryPhiTailBox.normalizedDerivative,
    SmallBoundaryPhiTailBox.derivativeNum, SmallBoundaryPhiTailBox.derivativeDen,
    SmallBoundaryPhiTailBox.cFactor, SmallBoundaryPhiTailBox.pFactor]
  dsimp [SmallBoundaryPhiTailBox.pFactor] at hp
  field_simp [ht.ne', hc.ne', hp.ne']
  ring

theorem hasDerivAt_naturalA_scaled {t : ℝ} (ht : 0 < t) (ht' : t < 1/2) :
    HasDerivAt naturalA
      (SmallBoundaryPhiTailBox.normalizedDerivative t (tailZ t) (tailB t)/t) t := by
  apply (hasDerivAt_boxA_curve ht ht').congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht ht'] with u hu
  exact actualA_eq_box hu.1 hu.2

theorem hasDerivAt_log_entropy_ratio {t : ℝ} (ht : 0 < t) (ht' : t < 1/2) :
    HasDerivAt (fun u => Real.log (H u/(1-2*u)))
      (SmallBoundaryPhiTailBox.EL t (tailZ t) (tailB t)/t) t := by
  obtain ⟨hc,hz,hb,hp,hcF⟩ := coordinate_positivity ht ht'
  have ht1 : t < 1 := by linarith
  have hτ : 0 < 1-2*t := by linarith
  have hH : 0 < H t := H_pos ht ht1
  have hD := (Comparison.hasDerivAt_H ht ht1).div
    (((hasDerivAt_id t).const_mul 2).const_sub 1) hτ.ne'
  have hd := hD.log (ne_of_gt (div_pos hH hτ))
  have heH : H t = (t/tailZ t)*(1+(1-t)*tailB t*tailZ t)/Real.log 2 := by
    apply (eq_div_iff log_two_pos.ne').mpr
    rw [← Certificates.Mixed.hn_eq_H_mul_log]
    exact hn_eq_tailCoordinates ht ht1
  have heJ : J t = (1/tailZ t-t*tailB t)/Real.log 2 := by
    unfold J
    rw [Real.log_div hc.ne' ht.ne', log_eq_tailZ ht ht1,
      log_complement_eq_tailB t ht.ne']
    ring
  convert! hd using 1
  simp only [Pi.div_apply,id_eq]
  rw [heH, heJ]
  dsimp [SmallBoundaryPhiTailBox.EL, SmallBoundaryPhiTailBox.cFactor,
    SmallBoundaryPhiTailBox.pFactor]
  dsimp [SmallBoundaryPhiTailBox.cFactor] at hcF
  field_simp [ht.ne', hz.ne', hτ.ne', log_two_pos.ne', hcF.ne']
  ring

theorem hasDerivAt_comparisonPotential {t : ℝ} (ht : 0 < t) (ht' : t < 1/2) :
    HasDerivAt comparisonPotential
      ((SmallBoundaryPhiTailBox.normalizedDerivative t (tailZ t) (tailB t) -
        SmallBoundaryPhiTailBox.EL t (tailZ t) (tailB t)/10)/t) t := by
  have hd := (hasDerivAt_naturalA_scaled ht ht').sub
    ((hasDerivAt_log_entropy_ratio ht ht').const_mul (1/10))
  convert! hd using 1
  ring

#print axioms actualA_eq_box
#print axioms actualK_eq_box
#print axioms coordinate_mFactor_pos
#print axioms actual_difference_eq_box
#print axioms hasDerivAt_boxA_curve
#print axioms hasDerivAt_naturalA_scaled
#print axioms hasDerivAt_log_entropy_ratio
#print axioms hasDerivAt_comparisonPotential

end GeneralCK.SmallBoundaryPhiSchur

end


