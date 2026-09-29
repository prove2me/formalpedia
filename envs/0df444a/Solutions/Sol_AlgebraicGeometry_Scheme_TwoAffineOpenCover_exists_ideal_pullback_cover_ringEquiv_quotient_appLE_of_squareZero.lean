-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f17dde40-bc82-552a-acd3-27f329457a8e

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"

set_option autoImplicit false
set_option maxHeartbeats 16000000

noncomputable section

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero.AlgebraicGeometry TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE Scheme.Hom Spec Scheme Scheme.Hom.appLE_map RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelPicard.LFP.stageHom Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE Hom mk Hom.appLE_map TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.baseChangeSnd_preimage_U0 TwoAffineOpenCover.baseChangeSnd_preimage_U1 TwoAffineOpenCover.baseChangeSnd_preimage_inf"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap cover cover_ρ0_apply cover_ρ1_apply pullback U1 U0 mk exists_stage_baseChangeIsos_structureSheaf baseChangeSnd_preimage_U0 baseChangeSnd_preimage_U1 baseChangeSnd_preimage_inf"
namespace ChartQuotAppLE
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {B : Type u} [CommRing B] (I : Ideal B) (A : Type u) [CommRing A] [Algebra B A]

noncomputable def quotMapEquiv : (A ⧸ (I.map (algebraMap B A))) ≃+* ((B ⧸ I) ⊗[B] A) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).toRingEquiv.trans
    (Algebra.TensorProduct.comm B A (B ⧸ I)).toRingEquiv

theorem quotMapEquiv_mk (a : A) :
    quotMapEquiv I A (Ideal.Quotient.mk _ a) = (1 : B ⧸ I) ⊗ₜ[B] a := by
  change (Algebra.TensorProduct.comm B A (B ⧸ I))
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I) (Ideal.Quotient.mk _ a)) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, Algebra.TensorProduct.comm_tmul]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.ChartQuotAppLE

open AlgebraicGeometry.Scheme.TwoAffineOpenCover.ChartQuotAppLE in
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover _root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero.AlgebraicGeometry.Scheme.TwoAffineOpenCover in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥) :
    let 𝒱B := 𝒱.pullback c B
    let cB := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B)
    let 𝒱BI := 𝒱.pullback c (B ⧸ I)
    let cBI := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))
    let σst := RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))
    ∃ (J0 : Ideal (𝒱B.cover cB).A0) (J1 : Ideal (𝒱B.cover cB).A1)
      (J01 : Ideal (𝒱B.cover cB).A01),
      J0 ^ 2 = ⊥ ∧ J1 ^ 2 = ⊥ ∧ J01 ^ 2 = ⊥ ∧
      ∃ (φ0 : (𝒱B.cover cB).A0 ⧸ J0 ≃+* (𝒱BI.cover cBI).A0)
        (φ1 : (𝒱B.cover cB).A1 ⧸ J1 ≃+* (𝒱BI.cover cBI).A1)
        (φ01 : (𝒱B.cover cB).A01 ⧸ J01 ≃+* (𝒱BI.cover cBI).A01),
        (∀ a, φ01 ((Ideal.Quotient.mk J01) ((𝒱B.cover cB).ρ0 a)) =
          (𝒱BI.cover cBI).ρ0 (φ0 ((Ideal.Quotient.mk J0) a))) ∧
        (∀ a, φ01 ((Ideal.Quotient.mk J01) ((𝒱B.cover cB).ρ1 a)) =
          (𝒱BI.cover cBI).ρ1 (φ1 ((Ideal.Quotient.mk J1) a))) ∧
        (∀ a, φ0 ((Ideal.Quotient.mk J0) a) =
          (σst.appLE 𝒱B.U0 𝒱BI.U0
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a) ∧
        (∀ a, φ1 ((Ideal.Quotient.mk J1) a) =
          (σst.appLE 𝒱B.U1 𝒱BI.U1
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a) ∧
        (∀ a, φ01 ((Ideal.Quotient.mk J01) a) =
          (σst.appLE (𝒱B.U0 ⊓ 𝒱B.U1) (𝒱BI.U0 ⊓ 𝒱BI.U1)
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a) := by
  intro 𝒱B cB 𝒱BI cBI σst
  obtain ⟨eR0, eR1, eR01, heR0, heR1, heR01⟩ :=
    exists_stage_baseChangeIsos_structureSheaf 𝒱 c B (B ⧸ I)

  have hmk0 : ∀ a : (𝒱B.cover cB).A0,
      ((quotMapEquiv I (𝒱B.cover cB).A0).trans eR0.toRingEquiv)
        (Ideal.Quotient.mk _ a)
      = (σst.appLE 𝒱B.U0 𝒱BI.U0
          (baseChangeSnd_preimage_U0 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a :=
    fun a => by rw [RingEquiv.trans_apply, quotMapEquiv_mk]; exact heR0 a
  have hmk1 : ∀ a : (𝒱B.cover cB).A1,
      ((quotMapEquiv I (𝒱B.cover cB).A1).trans eR1.toRingEquiv)
        (Ideal.Quotient.mk _ a)
      = (σst.appLE 𝒱B.U1 𝒱BI.U1
          (baseChangeSnd_preimage_U1 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a :=
    fun a => by rw [RingEquiv.trans_apply, quotMapEquiv_mk]; exact heR1 a
  have hmk01 : ∀ a : (𝒱B.cover cB).A01,
      ((quotMapEquiv I (𝒱B.cover cB).A01).trans eR01.toRingEquiv)
        (Ideal.Quotient.mk _ a)
      = (σst.appLE (𝒱B.U0 ⊓ 𝒱B.U1) (𝒱BI.U0 ⊓ 𝒱BI.U1)
          (baseChangeSnd_preimage_inf 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a :=
    fun a => by rw [RingEquiv.trans_apply, quotMapEquiv_mk]; exact heR01 a
  refine ⟨I.map (algebraMap B (𝒱B.cover cB).A0),
          I.map (algebraMap B (𝒱B.cover cB).A1),
          I.map (algebraMap B (𝒱B.cover cB).A01),
          by rw [← Ideal.map_pow, hI, Ideal.map_bot],
          by rw [← Ideal.map_pow, hI, Ideal.map_bot],
          by rw [← Ideal.map_pow, hI, Ideal.map_bot],
          (quotMapEquiv I (𝒱B.cover cB).A0).trans eR0.toRingEquiv,
          (quotMapEquiv I (𝒱B.cover cB).A1).trans eR1.toRingEquiv,
          (quotMapEquiv I (𝒱B.cover cB).A01).trans eR01.toRingEquiv,
          fun a => ?_, fun a => ?_, hmk0, hmk1, hmk01⟩
  ·
    rw [hmk01, hmk0, cover_ρ0_apply, cover_ρ0_apply,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  ·
    rw [hmk01, hmk1, cover_ρ1_apply, cover_ρ1_apply,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

end
end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero (solution)
