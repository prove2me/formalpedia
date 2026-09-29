-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_snd_apply_eq_and_notMem_support
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1ae21cd1-2eae-5a11-90d4-0fe7068317a6

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.finite_preimage_singleton SmoothOfRelativeDimension.smooth SmoothOfRelativeDimension IsProper Scheme.Hom Scheme.Hom.range_fiberι GeometricallyIrreducible IsFinite Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Scheme Smooth IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Scheme.IdealSheafData isIntegral_of_irreducibleSpace_of_isReduced RelEffCartierDiv isReduced_of_smooth_over_field"
namespace RelEffCartierDiv
p2m_export "AlgebraicGeometry.RelEffCartierDiv" "I isFinite"
namespace OffSupportSol
p2m_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

theorem main
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {d : ℕ} (D : RelEffCartierDiv c d t) (x : T) :
    ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x ∧ y ∉ D.I.support := by
  classical
  let q := pullback.snd c t

  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have hsm1 : SmoothOfRelativeDimension 1 q := MorphismProperty.pullback_snd c t inferInstance
  have hsm2 : SmoothOfRelativeDimension 1 (q.fiberToSpecResidueField x) :=
    MorphismProperty.pullback_snd q (T.fromSpecResidueField x) hsm1
  have hsmooth : Smooth (q.fiberToSpecResidueField x) := @SmoothOfRelativeDimension.smooth 1 _ _ _ hsm2
  haveI : IsReduced (q.fiber x) := isReduced_of_smooth_over_field hsmooth
  haveI : IrreducibleSpace ↥(q.fiber x) := inferInstance
  haveI : IsIntegral (q.fiber x) := isIntegral_of_irreducibleSpace_of_isReduced _
  have hinf : Infinite ↥(q.fiber x) := by
    have h := @AlgebraicCurve.infinite_setOf_isClosed_singleton _ _ _ (q.fiberToSpecResidueField x) inferInstance hsm2
    haveI := h.to_subtype
    exact Infinite.of_injective (fun z : {y : ↥(q.fiber x) | IsClosed ({y} : Set ↥(q.fiber x))} => (z : ↥(q.fiber x)))
      Subtype.val_injective

  haveI : IsFinite (D.I.subschemeι ≫ q) := D.isFinite
  have hfin : ((D.I.subschemeι ≫ q).base ⁻¹' {x}).Finite := Scheme.Hom.finite_preimage_singleton _ x

  by_contra hcon
  push_neg at hcon
  have hsub : ∀ z : ↥(q.fiber x), ∃ w : ↥(D.I.subscheme), D.I.subschemeι.base w = (q.fiberι x).base z := by
    intro z
    have hx : q.base ((q.fiberι x).base z) = x := by
      have : (q.fiberι x).base z ∈ q.base ⁻¹' {x} := by
        rw [← Scheme.Hom.range_fiberι]; exact ⟨z, rfl⟩
      exact this
    have hmem := hcon _ hx
    have : (q.fiberι x).base z ∈ Set.range D.I.subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hmem
    exact this
  choose w hw using hsub
  have hwS : ∀ z, w z ∈ (D.I.subschemeι ≫ q).base ⁻¹' {x} := by
    intro z
    show q.base (D.I.subschemeι.base (w z)) ∈ ({x} : Set T)
    rw [hw z]
    have : (q.fiberι x).base z ∈ q.base ⁻¹' {x} := by
      rw [← Scheme.Hom.range_fiberι]; exact ⟨z, rfl⟩
    exact this
  haveI : Finite ↥((D.I.subschemeι ≫ q).base ⁻¹' {x}) := hfin.to_subtype
  have hinj : Function.Injective (fun z : ↥(q.fiber x) => (⟨w z, hwS z⟩ : ↥((D.I.subschemeι ≫ q).base ⁻¹' {x}))) := by
    intro z₁ z₂ h12
    have h' : w z₁ = w z₂ := congrArg Subtype.val h12
    have := (hw z₁).symm.trans ((congrArg (fun v => D.I.subschemeι.base v) h') ▸ (hw z₂))
    exact (q.fiberι x).isEmbedding.injective (by rw [← hw z₁, ← hw z₂, h'])
  haveI := Finite.of_injective _ hinj
  exact not_finite ↥(q.fiber x)

end AlgebraicGeometry.RelEffCartierDiv.OffSupportSol

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {d : ℕ} (D : RelEffCartierDiv c d t) (x : T) :
    ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x ∧ y ∉ D.I.support :=
  AlgebraicGeometry.RelEffCartierDiv.OffSupportSol.main c t D x

end S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support (solution)
