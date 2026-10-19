-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedOriginalPointedCurveAndLiteralPicardFibreTransportData20261019
-- name    : MazurTransfer_Order13MixedOriginalPointedCurveAndLiteralPicardFibreTransportData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T08:24:02.903995+00:00
-- url     : https://prove2.me/theorems/2078d6b4-261b-4fc2-9f18-df4bfb23b683
-- title:
--   Original pointed curve and literal Picard fibre transport
-- statement:
--   The original pointed mixed/square whole-curve comparison and literal Picard algebra base changes, preserving the chosen representing scheme, original zero section and relative multiplication. Named downstream consumer: the chosen actual dyadic Picard rational-fibre comparison.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pointed whole mixed/square curve comparison and literal Picard fibres preserving relative multiplication.
Named downstream consumer: the chosen actual dyadic Picard family rational-fibre identification and Neron extensions of the actual norm maps.
Original per-file attribution is retained below.
-/
import Definitions.Def_MazurTransfer_Order13MixedOriginalSixMarkedSectionsAndPicardChartSelectionData20261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeRationalCurveComparisonData20261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
import Definitions.Def_MazurTransfer_PointedCurvePicardRepresentationTransport
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_points_mul_poincare_compat

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the two ACTUAL mixed infinity sections with the
previously chosen positive and negative infinity sections under the whole
completing-square isomorphism. Named downstream consumer: compatible Picard
rigidification and the fixed infinity divisor class on the generic fibre.
-/

noncomputable section
namespace MazurTransfer.Order13MixedQuadraticInfinityComparison
open Polynomial CategoryTheory AlgebraicGeometry
open Order13MixedQuadraticSquareComparisonGenerators Order13MixedQuadraticSquareTransitionSquares
open Order13MixedQuadraticWholeCurveComparison Order13MixedQuadraticInfinitySections
universe u
variable (R : Type u) [CommRing R] (c : Polynomial R) (hc : 2 * c = 1)

@[simp] theorem zero_z : infinityPointZero R (Order13MixedQuadraticOverlapCoordinates.zCoordinate R) = 0 := by
  simp only [infinityPointZero, Order13MixedQuadraticOverlapCoordinates.zCoordinate, AdjoinRoot.liftAlgHom_of]
  simp

@[simp] theorem zero_w : infinityPointZero R (Order13MixedQuadraticOverlapCoordinates.wCoordinate R) = 0 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp] theorem negOne_z : infinityPointNegOne R (Order13MixedQuadraticOverlapCoordinates.zCoordinate R) = 0 := by
  simp only [infinityPointNegOne, Order13MixedQuadraticOverlapCoordinates.zCoordinate, AdjoinRoot.liftAlgHom_of]
  simp

@[simp] theorem negOne_w : infinityPointNegOne R (Order13MixedQuadraticOverlapCoordinates.wCoordinate R) = -1 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

def oldInfinityAlgHom (a : R) (ha : a ^ 2 = 1) : MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalRing R →ₐ[R] R where
  __ := Order13IntegralSections.reciprocalInfinityEvaluation R a ha
  commutes' r := DFunLike.congr_fun (Order13IntegralSections.reciprocalInfinityEvaluation_comp_algebraMap R a ha) r

theorem zero_evaluation_comparison :
    (infinityPointZero R).comp (reciprocalEquiv R c hc).toAlgHom =
      oldInfinityAlgHom R 1 (by simp) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change infinityPointZero R (reciprocalEquiv R c hc (MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate R)) =
      Order13IntegralSections.reciprocalInfinityEvaluation R 1 (by simp) (MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate R)
    rw [reciprocalEquiv_z, zero_z, Order13IntegralSections.reciprocalInfinityEvaluation_z]
  · change infinityPointZero R (reciprocalEquiv R c hc (MazurTorsion.XOneThirteenProjectiveCurve.wCoordinate R)) =
      Order13IntegralSections.reciprocalInfinityEvaluation R 1 (by simp) (MazurTorsion.XOneThirteenProjectiveCurve.wCoordinate R)
    rw [reciprocalEquiv_w, Order13IntegralSections.reciprocalInfinityEvaluation_w]
    simp only [map_add, map_mul, map_ofNat, map_one, map_pow, zero_z, zero_w]
    ring

theorem negOne_evaluation_comparison :
    (infinityPointNegOne R).comp (reciprocalEquiv R c hc).toAlgHom =
      oldInfinityAlgHom R (-1) (by simp) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change infinityPointNegOne R (reciprocalEquiv R c hc (MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate R)) =
      Order13IntegralSections.reciprocalInfinityEvaluation R (-1) (by simp) (MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate R)
    rw [reciprocalEquiv_z, negOne_z, Order13IntegralSections.reciprocalInfinityEvaluation_z]
  · change infinityPointNegOne R (reciprocalEquiv R c hc (MazurTorsion.XOneThirteenProjectiveCurve.wCoordinate R)) =
      Order13IntegralSections.reciprocalInfinityEvaluation R (-1) (by simp) (MazurTorsion.XOneThirteenProjectiveCurve.wCoordinate R)
    rw [reciprocalEquiv_w, Order13IntegralSections.reciprocalInfinityEvaluation_w]
    simp only [map_add, map_mul, map_ofNat, map_one, map_pow, negOne_z, negOne_w]
    ring

private theorem compose_chart_point {S A B X Y : Scheme.{u}}
    (t : S ⟶ A) (v : S ⟶ B) (e : A ⟶ B) (a : A ⟶ X) (b : B ⟶ Y) (f : X ⟶ Y)
    (h : a ≫ f = e ≫ b) (k : t ≫ e = v) : (t ≫ a) ≫ f = v ≫ b := by
  rw [Category.assoc, h, ← Category.assoc, k]

theorem infinitySectionZero_comparison :
    infinitySectionZero R ≫ (wholeCurveIso R c hc).hom =
      Order13IntegralSections.infinityMorphism R 1 (by simp) := by
  let t : Spec (.of R) ⟶ Order13DyadicMixedQuadraticCharts.reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (infinityPointZero R).toRingHom)
  let v : Spec (.of R) ⟶ MazurTorsion.XOneThirteenProjectiveCurve.reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (Order13IntegralSections.reciprocalInfinityEvaluation R 1 (by simp)))
  have ht : t ≫ (reciprocalIso R c hc).hom = v := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (zero_evaluation_comparison R c hc)
  exact compose_chart_point t v (reciprocalIso R c hc).hom _ _ _ (reciprocal_forward R c hc) ht

theorem infinitySectionNegOne_comparison :
    infinitySectionNegOne R ≫ (wholeCurveIso R c hc).hom =
      Order13IntegralSections.infinityMorphism R (-1) (by simp) := by
  let t : Spec (.of R) ⟶ Order13DyadicMixedQuadraticCharts.reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (infinityPointNegOne R).toRingHom)
  let v : Spec (.of R) ⟶ MazurTorsion.XOneThirteenProjectiveCurve.reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (Order13IntegralSections.reciprocalInfinityEvaluation R (-1) (by simp)))
  have ht : t ≫ (reciprocalIso R c hc).hom = v := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (negOne_evaluation_comparison R c hc)
  exact compose_chart_point t v (reciprocalIso R c hc).hom _ _ _ (reciprocal_forward R c hc) ht

end MazurTransfer.Order13MixedQuadraticInfinityComparison
#print axioms MazurTransfer.Order13MixedQuadraticInfinityComparison.infinitySectionZero_comparison
#print axioms MazurTransfer.Order13MixedQuadraticInfinityComparison.infinitySectionNegOne_comparison

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the evaluation and section naturality argument of
Order13IntegralInfinitySectionsBaseChange to the actual mixed equations.
Design boundary: both literal mixed infinity sections commute with arbitrary
scalar extension. Named downstream consumer: the pointed dyadic generic
fibre and compatible Picard rigidification.
-/

noncomputable section
namespace MazurTransfer.Order13MixedQuadraticInfinitySectionsBaseChange
open Polynomial CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedQuadraticInfinitySections Order13MixedQuadraticInfinityComparison
open Order13MixedQuadraticCoefficientBaseChange Order13MixedQuadraticActualCurveBaseChange
open Order13MixedQuadraticOverlapCoordinates
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem zero_evaluation_natural :
    (infinityPointZero S).toRingHom.comp (reciprocalRingMap R S) =
      (algebraMap R S).comp (infinityPointZero R).toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      change infinityPointZero S (reciprocalRingMap R S (algebraMap R (reciprocalCoordinateRing R) r)) =
        algebraMap R S (infinityPointZero R (algebraMap R (reciprocalCoordinateRing R) r))
      rw [reciprocalRingMap_algebraMap, (infinityPointZero S).commutes, (infinityPointZero R).commutes]
      simp
    · change infinityPointZero S (reciprocalRingMap R S (zCoordinate R)) =
        algebraMap R S (infinityPointZero R (zCoordinate R))
      rw [reciprocalRingMap_z, zero_z, zero_z, map_zero]
  · change infinityPointZero S (reciprocalRingMap R S (wCoordinate R)) =
      algebraMap R S (infinityPointZero R (wCoordinate R))
    rw [reciprocalRingMap_w, zero_w, zero_w, map_zero]

theorem negOne_evaluation_natural :
    (infinityPointNegOne S).toRingHom.comp (reciprocalRingMap R S) =
      (algebraMap R S).comp (infinityPointNegOne R).toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      change infinityPointNegOne S (reciprocalRingMap R S (algebraMap R (reciprocalCoordinateRing R) r)) =
        algebraMap R S (infinityPointNegOne R (algebraMap R (reciprocalCoordinateRing R) r))
      rw [reciprocalRingMap_algebraMap, (infinityPointNegOne S).commutes, (infinityPointNegOne R).commutes]
      simp
    · change infinityPointNegOne S (reciprocalRingMap R S (zCoordinate R)) =
        algebraMap R S (infinityPointNegOne R (zCoordinate R))
      rw [reciprocalRingMap_z, negOne_z, negOne_z, map_zero]
  · change infinityPointNegOne S (reciprocalRingMap R S (wCoordinate R)) =
      algebraMap R S (infinityPointNegOne R (wCoordinate R))
    rw [reciprocalRingMap_w, negOne_w, negOne_w, map_neg, map_one]

private theorem section_natural {A B C D X Y : Scheme.{u}}
    (t : A ⟶ B) (s : A ⟶ C) (v : C ⟶ D) (e : B ⟶ D)
    (a : B ⟶ X) (b : D ⟶ Y) (f : X ⟶ Y)
    (h : a ≫ f = e ≫ b) (k : t ≫ e = s ≫ v) :
    (t ≫ a) ≫ f = s ≫ (v ≫ b) := by
  rw [Category.assoc, h, ← Category.assoc, k, Category.assoc]

theorem infinitySectionZero_curveMap :
    infinitySectionZero S ≫ curveMap R S =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ infinitySectionZero R := by
  let t : Spec (.of S) ⟶ reciprocalScheme S := Spec.map (CommRingCat.ofHom (infinityPointZero S).toRingHom)
  let v : Spec (.of R) ⟶ reciprocalScheme R := Spec.map (CommRingCat.ofHom (infinityPointZero R).toRingHom)
  let e : reciprocalScheme S ⟶ reciprocalScheme R := Spec.map (CommRingCat.ofHom (reciprocalRingMap R S))
  have ht : t ≫ e = Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ v := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (zero_evaluation_natural R S))
  exact section_natural t _ v e _ _ _ (reciprocalChartMap_curveMap R S) ht

theorem infinitySectionNegOne_curveMap :
    infinitySectionNegOne S ≫ curveMap R S =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ infinitySectionNegOne R := by
  let t : Spec (.of S) ⟶ reciprocalScheme S := Spec.map (CommRingCat.ofHom (infinityPointNegOne S).toRingHom)
  let v : Spec (.of R) ⟶ reciprocalScheme R := Spec.map (CommRingCat.ofHom (infinityPointNegOne R).toRingHom)
  let e : reciprocalScheme S ⟶ reciprocalScheme R := Spec.map (CommRingCat.ofHom (reciprocalRingMap R S))
  have ht : t ≫ e = Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ v := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (negOne_evaluation_natural R S))
  exact section_natural t _ v e _ _ _ (reciprocalChartMap_curveMap R S) ht

end MazurTransfer.Order13MixedQuadraticInfinitySectionsBaseChange
#print axioms MazurTransfer.Order13MixedQuadraticInfinitySectionsBaseChange.infinitySectionZero_curveMap
#print axioms MazurTransfer.Order13MixedQuadraticInfinitySectionsBaseChange.infinitySectionNegOne_curveMap

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every algebra base change of an actual order-13 Picard
representation represents the Picard functor of the literal new-ring curve,
using the genuine whole-curve isomorphism and positive infinity section.
The representing scheme, structural map and zero section are retained.
Named downstream consumer: the actual dyadic Picard rational-fibre
identification and norm extensions. The original method is adapted to the
SAME literal mixed curve and its positive infinity section.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedIntegralPicardLiteralFibreRepresentations
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian NeronModelInfra
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedIntegralSections Order13MixedQuadraticActualCurveBaseChange CurveIsoPicardRepresentationTransport
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def literalCurveFibreIso : curveScheme S ≅ pullback (curveToBase R) (specMap R S) :=
  (wholeCurve_isPullback R S).isoPullback

theorem literalCurveFibreIso_over :
    (literalCurveFibreIso R S).hom ≫ baseChange R (curveToBase R) S = curveToBase S :=
  (wholeCurve_isPullback R S).isoPullback_hom_snd

theorem literalCurveFibreIso_section :
    (positiveInfinitySection S).val ≫ (literalCurveFibreIso R S).hom =
      (sectionBaseChange S (positiveInfinitySection R)).val := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    change (positiveInfinitySection S).val ≫
      (wholeCurve_isPullback R S).isoPullback.hom ≫ pullback.fst _ _ = _
    rw [(wholeCurve_isPullback R S).isoPullback_hom_fst,sectionBaseChange_coe_fst]
    exact Order13MixedQuadraticInfinitySectionsBaseChange.infinitySectionZero_curveMap R S
  · rw [Category.assoc]
    change (positiveInfinitySection S).val ≫
      ((literalCurveFibreIso R S).hom ≫ baseChange R (curveToBase R) S) = _
    rw [literalCurveFibreIso_over,sectionBaseChange_coe_snd]
    exact (positiveInfinitySection S).property

def literalFibreDesignation (D : RelativePic0Designation R (curveToBase R)) :
    RelativePic0Designation S (curveToBase S) :=
  relabelDesignation (c' := curveToBase S) (D.baseChange S)

theorem literal_fibre_representation
    (D : RelativePic0Designation R (curveToBase R))
    (h : RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroCut (curveToBase R) (positiveInfinitySection R)) D) :
    Nonempty (RepresentsRelSubPic (curveToBase S) (positiveInfinitySection S)
      (algEquivZeroCut (curveToBase S) (positiveInfinitySection S))
      (literalFibreDesignation R S D)) := by
  obtain ⟨hS,_⟩ := exists_representsRelSubPic_baseChange R (curveToBase R)
    (positiveInfinitySection R) D h S
  exact ⟨transportRepresentation (literalCurveFibreIso R S)
    (literalCurveFibreIso_over R S) (literalCurveFibreIso_section R S) (D.baseChange S) hS⟩

end MazurTransfer.Order13MixedIntegralPicardLiteralFibreRepresentations
#print axioms MazurTransfer.Order13MixedIntegralPicardLiteralFibreRepresentations.literal_fibre_representation

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transporting a Picard representation along a pointed curve
isomorphism preserves the canonical relative point multiplication on its
unchanged representing scheme. Named downstream consumer: relative group
compatibility of the actual integral family's arithmetic field fibres.
-/

noncomputable section
universe u
namespace MazurTransfer.MixedOriginalPicardPointMultiplicationTransport20261019
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open CurveHomRigidifiedLineBundlePullback CurveIsoRigidifiedLineBundleTransport
open CurveIsoPicardRepresentationTransport
open scoped CategoryTheory.MonObj
variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
variable {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
variable {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
variable {ε' : SchemeHomOver (𝟙 (Spec (.of R))) c'}

theorem transport_representation_relative_mul
    (e : C' ≅ C) (he : e.hom ≫ c = c') (hε : ε'.val ≫ e.hom = ε.val)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) (x y : SchemeHomOver t D.toBase) :
    ((show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D from h).relativeGroupLaw.mul t x y).val =
    ((show RepresentsRelSubPic c' ε' (algEquivZeroGroupCut c' ε').toSubPicCondition
        (relabelDesignation (c' := c') D) from transportRepresentation e he hε D h).relativeGroupLaw.mul t x y).val := by
  let hG : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D := h
  let h' := transportRepresentation e he hε D h
  let hG' : RepresentsRelSubPic c' ε' (algEquivZeroGroupCut c' ε').toSubPicCondition
      (relabelDesignation (c' := c') D) := h'
  letI := hG.grpObj
  have i1 : Nonempty ((h.poincare.pullbackAlong (hG.relativeGroupLaw.mul t x y)).L ≅
      ((h.poincare.pullbackAlong x).tensor (h.poincare.pullbackAlong y)).L) :=
    hG.nonempty_poincare_pullbackAlong_mul_iso
      (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
  letI := hG'.grpObj
  have i2 : Nonempty ((h'.poincare.pullbackAlong (hG'.relativeGroupLaw.mul t x y)).L ≅
      ((h'.poincare.pullbackAlong x).tensor (h'.poincare.pullbackAlong y)).L) :=
    hG'.nonempty_poincare_pullbackAlong_mul_iso
      (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
  have hi : (h'.poincare.pullbackAlong (hG.relativeGroupLaw.mul t x y)).L ≅
      (h'.poincare.pullbackAlong (hG'.relativeGroupLaw.mul t x y)).L :=
    (forward_pullbackAlong_iso e he hε (hG.relativeGroupLaw.mul t x y) h.poincare).symm ≪≫
      pullbackRigidified_congr e.hom he hε i1.some ≪≫
      Scheme.Modules.pullbackTensorObjIso (curvePullback e.hom he t) _ _ ≪≫
      (forward_pullbackAlong_iso e he hε x h.poincare ⊗ᵢ
        forward_pullbackAlong_iso e he hε y h.poincare) ≪≫ i2.some.symm
  exact congrArg Subtype.val (h'.ext_of_iso t _ _ ⟨hi⟩)

end MazurTransfer.MixedOriginalPicardPointMultiplicationTransport20261019
#print axioms MazurTransfer.MixedOriginalPicardPointMultiplicationTransport20261019.transport_representation_relative_mul

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal curve fibres retain the original integral Picard
family's relative multiplication, via its genuine base-change representation
and pointed whole-curve isomorphism. Named downstream consumer: the SAME dyadic family's arithmetic rational
fibre and its actual norm extensions. Adapts the checked square-model method.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedIntegralPicardLiteralFibreRelativeGroupCompatibility
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.SmoothProperCurve
open Order13MixedQuadraticGluedCurve Order13MixedIntegralSections
open Order13MixedIntegralPicardLiteralFibreRepresentations CurveIsoPicardRepresentationTransport
open MixedOriginalPicardPointMultiplicationTransport20261019
open scoped CategoryTheory.MonObj

theorem literal_fibre_relative_group_compatibility
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (D : RelativePic0Designation R (curveToBase R))
    (h : RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroCut (curveToBase R) (positiveInfinitySection R)) D) :
    ∃ hS : RepresentsRelSubPic (curveToBase S) (positiveInfinitySection S)
      (algEquivZeroCut (curveToBase S) (positiveInfinitySection S))
      (literalFibreDesignation R S D),
      letI := (show RepresentsRelSubPic (curveToBase S) (positiveInfinitySection S)
        (algEquivZeroGroupCut (curveToBase S) (positiveInfinitySection S)).toSubPicCondition
          (literalFibreDesignation R S D) from hS).grpObj
      ∃ Θ : (Over.mk (𝟙 (Spec (.of S))) ⟶ Over.mk (literalFibreDesignation R S D).toBase) ≃
          SchemeHomOver (specMap R S) D.toBase,
        (∀ a, (Θ a).val = a.left ≫ pullback.fst D.toBase (specMap R S)) ∧
        ∀ a b, Θ (a * b) =
          (show RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
            (algEquivZeroGroupCut (curveToBase R) (positiveInfinitySection R)).toSubPicCondition
              D from h).relativeGroupLaw.mul (specMap R S) (Θ a) (Θ b) := by
  obtain ⟨hB,hP⟩ := exists_representsRelSubPic_baseChange R (curveToBase R)
    (positiveInfinitySection R) D h S
  let hBG : RepresentsRelSubPic (baseChange R (curveToBase R) S)
      (sectionBaseChange S (positiveInfinitySection R))
      (algEquivZeroGroupCut (baseChange R (curveToBase R) S)
        (sectionBaseChange S (positiveInfinitySection R))).toSubPicCondition (D.baseChange S) := hB
  letI := hBG.grpObj
  obtain ⟨Θ,hcoe,hmul,_⟩ := baseChange_points_mul_poincare_compat R (curveToBase R)
    (positiveInfinitySection R) D h S hB hP
  have hmul0 : ∀ x y : SchemeHomOver (𝟙 (Spec (.of S))) (D.baseChange S).toBase,
      Θ (schemeHomOverToOverHom (hBG.relativeGroupLaw.mul (𝟙 _) x y)) =
        (show RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
          (algEquivZeroGroupCut (curveToBase R) (positiveInfinitySection R)).toSubPicCondition
            D from h).relativeGroupLaw.mul (specMap R S)
              (Θ (schemeHomOverToOverHom x)) (Θ (schemeHomOverToOverHom y)) := by
    intro x y
    simpa only [RepresentsRelSubPic.relativeGroupLaw,relativeGroupLawOfGrpObj_mul,
      schemeHomOverToOverHom_overHomToSchemeHomOver] using
        hmul (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
  let hS := transportRepresentation (literalCurveFibreIso R S)
    (literalCurveFibreIso_over R S) (literalCurveFibreIso_section R S) (D.baseChange S) hB
  let hSG : RepresentsRelSubPic (curveToBase S) (positiveInfinitySection S)
      (algEquivZeroGroupCut (curveToBase S) (positiveInfinitySection S)).toSubPicCondition
        (literalFibreDesignation R S D) := hS
  refine ⟨hS,?_⟩
  letI := hSG.grpObj
  refine ⟨Θ,hcoe,?_⟩
  intro a b
  have heq : schemeHomOverToOverHom
      (hBG.relativeGroupLaw.mul (𝟙 _) (overHomToSchemeHomOver a)
        (overHomToSchemeHomOver b)) = a * b := by
    apply Over.OverMorphism.ext
    exact transport_representation_relative_mul (literalCurveFibreIso R S)
      (literalCurveFibreIso_over R S) (literalCurveFibreIso_section R S)
      (D.baseChange S) hB (𝟙 _) (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)
  have hm := hmul0 (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)
  rw [heq] at hm
  exact hm

end MazurTransfer.Order13MixedIntegralPicardLiteralFibreRelativeGroupCompatibility
#print axioms MazurTransfer.Order13MixedIntegralPicardLiteralFibreRelativeGroupCompatibility.literal_fibre_relative_group_compatibility

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the inverse rational mixed/square whole-curve isomorphism
is over Q and preserves the exact marked positive infinity sections.
Named downstream consumer: rigidified Picard representation transport for
identifying the SAME dyadic Picard rational fibre with the arithmetic Picard.
-/

noncomputable section
namespace MazurTransfer.Order13DyadicMixedRationalPointedCurveComparison
open CategoryTheory AlgebraicGeometry Polynomial
open Order13MixedQuadraticGluedCurve Order13MixedQuadraticWholeCurveComparisonOverBase

def squareToMixedIso : MazurTorsion.XOneThirteenProjectiveCurve.curveScheme ℚ ≅ curveScheme ℚ :=
  rationalCurveIso.symm

theorem squareToMixedIso_over :
    squareToMixedIso.hom ≫ curveToBase ℚ =
      MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ := by
  rw [← rationalCurveIso_toBase]
  exact rationalCurveIso.inv_hom_id_assoc _

theorem squareToMixedIso_section :
    (Order13IntegralSections.positiveInfinitySection ℚ).val ≫ squareToMixedIso.hom =
      (Order13MixedIntegralSections.positiveInfinitySection ℚ).val := by
  have h : (Order13MixedIntegralSections.positiveInfinitySection ℚ).val ≫
      rationalCurveIso.hom = (Order13IntegralSections.positiveInfinitySection ℚ).val :=
    Order13MixedQuadraticInfinityComparison.infinitySectionZero_comparison ℚ (C ((1 : ℚ) / 2))
      Order13MixedQuadraticRationalChartComparison.rational_two_inverse
  exact (congrArg (fun f : Spec (.of ℚ) ⟶ MazurTorsion.XOneThirteenProjectiveCurve.curveScheme ℚ =>
    f ≫ rationalCurveIso.inv) h.symm).trans (by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])

end MazurTransfer.Order13DyadicMixedRationalPointedCurveComparison
#print axioms MazurTransfer.Order13DyadicMixedRationalPointedCurveComparison.squareToMixedIso_over
#print axioms MazurTransfer.Order13DyadicMixedRationalPointedCurveComparison.squareToMixedIso_section

end


