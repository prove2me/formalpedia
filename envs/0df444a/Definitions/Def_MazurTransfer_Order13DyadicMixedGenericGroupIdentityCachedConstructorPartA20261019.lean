-- Prove2me | Definitions.Def_MazurTransfer_Order13DyadicMixedGenericGroupIdentityCachedConstructorPartA20261019
-- name    : MazurTransfer_Order13DyadicMixedGenericGroupIdentityCachedConstructorPartA20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T09:46:19.713003+00:00
-- url     : https://prove2.me/theorems/037d2a8d-0a2b-4725-874d-6082425d6cf6
-- title:
--   Original generic norm group laws: Order13DyadicMixedGenericGroupIdentity
-- statement:
--   For the same chosen dyadic Picard scheme and its same rational generic fibre, preserve the original represented and base-changed group laws, designated zero, and transported norm endomorphisms. This constructor interface retains the original scoped group structures and their original unit or multiplication compatibility certificates. Every original complete type and whole nonproof value is checked independently. Named downstream consumer: the original integral norm unit and multiplication laws, norm composition and finite etale norm fibres. This is a cached part of the original interface, with no additional owned theorem credit.
-- source:
--   MazurTheorem by Vas and contributors; complete original generic norm group-law modules, preserving Apache-2.0 headers. Reuses the exact official Anthropic FLT rigidity and base-change interface at pin 6e837e75355538c7f80bab5b956861e86c4eacc2.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: The same chosen dyadic Picard generic fibre has its original represented and base-changed relative laws, the same zero and multiplication, and the transported rational group endomorphisms preserve that same law.
Named downstream consumer: Original integral norm units, multiplication and scalar composition.
Original per-file headers and attribution are retained below.
-/
import Definitions.Def_MazurTransfer_Order13DyadicOriginalPicardGeometryAndUniqueNormExtensionsData20261019
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME dyadic Picard group's generic law and the
canonically represented rational law have the SAME designated zero.
Named downstream consumer: abelian rigidity and actual dyadic integral
norm group laws. Adapts the checked good-prime group-identity proof.
-/

noncomputable section
namespace MazurTransfer.Order13DyadicMixedGenericGroupIdentity
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13DyadicMixedQuadraticCharts Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedRationalPicardComparison Order13DyadicMixedPicardGeometry
open Order13ActualPicardDiamondSchemeEndomorphism PicardCanonicalRepresentationGroupIsomorphism
local instance instFactPrimeOfNatNat_order13DyadicMixedGenericGroupIdentity : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev genericRepresentationGroup :
    RepresentsRelSubPic (curveToBase ℚ) infinitySection
      (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition
      (rationalPicard) := rationalRepresentation

def genericRepresentedLaw := (genericRepresentationGroup).relativeGroupLaw
def genericLocalLaw := (dyadicLaw).genericFibre ℚ

theorem localLaw_zero :
    ((dyadicLaw).one (𝟙 _)).val = (dyadicPicard).zeroSection :=
  (show RepresentsRelSubPic (Order13MixedQuadraticGluedCurve.curveToBase BaseRing) Order13DyadicMixedQuadraticPicardGeometryInputs.zeroSection
    (algEquivZeroGroupCut (Order13MixedQuadraticGluedCurve.curveToBase BaseRing)
      Order13DyadicMixedQuadraticPicardGeometryInputs.zeroSection).toSubPicCondition (dyadicPicard)
      from dyadicRepresentation).relativeGroupLaw_one

theorem genericRepresentedLaw_zero :
    ((genericRepresentedLaw).one (𝟙 _)).val =
      (rationalPicard).zeroSection :=
  (genericRepresentationGroup).relativeGroupLaw_one

theorem genericLocalLaw_zero :
    ((genericLocalLaw).one (𝟙 _)).val =
      (rationalPicard).zeroSection := by
  unfold genericLocalLaw
  rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    change ((dyadicLaw).one (𝟙 _ ≫ specGenericFibreInclusion BaseRing ℚ)).val =
      (rationalPicard).zeroSection ≫
        pullback.fst (dyadicPicard).toBase (specGenericFibreInclusion BaseRing ℚ)
    have hz : (rationalPicard).zeroSection ≫
        pullback.fst (dyadicPicard).toBase (specGenericFibreInclusion BaseRing ℚ) =
        specGenericFibreInclusion BaseRing ℚ ≫ (dyadicPicard).zeroSection :=
      RelativePic0Designation.baseChange_zeroSection_fst (dyadicPicard) ℚ
    rw [hz]
    have h := congrArg Subtype.val ((dyadicLaw).one_natural
      (𝟙 _) (𝟙 _ ≫ specGenericFibreInclusion BaseRing ℚ)
      (𝟙 _ ≫ specGenericFibreInclusion BaseRing ℚ) (by simp))
    change (𝟙 _ ≫ specGenericFibreInclusion BaseRing ℚ) ≫
      ((dyadicLaw).one (𝟙 _)).val =
        ((dyadicLaw).one (𝟙 _ ≫ specGenericFibreInclusion BaseRing ℚ)).val at h
    rw [localLaw_zero] at h
    exact h.symm.trans (by rw [Category.id_comp])
  · rw [pullback.lift_snd]
    exact (rationalPicard).zeroSection_toBase.symm

theorem generic_group_law_units_equal :
    (genericLocalLaw).one (𝟙 _) =
      (genericRepresentedLaw).one (𝟙 _) := by
  apply Subtype.ext
  exact (genericLocalLaw_zero).trans (genericRepresentedLaw_zero).symm

theorem genericPicard_geometry :
    Smooth (rationalPicard).toBase ∧ IsProper (rationalPicard).toBase ∧
      GeometricallyConnected (rationalPicard).toBase :=
  rationalPicard_geometry

theorem genericPicard_abelian :
    AbelianSchemePropertyBundle ℚ (rationalPicard).toBase := by
  obtain ⟨hs, hp, hg⟩ := genericPicard_geometry
  letI := hg
  exact ⟨hs, hp, fun s => (rationalPicard).toBase.isConnected_preimage_singleton s,
    ⟨genericRepresentedLaw⟩⟩

theorem actualLocalGenericOverIso_zero :
    actualPicard.zeroSection ≫ (actualDyadicRationalOverIso).hom.left =
      (rationalPicard).zeroSection :=
  canonicalSchemeIso_zero (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
    actualRepresentation (rationalRepresentation)


end MazurTransfer.Order13DyadicMixedGenericGroupIdentity
#print axioms MazurTransfer.Order13DyadicMixedGenericGroupIdentity.generic_group_law_units_equal
#print axioms MazurTransfer.Order13DyadicMixedGenericGroupIdentity.genericPicard_abelian

end


