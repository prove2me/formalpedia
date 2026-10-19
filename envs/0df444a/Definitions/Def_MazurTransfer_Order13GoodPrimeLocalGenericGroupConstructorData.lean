-- Prove2me | Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
-- name    : MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T04:26:43.408242+00:00
-- url     : https://prove2.me/theorems/f1c676d8-3ad5-4f55-a261-6e682f754469
-- title:
--   Generic group laws and zero sections on the same local Picard model
-- statement:
--   For each prime $q \nmid 104$, retain the group law obtained from the local Picard representation and the generic fibre of the integral group law. Their zero sections are compared with the designated Picard zero section, and the canonical comparison with the original rational Picard scheme preserves zero. The generic Picard scheme is smooth, proper and geometrically connected and has its represented abelian group law.
--
--   This constructor interface supports the separate comparison of the two group laws and the integral multiplication-by-nineteen identities.
-- source:
--   MazurTheorem, Order13GoodPrimeLocalGenericGroupIdentity.lean, complete original declarations (source SHA-256 5c0c699cd69d6ccc6911562bc192066a0478176f2835da167376e0bea205cde2), Apache-2.0. Original declaration types and nonproof values checked in full. Official Anthropic FLT interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the zero section of the SAME local Picard
model's generic group law with the chosen literal Picard representation.
Named downstream consumer: abelian-scheme rigidity, integral norm group
laws and local multiplication by nineteen.
-/
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericPicardComparisonDataNativeABIV3
import Theorems.Thm_MazurTransfer_Order13EveryRepresentedIntegralPicardGeometry_every_represented_integral_picard_geometry
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

noncomputable section
namespace MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections
open Order13GoodPrimeLocalPicardModels Order13LocalIntegralCoefficientMaps
open Order13GoodPrimeLocalGenericPicardComparison
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13SameIntegralPicardRationalSchemeComparison
open PicardCanonicalRepresentationGroupIsomorphism
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)

abbrev genericRepresentationGroup :
    RepresentsRelSubPic (curveToBase ℚ) infinitySection
      (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition
      (localGenericPicard q hq) := localGenericRepresentation q hq

def genericRepresentedLaw := (genericRepresentationGroup q hq).relativeGroupLaw
def genericLocalLaw := (localLaw q hq).genericFibre ℚ

theorem localLaw_zero :
    ((localLaw q hq).one (𝟙 _)).val = (localPicard q hq).zeroSection :=
  (show RepresentsRelSubPic (curveToBase (LocalRing q)) (positiveInfinitySection (LocalRing q))
    (algEquivZeroGroupCut (curveToBase (LocalRing q))
      (positiveInfinitySection (LocalRing q))).toSubPicCondition (localPicard q hq)
      from localRepresentation q hq).relativeGroupLaw_one

theorem genericRepresentedLaw_zero :
    ((genericRepresentedLaw q hq).one (𝟙 _)).val =
      (localGenericPicard q hq).zeroSection :=
  (genericRepresentationGroup q hq).relativeGroupLaw_one

theorem genericPicard_geometry :
    Smooth (localGenericPicard q hq).toBase ∧ IsProper (localGenericPicard q hq).toBase ∧
      GeometricallyConnected (localGenericPicard q hq).toBase :=
  Order13EveryRepresentedIntegralPicardGeometry.every_represented_integral_picard_geometry ℚ (by norm_num)
    (localGenericPicard q hq) (localGenericRepresentation q hq)

theorem genericPicard_abelian :
    AbelianSchemePropertyBundle ℚ (localGenericPicard q hq).toBase := by
  obtain ⟨hs, hp, hg⟩ := genericPicard_geometry q hq
  letI := hg
  exact ⟨hs, hp, fun s => (localGenericPicard q hq).toBase.isConnected_preimage_singleton s,
    ⟨genericRepresentedLaw q hq⟩⟩

theorem actualLocalGenericOverIso_zero :
    actualPicard.zeroSection ≫ (actualLocalGenericOverIso q hq).hom.left =
      (localGenericPicard q hq).zeroSection :=
  canonicalSchemeIso_zero (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
    actualRepresentation (localGenericRepresentation q hq)

end MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.genericPicard_abelian
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.actualLocalGenericOverIso_zero

#print axioms MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.genericRepresentationGroup
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.genericRepresentedLaw
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.genericLocalLaw
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.localLaw_zero
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.genericRepresentedLaw_zero
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.genericPicard_geometry
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.genericPicard_abelian
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.actualLocalGenericOverIso_zero


