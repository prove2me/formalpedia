-- Prove2me | Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericPicardComparisonDataNativeABIV3
-- name    : MazurTransfer_Order13GoodPrimeLocalGenericPicardComparisonDataNativeABIV3
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T04:22:33.945933+00:00
-- url     : https://prove2.me/theorems/5e8c8c46-6f73-4593-9252-d1212626caa8
-- title:
--   Canonical generic-fibre comparison and transported rational norms
-- statement:
--   For a prime $q \nmid 104$, retain the generic fibre of the selected local Picard model and its representation of the rational curve’s degree-zero Picard functor. The canonical comparison with the original rational Picard scheme is a group-scheme isomorphism. Transport an actual rational endomorphism $\phi$ across this isomorphism to obtain its local generic-fibre endomorphism; in particular this defines the two transported nineteen-norm maps.
--
--   The comparison intertwines each transported map with $\phi$. This is the constructor boundary for extending those specific norm maps to the same integral model.
-- source:
--   MazurTheorem, Order13GoodPrimeLocalGenericPicardComparison.lean, complete original declarations (source SHA-256 88ece9d9e1a3c91f894258bb1d2c9fe9dfb4345734dfaf39ee1528eab92f58a4), Apache-2.0. Original declaration types and nonproof values checked in full. Official Anthropic FLT interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME rational Picard scheme canonically represents
the rational generic fibre of the selected family's local Z_(q) model.
Transfer its actual norm maps along that group scheme isomorphism.
Named downstream consumer: unique local integral extensions of these
specific rational norm maps through the Neron mapping property.
-/
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalPicardModelsData
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData

noncomputable section
namespace MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections
open Order13GoodPrimeLocalPicardModels Order13LocalIntegralCoefficientMaps
open Order13IntegralPicardLiteralFibreRepresentations
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13SameIntegralPicardRationalSchemeComparison
open PicardCanonicalRepresentationGroupIsomorphism
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)

def localGenericPicard := literalFibreDesignation (LocalRing q) ℚ (localPicard q hq)

def localGenericRepresentation : RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroCut (curveToBase ℚ) infinitySection) (localGenericPicard q hq) :=
  (Order13IntegralPicardLiteralFibreRelativeGroupCompatibility.literal_fibre_relative_group_compatibility
    (LocalRing q) ℚ (localPicard q hq) (localRepresentation q hq)).choose

def actualLocalGenericOverIso :
    Over.mk actualPicard.toBase ≅ Over.mk (localGenericPicard q hq).toBase :=
  canonicalOverIso (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
    actualRepresentation (localGenericRepresentation q hq)

local instance localGenericPicardComparisonProvider120261018 : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance localGenericPicardComparisonProvider220261018 : GrpObj (Over.mk (localGenericPicard q hq).toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition
      (localGenericPicard q hq) from localGenericRepresentation q hq).grpObj

theorem actualLocalGenericOverIso_isMonHom :
    IsMonHom (actualLocalGenericOverIso q hq).hom :=
  canonicalOverIso_isMonHom (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
    actualRepresentation (localGenericRepresentation q hq)

def localGenericNorm
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    SchemeHomOver
      (pullback.snd (localPicard q hq).toBase (specGenericFibreInclusion (LocalRing q) ℚ))
      (pullback.snd (localPicard q hq).toBase (specGenericFibreInclusion (LocalRing q) ℚ)) :=
  overHomToSchemeHomOver ((actualLocalGenericOverIso q hq).inv ≫ φ ≫
    (actualLocalGenericOverIso q hq).hom)

theorem localGenericNorm_intertwine
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    (actualLocalGenericOverIso q hq).hom.left ≫ (localGenericNorm q hq φ).val =
      φ.left ≫ (actualLocalGenericOverIso q hq).hom.left := by
  change ((actualLocalGenericOverIso q hq).hom ≫
    (actualLocalGenericOverIso q hq).inv ≫ φ ≫
    (actualLocalGenericOverIso q hq).hom).left = _
  simp only [Iso.hom_inv_id_assoc]
  rfl

def localGenericPi := localGenericNorm q hq schemePi
def localGenericPiConjugate := localGenericNorm q hq schemePiConjugate

end MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison.localGenericRepresentation
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison.actualLocalGenericOverIso_isMonHom
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison.localGenericNorm_intertwine

#print axioms MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison.localGenericPicard
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison.actualLocalGenericOverIso
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison.localGenericNorm
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison.localGenericPi
#print axioms MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison.localGenericPiConjugate


