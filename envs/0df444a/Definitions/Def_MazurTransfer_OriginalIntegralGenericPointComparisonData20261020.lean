-- Prove2me | Definitions.Def_MazurTransfer_OriginalIntegralGenericPointComparisonData20261020
-- name    : MazurTransfer_OriginalIntegralGenericPointComparisonData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T02:36:57.862642+00:00
-- url     : https://prove2.me/theorems/100275ac-8457-4cfa-94d7-57af298883c4
-- title:
--   Original actual rational-to-integral local Picard point equivalence
-- statement:
--   Retain the original local generic inclusion, both original point maps, their intrinsic inverse certificates and the exact original point equivalence, with both same chosen group structures. All six complete constructor types, four whole point-function values, both original group-provider types and whole values, and every actual original coefficient context are independently checked. Point and norm compatibility are separate theorem interfaces. Named downstream consumer: the actual arithmetic field-point and norm-kernel Galois comparison.
-- source:
--   MazurTheorem Order13IntegralGenericPointComparison by Vas and contributors; complete original point-map and group-provider types and whole values, preserving Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: compare points of the SAME selected integral Picard
with the fixed actual rational Picard on every rational test scheme,
using its actual generic fibre and the retained canonical over-isomorphism.
Retain multiplication, zero, every test-scheme precomposition and the
SAME selected integral extensions of actual rational endomorphisms.
Named downstream consumer: arithmetic Galois comparison of norm kernels.
-/
import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData

noncomputable section
namespace MazurTransfer.Order13IntegralGenericPointComparison
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeLocalGenericPicardComparison Order13GoodPrimeLocalGenericGroupIdentity
open Order13PicardComparisonPublicGroupCompatibility
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralGenericPointComparison : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance instGrpObjOverSchemeSpecOfRatMkToBaseLocalGenericPicard_order13IntegralGenericPointComparison : GrpObj (Over.mk (localGenericPicard q hq).toBase) :=
  (genericRepresentationGroup q hq).grpObj

abbrev localGenericInclusion := specGenericFibreInclusion (LocalRing q) ℚ

def actualToLocal {T : Scheme} {t : T ⟶ Spec (CommRingCat.of ℚ)}
    (a : Over.mk t ⟶ Over.mk actualPicard.toBase) :
    SchemeHomOver (t ≫ localGenericInclusion q) (localPicard q hq).toBase :=
  RelativeGroupLaw.baseChangePointToBase (f := (localPicard q hq).toBase)
    (localGenericInclusion q) (overHomToSchemeHomOver (a ≫ (actualLocalGenericOverIso q hq).hom))

def localToActual {T : Scheme} {t : T ⟶ Spec (CommRingCat.of ℚ)}
    (x : SchemeHomOver (t ≫ localGenericInclusion q) (localPicard q hq).toBase) :
    Over.mk t ⟶ Over.mk actualPicard.toBase :=
  schemeHomOverToOverHom (RelativeGroupLaw.baseChangePointOfBase
    (f := (localPicard q hq).toBase) (localGenericInclusion q) x) ≫
      (actualLocalGenericOverIso q hq).inv

theorem localToActual_actualToLocal {T : Scheme} {t : T ⟶ Spec (CommRingCat.of ℚ)}
    (a : Over.mk t ⟶ Over.mk actualPicard.toBase) :
    localToActual q hq (actualToLocal q hq a) = a := by
  unfold actualToLocal localToActual
  erw [RelativeGroupLaw.baseChangePointOfBase_toBase,
    schemeHomOverToOverHom_overHomToSchemeHomOver, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

theorem actualToLocal_localToActual {T : Scheme} {t : T ⟶ Spec (CommRingCat.of ℚ)}
    (x : SchemeHomOver (t ≫ localGenericInclusion q) (localPicard q hq).toBase) :
    actualToLocal q hq (localToActual q hq x) = x := by
  unfold actualToLocal localToActual
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    overHomToSchemeHomOver_schemeHomOverToOverHom,
    RelativeGroupLaw.baseChangePointToBase_ofBase]

def actualLocalPointEquiv {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ)) :
    (Over.mk t ⟶ Over.mk actualPicard.toBase) ≃
      SchemeHomOver (t ≫ localGenericInclusion q) (localPicard q hq).toBase where
  toFun := actualToLocal q hq
  invFun := localToActual q hq
  left_inv := localToActual_actualToLocal q hq
  right_inv := actualToLocal_localToActual q hq











end MazurTransfer.Order13IntegralGenericPointComparison
#print axioms MazurTransfer.Order13IntegralGenericPointComparison.localGenericInclusion
#print axioms MazurTransfer.Order13IntegralGenericPointComparison.actualToLocal
#print axioms MazurTransfer.Order13IntegralGenericPointComparison.localToActual
#print axioms MazurTransfer.Order13IntegralGenericPointComparison.localToActual_actualToLocal
#print axioms MazurTransfer.Order13IntegralGenericPointComparison.actualToLocal_localToActual
#print axioms MazurTransfer.Order13IntegralGenericPointComparison.actualLocalPointEquiv
#print axioms MazurTransfer.Order13IntegralGenericPointComparison.instGrpObjOverSchemeSpecOfRatMkToBaseLocalGenericPicard_order13IntegralGenericPointComparison
#print axioms MazurTransfer.Order13IntegralGenericPointComparison.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralGenericPointComparison


