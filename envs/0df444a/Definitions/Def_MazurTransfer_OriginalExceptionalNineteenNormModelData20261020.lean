-- Prove2me | Definitions.Def_MazurTransfer_OriginalExceptionalNineteenNormModelData20261020
-- name    : MazurTransfer_OriginalExceptionalNineteenNormModelData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T05:48:47.863126+00:00
-- url     : https://prove2.me/theorems/a918c0f4-d287-4f3c-9383-caebce6d3722
-- title:
--   Original exceptional nineteen integral Picard and generic point
-- statement:
--   Retain the original good-prime certificate at nineteen, the same chosen integral Picard designation, the same generic base and its structure map, and the same original actual generic-point map, with the original primality provider. Complete original types, all four whole nonproof values and original coefficient and model contexts are independently checked. Unique extension and finite-flat norm fibres remain separate theorem statements. Named downstream consumer: arithmetic integral norm-kernel Hopf models and Kummer local conditions at nineteen.
-- source:
--   MazurTheorem Order13ExceptionalNineteenFlatNormFibres by Vas and contributors; same original integral model and generic point, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: specialize the SAME actual Picard norm extensions to
Z_(19); extend each generic point uniquely and retain finite-flat,
locally finitely presented, surjective norm preimage families.
Named downstream consumer: exceptional nineteen local Kummer classes.
This proves flat norm models, without asserting a character unit bound.
-/

noncomputable section
namespace MazurTransfer.Order13ExceptionalNineteenFlatNormFibres
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeLocalGenericPicardComparison Order13LocalIntegralCoefficientMaps
open Order13ActualPicardDiamondSchemeEndomorphism

local instance instFactPrimeOfNatNat_order13ExceptionalNineteenFlatNormFibres : Fact (Nat.Prime 19) := ⟨by norm_num⟩
theorem nineteen_good : ¬ (19 : ℤ) ∣ 104 := by norm_num

abbrev integralModel := localPicard 19 nineteen_good
abbrev genericBase := pullback
  (𝟙 (Spec (CommRingCat.of (LocalRing 19))))
  (specGenericFibreInclusion (LocalRing 19) ℚ)
abbrev genericBaseToRationals : genericBase ⟶ Spec (CommRingCat.of ℚ) :=
  pullback.snd _ _

def actualGenericPoint
    (z : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase) :
    SchemeHomOver genericBaseToRationals
      (pullback.snd integralModel.toBase (specGenericFibreInclusion (LocalRing 19) ℚ)) :=
  ⟨genericBaseToRationals ≫ z.val ≫ (actualLocalGenericOverIso 19 nineteen_good).hom.left, by
    change (genericBaseToRationals ≫ z.val ≫
      (actualLocalGenericOverIso 19 nineteen_good).hom.left) ≫
        (localGenericPicard 19 nineteen_good).toBase = genericBaseToRationals
    erw [Category.assoc, Category.assoc, Over.w, z.property, Category.comp_id]⟩





end MazurTransfer.Order13ExceptionalNineteenFlatNormFibres
#print axioms MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.nineteen_good
#print axioms MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.integralModel
#print axioms MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.genericBase
#print axioms MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.genericBaseToRationals
#print axioms MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.actualGenericPoint
#print axioms MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.instFactPrimeOfNatNat_order13ExceptionalNineteenFlatNormFibres


