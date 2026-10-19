-- Prove2me | Definitions.Def_MazurTransfer_Order13DyadicOriginalGenericNormGroupLawData20261019
-- name    : MazurTransfer_Order13DyadicOriginalGenericNormGroupLawData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T09:56:02.346957+00:00
-- url     : https://prove2.me/theorems/cba31e05-1f1f-43e1-a6bd-71893feeae40
-- title:
--   Original generic norm group laws: stable API from cached original modules
-- statement:
--   For the same chosen dyadic Picard scheme and its same rational generic fibre, preserve the original represented and base-changed group laws, designated zero, and transported norm endomorphisms. This constructor interface retains the original scoped group structures and their original unit or multiplication compatibility certificates. Every original complete type and whole nonproof value is checked independently. Named downstream consumer: the original integral norm unit and multiplication laws, norm composition and finite etale norm fibres. This is a cached part of the original interface, with no additional owned theorem credit.
-- source:
--   MazurTheorem by Vas and contributors; complete original generic norm group-law modules, preserving Apache-2.0 headers. Reuses the exact official Anthropic FLT rigidity and base-change interface at pin 6e837e75355538c7f80bab5b956861e86c4eacc2.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: preserve the original generic norm group-law API using its three independently checked original constructor modules.
Named downstream consumer: original integral norm group laws and composition. The bridge records no additional theorem credit.
-/
import Definitions.Def_MazurTransfer_Order13DyadicMixedGenericNormGroupLawsCachedConstructorPartC20261019
noncomputable section
namespace MazurTransfer.DyadicGenericNormCachedConstructorFacade20261019
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedGenericGroupIdentity Order13DyadicMixedRationalPicardComparison
open Order13DyadicMixedGenericNormUnit Order13ActualDyadicMixedPicardNeronModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13DyadicMixedRationalPicardComparison
open scoped CategoryTheory.MonObj
open Order13DyadicMixedGenericNorms Order13DyadicMixedPicardGeometry
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNormGroupLaws.instFactPrimeOfNatNat_order13DyadicMixedGenericNormGroupLaws
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNormGroupLaws.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedGenericNormGroupLaws

theorem checkedOriginalNormMultiplication
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (x y : SchemeHomOver t (rationalPicard).toBase) :
    NeronModelInfra.schemeHomOverComp ((genericLocalLaw).mul t x y)
      (genericNorm φ) =
    (genericLocalLaw).mul t
      (NeronModelInfra.schemeHomOverComp x (genericNorm φ))
      (NeronModelInfra.schemeHomOverComp y (genericNorm φ)) :=
  MazurTransfer.Order13DyadicMixedGenericNormGroupLaws.localGenericNorm_preserves_mul φ t x y
end MazurTransfer.DyadicGenericNormCachedConstructorFacade20261019
#print axioms MazurTransfer.DyadicGenericNormCachedConstructorFacade20261019.checkedOriginalNormMultiplication
end


