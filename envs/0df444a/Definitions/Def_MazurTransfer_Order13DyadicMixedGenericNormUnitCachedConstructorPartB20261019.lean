-- Prove2me | Definitions.Def_MazurTransfer_Order13DyadicMixedGenericNormUnitCachedConstructorPartB20261019
-- name    : MazurTransfer_Order13DyadicMixedGenericNormUnitCachedConstructorPartB20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T09:48:47.712326+00:00
-- url     : https://prove2.me/theorems/707f01c9-8787-434f-83de-462bf90e83b9
-- title:
--   Original generic norm group laws: Order13DyadicMixedGenericNormUnit
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
import Definitions.Def_MazurTransfer_Order13DyadicMixedGenericGroupIdentityCachedConstructorPartA20261019

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the following checked good-prime proof is adapted to the
SAME selected actual dyadic Picard, its represented group law and actual
rational norm maps. No unit assumption on two or 104 is added.
Named downstream consumer: finite etale dyadic norm fibres and their
arithmetic inertia/Kummer condition. Original method and attribution follow.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the already transported actual norm morphisms preserve
zero for the generic fibre of the SAME local integral group law.
Named downstream consumer: field rigidity and integral norm group laws.
-/

noncomputable section
namespace MazurTransfer.Order13DyadicMixedGenericNormUnit
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedGenericGroupIdentity Order13DyadicMixedRationalPicardComparison
open Order13ActualDyadicMixedPicardNeronModel Order13DyadicMixedQuadraticCharts
open Order13ActualPicardDiamondSchemeEndomorphism Order13DyadicMixedRationalPicardComparison
open Order13ActualPicardSchemeNineteenNorm
open Order13DyadicMixedRationalPicardComparison
open scoped CategoryTheory.MonObj
open Order13DyadicMixedGenericNorms Order13DyadicMixedPicardGeometry
local instance instFactPrimeOfNatNat_order13DyadicMixedGenericNormUnit : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedGenericNormUnit : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance instGrpObjOverSchemeSpecOfRatMkToBaseRationalPicard_order13DyadicMixedGenericNormUnit : GrpObj (Over.mk (rationalPicard).toBase) :=
  (genericRepresentationGroup).grpObj

theorem genericPicard_connected : ConnectedSpace (rationalPicard).P := by
  letI := (genericPicard_geometry).2.2
  exact GeometricallyConnected.connectedSpace_of_subsingleton
    (f := (rationalPicard).toBase)

theorem localGenericNorm_isMonHom
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] :
    IsMonHom ((actualDyadicRationalOverIso).inv ≫ φ ≫
      (actualDyadicRationalOverIso).hom) := by
  letI := actualDyadicRationalOverIso_isMonHom
  infer_instance

theorem localGenericNorm_preserves_unit
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] :
    NeronModelInfra.schemeHomOverComp ((genericLocalLaw).one (𝟙 _))
      (genericNorm φ) = (genericLocalLaw).one (𝟙 _) := by
  letI := localGenericNorm_isMonHom φ
  have h := congrArg (fun f : Over.mk (𝟙 (Spec (CommRingCat.of ℚ))) ⟶
    Over.mk (rationalPicard).toBase => f.left)
    (MonObj.one_comp ((actualDyadicRationalOverIso).inv ≫ φ ≫
      (actualDyadicRationalOverIso).hom))
  change ((genericRepresentedLaw).one (𝟙 _)).val ≫
    (genericNorm φ).val = ((genericRepresentedLaw).one (𝟙 _)).val at h
  apply Subtype.ext
  change ((genericLocalLaw).one (𝟙 _)).val ≫
    (genericNorm φ).val = ((genericLocalLaw).one (𝟙 _)).val
  rw [generic_group_law_units_equal]
  exact h

end MazurTransfer.Order13DyadicMixedGenericNormUnit
#print axioms MazurTransfer.Order13DyadicMixedGenericNormUnit.genericPicard_connected
#print axioms MazurTransfer.Order13DyadicMixedGenericNormUnit.localGenericNorm_preserves_unit

end


