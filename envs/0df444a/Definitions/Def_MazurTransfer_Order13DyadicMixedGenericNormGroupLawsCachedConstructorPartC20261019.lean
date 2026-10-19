-- Prove2me | Definitions.Def_MazurTransfer_Order13DyadicMixedGenericNormGroupLawsCachedConstructorPartC20261019
-- name    : MazurTransfer_Order13DyadicMixedGenericNormGroupLawsCachedConstructorPartC20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T09:52:29.815636+00:00
-- url     : https://prove2.me/theorems/a2e1efb7-fd58-4e47-acd0-6b88bb363b9c
-- title:
--   Original generic norm group laws: Order13DyadicMixedGenericNormGroupLaws
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
import Definitions.Def_MazurTransfer_Order13DyadicMixedGenericNormUnitCachedConstructorPartB20261019

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
Design boundary: use the complete pinned FLT abelian rigidity proof to
compare the already chosen group laws and prove that the SAME generic
norm morphisms preserve addition over every test scheme.
Named downstream consumer: descent of integral norm multiplication.
-/

noncomputable section
namespace MazurTransfer.Order13DyadicMixedGenericNormGroupLaws
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedGenericGroupIdentity Order13DyadicMixedRationalPicardComparison
open Order13DyadicMixedGenericNormUnit Order13ActualDyadicMixedPicardNeronModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13DyadicMixedRationalPicardComparison
open scoped CategoryTheory.MonObj
open Order13DyadicMixedGenericNorms Order13DyadicMixedPicardGeometry
local instance instFactPrimeOfNatNat_order13DyadicMixedGenericNormGroupLaws : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedGenericNormGroupLaws : GrpObj (Over.mk actualPicard.toBase) := actualGroup

theorem generic_group_law_multiplications_equal {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ))
    (x y : SchemeHomOver t (rationalPicard).toBase) :
    (genericLocalLaw).mul t x y = (genericRepresentedLaw).mul t x y := by
  letI := (genericPicard_geometry).1
  letI := (genericPicard_geometry).2.1
  letI := genericPicard_connected
  have h := RelativeGroupLaw.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
    ℚ (f := (rationalPicard).toBase) (genericLocalLaw) (genericRepresentedLaw)
    (genericPicard_abelian) (schemeHomOverId (rationalPicard).toBase)
    (by
      apply Subtype.ext
      change ((genericLocalLaw).one (𝟙 _)).val ≫ 𝟙 _ =
        ((genericRepresentedLaw).one (𝟙 _)).val
      rw [Category.comp_id]
      exact congrArg Subtype.val (generic_group_law_units_equal)) t x y
  erw [NeronModelInfra.schemeHomOverComp_id_right,
    NeronModelInfra.schemeHomOverComp_id_right,
    NeronModelInfra.schemeHomOverComp_id_right] at h
  exact h

theorem localGenericNorm_preserves_mul
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (x y : SchemeHomOver t (rationalPicard).toBase) :
    NeronModelInfra.schemeHomOverComp ((genericLocalLaw).mul t x y)
      (genericNorm φ) =
    (genericLocalLaw).mul t
      (NeronModelInfra.schemeHomOverComp x (genericNorm φ))
      (NeronModelInfra.schemeHomOverComp y (genericNorm φ)) := by
  letI := (genericPicard_geometry).1
  letI := (genericPicard_geometry).2.1
  letI := genericPicard_connected
  exact RelativeGroupLaw.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
    ℚ (f := (rationalPicard).toBase) (genericLocalLaw) (genericLocalLaw)
    (genericPicard_abelian) (genericNorm φ)
    (localGenericNorm_preserves_unit φ) t x y

end MazurTransfer.Order13DyadicMixedGenericNormGroupLaws
#print axioms MazurTransfer.Order13DyadicMixedGenericNormGroupLaws.generic_group_law_multiplications_equal
#print axioms MazurTransfer.Order13DyadicMixedGenericNormGroupLaws.localGenericNorm_preserves_mul

end


