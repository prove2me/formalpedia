-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:03:21.947207+00:00
-- url     : https://prove2.me/theorems/c1f4943c-b3d6-49a0-b90e-0c1df245556a
-- title:
--   LPSOriginal Full Meromorphic Function Field
-- statement:
--   Definitions and structural lemmas for LPSOriginal Full Meromorphic Function Field, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFullMeromorphicFunctionField.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Mathlib.FieldTheory.PrimitiveElement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFullMeromorphic_bounded_annihilator
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finrank_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedToFullMeromorphic_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integral

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalFullMeromorphicJN
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    lpsOriginalFilledMeromorphicRestrictionSubfield N hN :=
  lpsOriginalFilledMeromorphicRestriction N hN (lpsOriginalFilledJDilated N hpos)
    (lpsOriginalFilledChartMeromorphic_jN N hpos hN)
lemma lpsOriginalFullMeromorphic_integral
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
    ∀ x : lpsOriginalFilledMeromorphicRestrictionSubfield N hN,
      IsIntegral (FractionRing (Polynomial ℂ)) x := by
  let := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
  intro x
  obtain ⟨P,hP,hd,he⟩ := lpsOriginalFullMeromorphic_bounded_annihilator N hN x
  exact ⟨P,hP,he⟩
lemma lpsOriginalFullMeromorphic_minpoly_degree_bound
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
    ∀ x : lpsOriginalFilledMeromorphicRestrictionSubfield N hN,
      (minpoly (FractionRing (Polynomial ℂ)) x).natDegree ≤
        Nat.card (LPSOriginalMeromorphicCosets N) := by
  let := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
  intro x
  obtain ⟨P,hP,hd,he⟩ := lpsOriginalFullMeromorphic_bounded_annihilator N hN x
  exact (Polynomial.natDegree_le_of_dvd
    (minpoly.dvd (FractionRing (Polynomial ℂ)) x he) hP.ne_zero).trans hd
lemma lpsOriginalFullMeromorphicJN_minpoly
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    letI := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
    minpoly (FractionRing (Polynomial ℂ)) (lpsOriginalFullMeromorphicJN N hpos hN) =
      minpoly (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hpos) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
  let := (lpsOriginalHolomorphicFractionToMeromorphicGerm.comp
    lpsOriginalJFractionEmbedding).toAlgebra
  let f : LPSOriginalHolomorphicFractionField →ₐ[FractionRing (Polynomial ℂ)]
      LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet :=
    { lpsOriginalHolomorphicFractionToMeromorphicGerm with commutes' _ := rfl }
  let g : lpsOriginalFilledMeromorphicRestrictionSubfield N hN →ₐ[FractionRing (Polynomial ℂ)]
      LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet :=
    { (lpsOriginalFilledMeromorphicRestrictionSubfield N hN).subtype with commutes' _ := rfl }
  have hx : g (lpsOriginalFullMeromorphicJN N hpos hN) =
      f (lpsOriginalJNInFractionField N hpos) := by
    rw [show f (lpsOriginalJNInFractionField N hpos) =
      lpsOriginalHolomorphicToMeromorphicGerm (lpsOriginalJNHolomorphic N hpos) from
        lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic _]
    exact lpsOriginalFilledMeromorphicRestriction_jN N hpos hN
  have hf := minpoly.algHom_eq f f.injective (lpsOriginalJNInFractionField N hpos)
  have hg := minpoly.algHom_eq g g.injective (lpsOriginalFullMeromorphicJN N hpos hN)
  rw [hx] at hg
  exact hg.symm.trans hf
lemma lpsOriginalFullMeromorphicJN_finrank
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
    Module.finrank (FractionRing (Polynomial ℂ))
      (IntermediateField.adjoin (FractionRing (Polynomial ℂ))
        {lpsOriginalFullMeromorphicJN N hpos hN}) =
      Nat.card (LPSOriginalMeromorphicCosets N) := by
  let := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
  let := lpsOriginalJFractionEmbedding.toAlgebra
  rw [IntermediateField.adjoin.finrank
    (lpsOriginalFullMeromorphic_integral N hN (lpsOriginalFullMeromorphicJN N hpos hN)),
    lpsOriginalFullMeromorphicJN_minpoly N hpos hN,
    ←IntermediateField.adjoin.finrank (lpsOriginalJNInFractionField_integral N hpos)]
  exact lpsOriginalGeneratedFunctionField_finrank_eq N hpos
lemma lpsOriginalFullMeromorphic_adjoinJN_eq_top
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
    IntermediateField.adjoin (FractionRing (Polynomial ℂ))
      {lpsOriginalFullMeromorphicJN N hpos hN} = ⊤ := by
  let := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
  let K := FractionRing (Polynomial ℂ)
  let E := lpsOriginalFilledMeromorphicRestrictionSubfield N hN
  let α : E := lpsOriginalFullMeromorphicJN N hpos hN
  apply top_unique
  intro x hx
  let H := IntermediateField.adjoin K ({α,x} : Set E)
  let := IntermediateField.finiteDimensional_adjoin_pair
    (lpsOriginalFullMeromorphic_integral N hN α)
    (lpsOriginalFullMeromorphic_integral N hN x)
  obtain ⟨y,hy⟩ := Field.exists_primitive_element K H
  have hm : minpoly K (y : E) = minpoly K y :=
    minpoly.algHom_eq H.val H.val.injective y
  have hr := (Field.primitive_element_iff_minpoly_natDegree_eq K y).mp hy
  have hb : Module.finrank K H ≤ Nat.card (LPSOriginalMeromorphicCosets N) := by
    rw [←hr,←hm]
    exact lpsOriginalFullMeromorphic_minpoly_degree_bound N hN (y : E)
  have hle : IntermediateField.adjoin K ({α} : Set E) ≤ H := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact IntermediateField.mem_adjoin_pair_left K α x
  have he : IntermediateField.adjoin K ({α} : Set E) = H :=
    IntermediateField.eq_of_le_of_finrank_le hle (by
      rw [lpsOriginalFullMeromorphicJN_finrank N hpos hN]
      exact hb)
  rw [he]
  exact IntermediateField.mem_adjoin_pair_right K α x
lemma lpsOriginalGeneratedToFullMeromorphic_surjective
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    Function.Surjective (lpsOriginalGeneratedToFullMeromorphic N hpos hN) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
  let f := lpsOriginalGeneratedToFullMeromorphic N hpos hN
  have hb : Set.range (algebraMap (FractionRing (Polynomial ℂ))
      (lpsOriginalFilledMeromorphicRestrictionSubfield N hN)) ⊆ f.fieldRange := by
    rintro x ⟨r,rfl⟩
    apply RingHom.mem_fieldRange.mpr
    refine ⟨algebraMap (FractionRing (Polynomial ℂ))
      (lpsOriginalGeneratedFunctionField N hpos) r,?_⟩
    apply Subtype.ext
    rfl
  have hj : ({lpsOriginalFullMeromorphicJN N hpos hN} :
      Set (lpsOriginalFilledMeromorphicRestrictionSubfield N hN)) ⊆ f.fieldRange := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    apply RingHom.mem_fieldRange.mpr
    let y : lpsOriginalGeneratedFunctionField N hpos :=
      ⟨lpsOriginalJNInFractionField N hpos,
        IntermediateField.subset_adjoin (FractionRing (Polynomial ℂ))
          {lpsOriginalJNInFractionField N hpos} (Set.mem_singleton _)⟩
    refine ⟨y,?_⟩
    apply Subtype.ext
    change lpsOriginalHolomorphicFractionToMeromorphicGerm
      (lpsOriginalJNInFractionField N hpos) =
        (lpsOriginalFullMeromorphicJN N hpos hN).val
    rw [lpsOriginalJNInFractionField,
      lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic]
    exact (lpsOriginalFilledMeromorphicRestriction_jN N hpos hN).symm
  have ht := IntermediateField.adjoin_le_subfield
    (F := FractionRing (Polynomial ℂ))
    (S := {lpsOriginalFullMeromorphicJN N hpos hN}) hb hj
  intro x
  apply RingHom.mem_fieldRange.mp
  apply ht
  rw [lpsOriginalFullMeromorphic_adjoinJN_eq_top N hpos hN]
  trivial
def lpsOriginalGeneratedFullMeromorphicEquiv
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    lpsOriginalGeneratedFunctionField N hpos ≃+*
      lpsOriginalFilledMeromorphicRestrictionSubfield N hN := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  exact RingEquiv.ofBijective (lpsOriginalGeneratedToFullMeromorphic N hpos hN)
    ⟨lpsOriginalGeneratedToFullMeromorphic_injective N hpos hN,
      lpsOriginalGeneratedToFullMeromorphic_surjective N hpos hN⟩
end
end QEC.Coding.TannerLiftedProduct


