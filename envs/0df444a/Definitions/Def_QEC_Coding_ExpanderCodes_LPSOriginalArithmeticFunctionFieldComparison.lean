-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:06:10.588282+00:00
-- url     : https://prove2.me/theorems/3b0cdf36-237a-4747-adc9-89689bd03dd5
-- title:
--   LPSOriginal Arithmetic Function Field Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Arithmetic Function Field Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalArithmeticFunctionFieldComparison.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_finiteDimensional
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_finrank_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finiteDimensional
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finrank_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbedding_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integral

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
def lpsOriginalJBaseQToC :
    FractionRing (Polynomial ℚ) →+* FractionRing (Polynomial ℂ) :=
  IsFractionRing.lift
    (g := (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))).comp
      (Polynomial.mapRingHom (algebraMap ℚ ℂ)))
    ((IsFractionRing.injective (Polynomial ℂ) (FractionRing (Polynomial ℂ))).comp
      (Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective))
lemma lpsOriginalJBaseQToC_polynomial (P : Polynomial ℚ) :
    lpsOriginalJBaseQToC (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P) =
      algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))
        (P.map (algebraMap ℚ ℂ)) :=
  IsFractionRing.lift_algebraMap _ P
lemma lpsOriginalJBaseQToC_actualEmbedding :
    lpsOriginalJFractionEmbedding.comp lpsOriginalJBaseQToC =
      lpsOriginalJFractionEmbeddingQ := by
  apply IsFractionRing.ringHom_ext (A := Polynomial ℚ)
  intro P
  change lpsOriginalJFractionEmbedding
    (lpsOriginalJBaseQToC (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P)) =
      lpsOriginalJFractionEmbeddingQ
        (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P)
  rw [lpsOriginalJBaseQToC_polynomial,lpsOriginalJFractionEmbedding_polynomial,
    lpsOriginalJFractionEmbeddingQ_polynomial]
  rfl
lemma lpsOriginalJBaseQToC_actualTower :
    letI := lpsOriginalJBaseQToC.toAlgebra
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    IsScalarTower (FractionRing (Polynomial ℚ)) (FractionRing (Polynomial ℂ))
      LPSOriginalHolomorphicFractionField := by
  let := lpsOriginalJBaseQToC.toAlgebra
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact IsScalarTower.of_algebraMap_eq'
    lpsOriginalJBaseQToC_actualEmbedding.symm
lemma lpsOriginalGeneratedFunctionFieldQ_mem_complex (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∀ x ∈ lpsOriginalGeneratedFunctionFieldQ N hN,
      x ∈ lpsOriginalGeneratedFunctionField N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let := lpsOriginalJBaseQToC.toAlgebra
  let := lpsOriginalJBaseQToC_actualTower
  have hle : lpsOriginalGeneratedFunctionFieldQ N hN ≤
      (lpsOriginalGeneratedFunctionField N hN).restrictScalars
        (FractionRing (Polynomial ℚ)) := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    exact IntermediateField.subset_adjoin (FractionRing (Polynomial ℂ))
      {lpsOriginalJNInFractionField N hN} hx
  exact hle
section ScalarExtension
local instance _p2m_local_instance_6e81b77173_97 : Algebra (FractionRing (Polynomial ℚ)) (FractionRing (Polynomial ℂ)) :=
  lpsOriginalJBaseQToC.toAlgebra
local instance _p2m_local_instance_6e81b77173_99 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local instance _p2m_local_instance_6e81b77173_101 : Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
local instance _p2m_local_instance_6e81b77173_103 : IsScalarTower (FractionRing (Polynomial ℚ))
    (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJBaseQToC_actualTower
def lpsOriginalGeneratedQToComplex (N : ℕ) (hN : 0 < N) :
    lpsOriginalGeneratedFunctionFieldQ N hN →ₐ[FractionRing (Polynomial ℚ)]
      lpsOriginalGeneratedFunctionField N hN := by
  change lpsOriginalGeneratedFunctionFieldQ N hN →ₐ[FractionRing (Polynomial ℚ)]
    (lpsOriginalGeneratedFunctionField N hN).restrictScalars (FractionRing (Polynomial ℚ))
  exact IntermediateField.inclusion (lpsOriginalGeneratedFunctionFieldQ_mem_complex N hN)
def lpsOriginalRationalComplexTensorMap (N : ℕ) (hN : 0 < N) :
    (FractionRing (Polynomial ℂ)) ⊗[FractionRing (Polynomial ℚ)]
      (lpsOriginalGeneratedFunctionFieldQ N hN) →ₐ[FractionRing (Polynomial ℂ)]
        lpsOriginalGeneratedFunctionField N hN :=
  (AlgHom.liftEquiv (FractionRing (Polynomial ℚ)) (FractionRing (Polynomial ℂ))
    (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalGeneratedFunctionField N hN))
      (lpsOriginalGeneratedQToComplex N hN)
lemma lpsOriginalRationalComplexTensorMap_tmul (N : ℕ) (hN : 0 < N)
    (r : FractionRing (Polynomial ℂ)) (x : lpsOriginalGeneratedFunctionFieldQ N hN) :
    lpsOriginalRationalComplexTensorMap N hN (r ⊗ₜ[FractionRing (Polynomial ℚ)] x) =
      r • lpsOriginalGeneratedQToComplex N hN x := rfl
lemma lpsOriginalRationalComplexTensorMap_surjective
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Function.Surjective (lpsOriginalRationalComplexTensorMap N hN) := by
  let pb := IntermediateField.adjoin.powerBasis
    (lpsOriginalJNInFractionField_integral N hN)
  let αQ : lpsOriginalGeneratedFunctionFieldQ N hN :=
    ⟨lpsOriginalJNInFractionField N hN,
      IntermediateField.subset_adjoin (FractionRing (Polynomial ℚ))
        {lpsOriginalJNInFractionField N hN} (Set.mem_singleton _)⟩
  have hα : lpsOriginalRationalComplexTensorMap N hN
      ((1 : FractionRing (Polynomial ℂ)) ⊗ₜ[FractionRing (Polynomial ℚ)] αQ) = pb.gen := by
    rw [lpsOriginalRationalComplexTensorMap_tmul,one_smul]
    apply Subtype.ext
    rfl
  intro x
  obtain ⟨P,hP⟩ := pb.exists_eq_aeval' x
  refine ⟨Polynomial.aeval
    ((1 : FractionRing (Polynomial ℂ)) ⊗ₜ[FractionRing (Polynomial ℚ)] αQ) P,?_⟩
  rw [←Polynomial.aeval_algHom_apply,hα]
  exact hP.symm
lemma lpsOriginalRationalComplexTensorMap_finrank
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Module.finrank (FractionRing (Polynomial ℂ))
      ((FractionRing (Polynomial ℂ)) ⊗[FractionRing (Polynomial ℚ)]
        (lpsOriginalGeneratedFunctionFieldQ N hN)) =
    Module.finrank (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN) := by
  let : Module.Free (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace _ _)
  rw [Module.finrank_baseChange,lpsOriginalGeneratedFunctionFieldQ_finrank_eq,
    lpsOriginalGeneratedFunctionField_finrank_eq]
lemma lpsOriginalRationalComplexTensorMap_injective
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Function.Injective (lpsOriginalRationalComplexTensorMap N hN) := by
  let := lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hN
  let := lpsOriginalGeneratedFunctionField_finiteDimensional N hN
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (lpsOriginalRationalComplexTensorMap_finrank N hN)).mpr
      (lpsOriginalRationalComplexTensorMap_surjective N hN)
def lpsOriginalRationalComplexTensorEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (FractionRing (Polynomial ℂ)) ⊗[FractionRing (Polynomial ℚ)]
      (lpsOriginalGeneratedFunctionFieldQ N hN) ≃ₐ[FractionRing (Polynomial ℂ)]
        lpsOriginalGeneratedFunctionField N hN :=
  AlgEquiv.ofBijective (lpsOriginalRationalComplexTensorMap N hN)
    ⟨lpsOriginalRationalComplexTensorMap_injective N hN,
      lpsOriginalRationalComplexTensorMap_surjective N hN⟩
def lpsOriginalRationalCompactMeromorphicTensorEquiv
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    (FractionRing (Polynomial ℂ)) ⊗[FractionRing (Polynomial ℚ)]
      (lpsOriginalGeneratedFunctionFieldQ N hpos) ≃ₐ[FractionRing (Polynomial ℂ)]
        LPSOriginalCompactMeromorphicGermRing N hN := by
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  exact (lpsOriginalRationalComplexTensorEquiv N hpos).trans
    (lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN)
def lpsOriginalIntegerNormalGenericJFractionEmbedding
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hpos
    FractionRing (Polynomial ℚ) →+*
      (lpsOriginalIntegerNormalGluedScheme N hpos).functionField := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hpos
  exact (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hpos).symm.toRingHom.comp
    (algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hpos))
def lpsOriginalIntegerNormalGenericFunctionFieldAlgEquiv
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hpos
    letI := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
    (lpsOriginalIntegerNormalGluedScheme N hpos).functionField ≃ₐ[FractionRing (Polynomial ℚ)]
      lpsOriginalGeneratedFunctionFieldQ N hpos := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hpos
  let := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
  let e := lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hpos
  refine { e with commutes' := ?_ }
  intro r
  exact e.apply_symm_apply _
def lpsOriginalIntegerNormalGenericCompactTensorEquiv
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hpos
    letI := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    (FractionRing (Polynomial ℂ)) ⊗[FractionRing (Polynomial ℚ)]
      ((lpsOriginalIntegerNormalGluedScheme N hpos).functionField) ≃ₐ[FractionRing (Polynomial ℂ)]
        LPSOriginalCompactMeromorphicGermRing N hN := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hpos
  let := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : FractionRing (Polynomial ℂ) ≃ₐ[FractionRing (Polynomial ℂ)]
    FractionRing (Polynomial ℂ))
    (lpsOriginalIntegerNormalGenericFunctionFieldAlgEquiv N hpos)).trans
      (lpsOriginalRationalCompactMeromorphicTensorEquiv N hpos hN)
end ScalarExtension
end
end QEC.Coding.TannerLiftedProduct


