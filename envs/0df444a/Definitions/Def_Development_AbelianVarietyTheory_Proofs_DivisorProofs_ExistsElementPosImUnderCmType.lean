-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsElementPosImUnderCmType
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsElementPosImUnderCmType
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:42:49.787392+00:00
-- url     : https://prove2.me/theorems/ef3f48b3-5c9d-4658-9df9-b6c2659702bb
-- title:
--   Exists Element Pos Im Under Cm Type
-- statement:
--   Definitions and structural lemmas for Exists Element Pos Im Under Cm Type, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsElementPosImUnderCmType.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DenseRangeEmbeddingPi
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_DenseEmbeddingProduct_denseRange_embedding_pi
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub
attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply


set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
open NumberField IsDedekindDomain GlobalTheory.CMVal
namespace GlobalTheory.CMTypeImPos
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem denseRange_embeddings : DenseRange fun (x : E) (w : InfinitePlace E) => w.embedding x := by
  first
  | exact @_root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi
  | exact _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi
  | (apply _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi ..)
theorem exists_im_pos (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) : ∃ θ : E, ∀ i, 0 < (φ i θ).im := by
  classical

  let f : I → (InfinitePlace E → ℂ) → ℝ := fun i z =>
    if (InfinitePlace.mk (φ i)).embedding = φ i then (z (InfinitePlace.mk (φ i))).im
    else -(z (InfinitePlace.mk (φ i))).im
  have hfc : ∀ i, Continuous (f i) := by
    intro i
    by_cases h : (InfinitePlace.mk (φ i)).embedding = φ i
    · simp only [f, h, if_true]
      exact Complex.continuous_im.comp (continuous_apply _)
    · simp only [f, h, if_false]
      exact (Complex.continuous_im.comp (continuous_apply _)).neg
  let U : Set (InfinitePlace E → ℂ) := {z | ∀ i, 0 < f i z}
  have hU : IsOpen U := by
    have : U = ⋂ i, {z | 0 < f i z} := by ext z; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hfc i)

  let y : InfinitePlace E → ℂ := fun w => if ∃ j, w.embedding = φ j then Complex.I else -Complex.I
  have hy : y ∈ U := by
    intro i
    have hnr : ¬ ComplexEmbedding.IsReal (φ i) :=
      InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex _)
    rcases InfinitePlace.embedding_mk_eq (φ i) with h | h
    · have hex : ∃ j, (InfinitePlace.mk (φ i)).embedding = φ j := ⟨i, h⟩
      simp [f, y, h, hex]
    · have hne : (InfinitePlace.mk (φ i)).embedding ≠ φ i := by
        rw [h]; exact fun h' => hnr (ComplexEmbedding.isReal_iff.2 h')
      have hex : ¬ ∃ j, (InfinitePlace.mk (φ i)).embedding = φ j := by
        rintro ⟨j, hj⟩
        obtain ⟨k, _, hk⟩ := hφ (InfinitePlace.mk (φ i)).embedding
        have hi : i = k := hk i (Or.inr h)
        have hj' : j = k := hk j (Or.inl hj)
        subst hi; subst hj'
        exact hne hj
      simp [f, y, hne, hex]
  obtain ⟨θ, hθ⟩ := denseRange_embeddings.exists_mem_open hU ⟨y, hy⟩
  refine ⟨θ, fun i => ?_⟩
  have := hθ i
  rcases InfinitePlace.embedding_mk_eq (φ i) with h | h
  · simpa [f, h] using this
  · by_cases h' : (InfinitePlace.mk (φ i)).embedding = φ i
    · simpa [f, h'] using this
    · simp only [f, h', if_false] at this
      rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_im] at this
      linarith
end GlobalTheory.CMTypeImPos
example : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∃ θ : E, ∀ i, 0 < (φ i θ).im := GlobalTheory.CMTypeImPos.exists_im_pos


