-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadr
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:01.942744+00:00
-- url     : https://prove2.me/theorems/640af8f4-bf82-4fd1-9816-3a619a18bbe4
-- title:
--   Im Embedding Ne Zero Of Not Mem Range Of Totally Real Quadr
-- statement:
--   Definitions and structural lemmas for Im Embedding Ne Zero Of Not Mem Range Of Totally Real Quadr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadr.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace GlobalTheory
theorem im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E]
    (w : InfinitePlace E) (θ : E) (hθ : θ ∉ Set.range (algebraMap F E)) :
    (w.embedding θ).im ≠ 0 := by
  intro h
  set φ := w.embedding with hφ
  have hF : ∀ c : F, (φ (algebraMap F E c)).im = 0 := by
    intro c
    have hr : ComplexEmbedding.IsReal (φ.comp (algebraMap F E)) :=
      InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
    have := ComplexEmbedding.isReal_iff.1 hr
    have h2 := RingHom.congr_fun this c
    exact Complex.conj_eq_iff_im.1 h2
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hθ
      refine ⟨-(s / t), ?_⟩
      have : t • θ = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at this
      have ht' : algebraMap F E t ≠ 0 := by simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      rw [mul_comm] at this
      linear_combination -this
  have hspan : Submodule.span F (Set.range ![(1 : E), θ]) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank
    simp [Algebra.IsQuadraticExtension.finrank_eq_two F E]
  have hall : ∀ z : E, (φ z).im = 0 := by
    intro z
    have hz : z ∈ Submodule.span F (Set.range ![(1 : E), θ]) := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hz
    rw [← hc, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Algebra.smul_def,
      mul_one, map_add, map_mul, Complex.add_im, Complex.mul_im, hF, h, zero_mul, mul_zero,
      add_zero]
  have hreal : ComplexEmbedding.IsReal φ := by
    rw [ComplexEmbedding.isReal_iff]
    ext1 z
    exact Complex.conj_eq_iff_im.2 (hall z)
  exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
    (InfinitePlace.isReal_iff.2 hreal)
example : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w : InfinitePlace E) (θ : E), θ ∉ Set.range (algebraMap F E) → (w.embedding θ).im ≠ 0 :=
  im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic
end GlobalTheory


