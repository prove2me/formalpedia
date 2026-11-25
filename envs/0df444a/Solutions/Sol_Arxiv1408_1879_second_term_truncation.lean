-- Prove2me | solution 1 for Arxiv1408_1879.second_term_truncation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T11:39:00.31696+00:00
-- url     : https://prove2.me/submissions/f6811715-d215-4d61-8c02-44926e3ca209

import Mathlib
import Definitions.Def_Arxiv1408_1879_Basic
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace Arxiv1408_1879

theorem second_term_truncation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E ≃L[ℂ] E) (R : E →L[ℂ] E) (ψi : E) :
    seriesTerm L R ψi 0 = firstApprox L ψi ∧
    seriesTerm L R ψi 1 = correctionTerm L R ψi ∧
    (∑ n ∈ Finset.range 2, (-1 : ℂ) ^ n • seriesTerm L R ψi n) =
      firstApprox L ψi - correctionTerm L R ψi ∧
    correctionTerm L R ψi = L.symm (R (firstApprox L ψi)) := by
  have h0 : seriesTerm L R ψi 0 = firstApprox L ψi := by
    simp [seriesTerm, firstApprox]
  have h1 : seriesTerm L R ψi 1 = correctionTerm L R ψi := by
    simp [seriesTerm, correctionTerm]
  refine ⟨h0, h1, ?_, rfl⟩
  rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
  simp [sub_eq_add_neg]

end Arxiv1408_1879
open Arxiv1408_1879 in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E ≃L[ℂ] E) (R : E →L[ℂ] E) (ψi : E) :
    seriesTerm L R ψi 0 = firstApprox L ψi ∧
    seriesTerm L R ψi 1 = correctionTerm L R ψi ∧
    (∑ n ∈ Finset.range 2, (-1 : ℂ) ^ n • seriesTerm L R ψi n) =
      firstApprox L ψi - correctionTerm L R ψi ∧
    correctionTerm L R ψi = L.symm (R (firstApprox L ψi)) :=
  second_term_truncation L R ψi
