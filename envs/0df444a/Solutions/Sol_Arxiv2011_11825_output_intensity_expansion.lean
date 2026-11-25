-- Prove2me | solution 1 for Arxiv2011_11825.output_intensity_expansion
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:55:40.814694+00:00
-- url     : https://prove2.me/submissions/04c9fc33-05c2-40c7-ab99-b7a4e189ed5b

import Mathlib
import Definitions.Def_Arxiv2011_11825_Basic

open Finset Arxiv2011_11825

lemma outIntensity_eq_double_sum {M N : ℕ} (t : Matrix (Fin M) (Fin N) ℂ) (E : Fin N → ℂ)
    (m : Fin M) :
    outIntensity t E m = ∑ i, ∑ j, (amp t E m i * (starRingEnd ℂ) (amp t E m j)).re := by
  have h : outField t E m = ∑ i, amp t E m i := rfl
  have hn : ∀ z : ℂ, Complex.normSq z = (z * (starRingEnd ℂ) z).re := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re]
  rw [outIntensity, hn, h, map_sum, sum_mul_sum, Complex.re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]

theorem solution {M N : ℕ} (t : Matrix (Fin M) (Fin N) ℂ) (E : Fin N → ℂ)
    (m : Fin M) :
    outIntensity t E m =
      (∑ i, Complex.normSq (amp t E m i)) +
        ∑ i, ∑ j ∈ univ.filter (fun j => j ≠ i),
          (amp t E m i * (starRingEnd ℂ) (amp t E m j)).re := by
  rw [outIntensity_eq_double_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← add_sum_erase _ _ (mem_univ i), filter_ne', Complex.mul_conj, Complex.ofReal_re]
