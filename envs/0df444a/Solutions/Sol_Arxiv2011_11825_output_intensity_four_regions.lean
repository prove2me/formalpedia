-- Prove2me | solution 1 for Arxiv2011_11825.output_intensity_four_regions
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:55:45.682716+00:00
-- url     : https://prove2.me/submissions/5a81c3f9-fdc2-4163-91d3-f26af3f70b11

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

lemma outIntensity_eq_sum_segBracket {M N k : ℕ} (t : Matrix (Fin M) (Fin N) ℂ)
    (E : Fin N → ℂ) (m : Fin M) (seg : Fin N → Fin k) :
    outIntensity t E m = ∑ p, segBracket t E m seg p := by
  set f : Fin N → Fin N → ℝ := fun i j => (amp t E m i * (starRingEnd ℂ) (amp t E m j)).re
    with hf
  rw [outIntensity_eq_double_sum, ← sum_fiberwise univ seg]
  refine sum_congr rfl fun p _ => ?_
  -- rewrite the bracket as a single sum over the modes of segment `p`
  have hself : selfTerm t E m seg p = ∑ i ∈ univ.filter (fun i => seg i = p), f i i := by
    unfold selfTerm
    refine sum_congr rfl fun i _ => ?_
    simp only [hf]
    rw [Complex.mul_conj, Complex.ofReal_re]
  have hcross : ∑ q ∈ univ.filter (fun q => q ≠ p), crossTerm t E m seg p q =
      ∑ i ∈ univ.filter (fun i => seg i = p),
        ∑ q ∈ univ.filter (fun q => q ≠ p), ∑ j ∈ univ.filter (fun j => seg j = q), f i j := by
    unfold crossTerm
    exact sum_comm
  unfold segBracket
  rw [hself, hcross]
  unfold intraTerm
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hip : seg i = p := (mem_filter.mp hi).2
  -- split the inner sum over all `j` by the segment of `j`
  rw [← sum_fiberwise univ seg (f i), ← add_sum_erase _ _ (mem_univ p), filter_ne' univ p]
  congr 1
  rw [← add_sum_erase _ _ (mem_filter.mpr ⟨mem_univ i, hip⟩)]
  congr 1
  refine sum_congr ?_ fun _ _ => rfl
  ext j
  simp [and_comm]

theorem solution {M N : ℕ} (t : Matrix (Fin M) (Fin N) ℂ) (E : Fin N → ℂ)
    (m : Fin M) (seg : Fin N → Fin 4) (hseg : Function.Surjective seg) :
    outIntensity t E m =
      (selfTerm t E m seg 0 + intraTerm t E m seg 0 + crossTerm t E m seg 0 1 +
          crossTerm t E m seg 0 2 + crossTerm t E m seg 0 3) +
        (selfTerm t E m seg 1 + intraTerm t E m seg 1 + crossTerm t E m seg 1 0 +
          crossTerm t E m seg 1 2 + crossTerm t E m seg 1 3) +
        (selfTerm t E m seg 2 + intraTerm t E m seg 2 + crossTerm t E m seg 2 0 +
          crossTerm t E m seg 2 1 + crossTerm t E m seg 2 3) +
        (selfTerm t E m seg 3 + intraTerm t E m seg 3 + crossTerm t E m seg 3 0 +
          crossTerm t E m seg 3 1 + crossTerm t E m seg 3 2) := by
  rw [outIntensity_eq_sum_segBracket t E m seg, Fin.sum_univ_four]
  simp only [segBracket, sum_filter, Fin.sum_univ_four]
  simp
  ring
