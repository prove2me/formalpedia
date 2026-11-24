-- Prove2me | Definitions.Def_SourceProof_81a7a13dc7d130704fab006e
-- name    : SourceProof_81a7a13dc7d130704fab006e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:34.196353+00:00
-- url     : https://prove2.me/theorems/fae59a93-8e15-48f8-a869-c22429e456d0
-- title:
--   StochLean source theorem: StochLean.sum_intervalIncrement_eq_zero

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Analysis_PathVariation_StepIntegral_F000

open private intervalStep_eventually_right from Definitions.Def_StochLean_Analysis_PathVariation_StepIntegral_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Representation independence of finite interval integration

The integrator is an arbitrary real-valued function. A zero finite linear
combination of half-open interval indicators has zero increment integral.
This is the deterministic algebra behind Protter's elementary integral.
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal Topology BigOperators

namespace StochLean


theorem _root_.Prove2MeSourceProof.h_81a7a13dc7d130704fab006e {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (c : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (hzero : ∀ t : ℝ≥0, 0 < t → ∑ i, (if a i < t ∧ t ≤ b i then c i else 0) = 0)
    (f : ℝ≥0 → ℝ) : ∑ i, c i * (f (b i) - f (a i)) = 0 := by
  classical
  have hright (s : ℝ≥0) : ∑ i, (if a i ≤ s ∧ s < b i then c i else 0) = 0 := by
    have hinterval := Filter.eventually_all.mpr fun i ↦
      intervalStep_eventually_right (a i) (b i) s (c i)
    have hpos : ∀ᶠ t in nhdsWithin s (Ioi s), s < t := self_mem_nhdsWithin
    obtain ⟨t, ht, heq⟩ := (hpos.and hinterval).exists
    have hsum := hzero t (lt_of_le_of_lt bot_le ht)
    simpa only [heq] using hsum
  have hpoint (s : ℝ≥0) : ∑ i, (if a i < s ∧ s ≤ b i then c i else 0) = 0 := by
    by_cases hs : s = 0
    · subst s
      simp
    · exact hzero s (lt_of_le_of_ne bot_le (Ne.symm hs))
  have hmass (s : ℝ≥0) :
      (∑ i, if b i = s then c i else 0) - (∑ i, if a i = s then c i else 0) = 0 := by
    have hcell (i : ι) :
        (if b i = s then c i else 0) - (if a i = s then c i else 0) =
          (if a i < s ∧ s ≤ b i then c i else 0) -
            (if a i ≤ s ∧ s < b i then c i else 0) := by
      have hi := hab i
      split_ifs <;> simp_all <;> grind
    rw [← sum_sub_distrib]
    simp_rw [hcell, sum_sub_distrib, hpoint, hright, sub_self]
  let S : Finset ℝ≥0 := univ.image a ∪ univ.image b
  have haS (i : ι) : a i ∈ S := mem_union_left _ (mem_image_of_mem a (mem_univ i))
  have hbS (i : ι) : b i ∈ S := mem_union_right _ (mem_image_of_mem b (mem_univ i))
  calc
    ∑ i, c i * (f (b i) - f (a i)) =
        ∑ i, ∑ s ∈ S, f s * ((if b i = s then c i else 0) -
          (if a i = s then c i else 0)) := by
      apply sum_congr rfl
      intro i _
      simp only [mul_sub, sum_sub_distrib, mul_ite, mul_zero]
      rw [sum_ite_eq S (b i), sum_ite_eq S (a i)]
      simp only [hbS, haS, ↓reduceIte]
      ring
    _ = ∑ s ∈ S, f s * ((∑ i, if b i = s then c i else 0) -
        (∑ i, if a i = s then c i else 0)) := by
      rw [sum_comm]
      simp only [mul_sum, mul_sub, sum_sub_distrib]
    _ = 0 := by simp only [hmass, mul_zero, sum_const_zero]
end StochLean


