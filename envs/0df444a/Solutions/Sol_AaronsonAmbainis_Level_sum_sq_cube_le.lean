-- Prove2me | solution 1 for AaronsonAmbainis.Level.sum_sq_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:00:38.033125+00:00
-- url     : https://prove2.me/submissions/a95ff8aa-ceef-48cd-b10b-eeb9c80ecc18

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Median

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
namespace AaronsonAmbainis.Level
theorem _root_.solution {α : Type*} (s : Finset α) (z : α → ℝ) :
    (∑ i ∈ s, z i ^ 2) ^ 3 ≤ (s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := by
  have hA : 0 ≤ ∑ i ∈ s, z i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  -- `(∑ z²)² ≤ (∑ |z|)(∑ |z|^3)`
  have h1 : (∑ i ∈ s, z i ^ 2) ^ 2 ≤ (∑ i ∈ s, |z i|) * (∑ i ∈ s, |z i| ^ 3) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i _ => abs_nonneg _)
      (fun i _ => pow_nonneg (abs_nonneg _) 3)
      (fun i _ => by
        rw [← sq_abs (z i)]
        exact le_of_eq (by ring))
  -- `(∑ |z|)² ≤ #s ∑ z²`
  have h2 : (∑ i ∈ s, |z i|) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, z i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => |z i|)
    simp only [sq_abs] at h
    exact h
  rcases hA.eq_or_lt with h0 | hpos
  · rw [← h0]
    have : (0 : ℝ) ≤ (s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := by positivity
    simpa using this
  · have h3 : ((∑ i ∈ s, z i ^ 2) ^ 2) ^ 2
        ≤ ((∑ i ∈ s, |z i|) * (∑ i ∈ s, |z i| ^ 3)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    have h4 : ((∑ i ∈ s, |z i|) * (∑ i ∈ s, |z i| ^ 3)) ^ 2
        ≤ ((s.card : ℝ) * ∑ i ∈ s, z i ^ 2) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    have h5 : (∑ i ∈ s, z i ^ 2) * (∑ i ∈ s, z i ^ 2) ^ 3
        ≤ (∑ i ∈ s, z i ^ 2) * ((s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2) := by
      calc (∑ i ∈ s, z i ^ 2) * (∑ i ∈ s, z i ^ 2) ^ 3
          = ((∑ i ∈ s, z i ^ 2) ^ 2) ^ 2 := by ring
        _ ≤ ((s.card : ℝ) * ∑ i ∈ s, z i ^ 2) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := h3.trans h4
        _ = (∑ i ∈ s, z i ^ 2) * ((s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2) := by ring
    exact le_of_mul_le_mul_left h5 hpos
end AaronsonAmbainis.Level
