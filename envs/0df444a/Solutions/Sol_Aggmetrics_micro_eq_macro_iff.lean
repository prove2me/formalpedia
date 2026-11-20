-- Prove2me | solution 1 for Aggmetrics.micro_eq_macro_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:52:45.687853+00:00
-- url     : https://prove2.me/submissions/1af0da41-e689-47a5-8915-6b6b54f10c9f

import Mathlib
import Definitions.Def_Aggmetrics_Basic

set_option autoImplicit true
open Finset
open Aggmetrics
namespace Aggmetrics
theorem _root_.solution {m : ℕ} (hm : 0 < m) (den : Fin m → ℝ) (hden : ∀ j, 0 < den j) :
    (∀ num : Fin m → ℝ,
      (∑ j, num j) / (∑ j, den j) = (1 / (m : ℝ)) * ∑ j, num j / den j)
    ↔ (∀ i j, den i = den j) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hne : (univ : Finset (Fin m)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  have key : ∀ p : Fin m, (∑ k, (if k = p then (1:ℝ) else 0) / den k) = 1 / den p := by
    intro p
    have hcongr : ∀ k, (if k = p then (1:ℝ) else 0) / den k = if k = p then 1 / den p else 0 := by
      intro k; split <;> simp_all
    rw [Finset.sum_congr rfl (fun k _ => hcongr k)]
    simp
  constructor
  · intro h i j
    have hi := h (fun k => if k = i then 1 else 0)
    have hj := h (fun k => if k = j then 1 else 0)
    simp only [Finset.sum_ite_eq' univ, mem_univ, ite_true] at hi hj
    rw [key i] at hi
    rw [key j] at hj
    have heq1 : (1:ℝ)/(m:ℝ) * (1/den i) = 1/(m:ℝ) * (1/den j) := hi.symm.trans hj
    have hm0 : (1:ℝ)/(m:ℝ) ≠ 0 := by positivity
    have heq2 : (1:ℝ)/den i = 1/den j := mul_left_cancel₀ hm0 heq1
    field_simp [(hden i).ne', (hden j).ne'] at heq2
    linarith [heq2]
  · intro h num
    obtain ⟨i0, -⟩ := hne
    have hconst : ∀ j, den j = den i0 := fun j => h j i0
    have hdi0 : den i0 ≠ 0 := (hden i0).ne'
    simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
               ← Finset.sum_div]
    field_simp
end Aggmetrics
