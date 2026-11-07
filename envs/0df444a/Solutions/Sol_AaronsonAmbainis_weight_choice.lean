-- Prove2me | solution 1 for AaronsonAmbainis.weight_choice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:19:51.264735+00:00
-- url     : https://prove2.me/submissions/f34f351f-aea7-4d6f-9a29-ad647513bfee

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Theorems.Thm_AaronsonAmbainis_le_of_forall_eps

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution {ι : Type*} [Fintype ι] (X Y : ι → ℝ) (hX : ∀ j, 0 ≤ X j)
    (hY : ∀ j, 0 ≤ Y j) (C Q : ℝ) (hC : 0 ≤ C)
    (h : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      Q ≤ (∑ j, w j * X j * Y j) * (C * ∑ j, (w j)⁻¹)) :
    Q ≤ C * (∑ j, Real.sqrt (X j * Y j)) ^ 2 := by
  have hr : ∀ j, 0 ≤ Real.sqrt (X j * Y j) := fun j => Real.sqrt_nonneg _
  have hS : 0 ≤ ∑ j, Real.sqrt (X j * Y j) := Finset.sum_nonneg fun j _ => hr j
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  refine le_of_forall_eps hS hC hcard ?_
  intro ε hε
  have hw : ∀ j, 0 < (Real.sqrt (X j * Y j) + ε)⁻¹ := fun j =>
    inv_pos.mpr (add_pos_of_nonneg_of_pos (hr j) hε)
  have h1 := h (fun j => (Real.sqrt (X j * Y j) + ε)⁻¹) hw
  have hA : ∑ j, (Real.sqrt (X j * Y j) + ε)⁻¹ * X j * Y j
      ≤ ∑ j, Real.sqrt (X j * Y j) := by
    apply Finset.sum_le_sum
    intro j _
    have hpos : 0 < Real.sqrt (X j * Y j) + ε := add_pos_of_nonneg_of_pos (hr j) hε
    have hsq : Real.sqrt (X j * Y j) * Real.sqrt (X j * Y j) = X j * Y j :=
      Real.mul_self_sqrt (mul_nonneg (hX j) (hY j))
    rw [mul_assoc, inv_mul_le_iff₀ hpos]
    nlinarith [mul_nonneg (hr j) hε.le]
  have hB : ∑ j, ((Real.sqrt (X j * Y j) + ε)⁻¹)⁻¹
      = ∑ j, Real.sqrt (X j * Y j) + (Fintype.card ι : ℝ) * ε := by
    simp only [inv_inv]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hD : 0 ≤ C * (∑ j, Real.sqrt (X j * Y j) + (Fintype.card ι : ℝ) * ε) :=
    mul_nonneg hC (add_nonneg hS (mul_nonneg hcard hε.le))
  calc Q ≤ (∑ j, (Real.sqrt (X j * Y j) + ε)⁻¹ * X j * Y j)
        * (C * ∑ j, ((Real.sqrt (X j * Y j) + ε)⁻¹)⁻¹) := h1
    _ = (∑ j, (Real.sqrt (X j * Y j) + ε)⁻¹ * X j * Y j)
        * (C * (∑ j, Real.sqrt (X j * Y j) + (Fintype.card ι : ℝ) * ε)) := by rw [hB]
    _ ≤ (∑ j, Real.sqrt (X j * Y j))
        * (C * (∑ j, Real.sqrt (X j * Y j) + (Fintype.card ι : ℝ) * ε)) :=
        mul_le_mul_of_nonneg_right hA hD
end AaronsonAmbainis
