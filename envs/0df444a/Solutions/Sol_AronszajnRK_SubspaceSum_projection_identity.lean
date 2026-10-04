-- Prove2me | solution 1 for AronszajnRK.SubspaceSum.projection_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T08:14:35.774215+00:00
-- url     : https://prove2.me/submissions/2454f888-60ce-4dde-9cff-600db71751dc

import Mathlib
import Definitions.Def_AronszajnRK_SubspaceSum_sumProjection

set_option autoImplicit false

namespace ProjId43c38e6a

theorem ab_pow {R : Type*} [Ring R] (a b : R) (k : ℕ) : a * (b * a) ^ k = (a * b) ^ k * a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih]
    simp only [mul_assoc]

theorem key {R : Type*} [Ring R] (P p q : R) (hp : p * p = p) (hq : q * q = q)
    (hpP : p * P = p) (hqP : q * P = q) (hPp : P * p = p) (hPq : P * q = q) (hPP : P * P = P)
    (n : ℕ) :
    ((P - p) * (P - q)) ^ (n + 1) =
      P - (∑ k ∈ Finset.range (n + 1),
        (p * (q * p) ^ k + q * (p * q) ^ k - (q * p) ^ (k + 1) - (p * q) ^ (k + 1))) -
        (q * p) ^ (n + 1) := by
  have hp' : ∀ z, p * (p * z) = p * z := fun z => by rw [← mul_assoc, hp]
  have hq' : ∀ z, q * (q * z) = q * z := fun z => by rw [← mul_assoc, hq]
  have hpP' : ∀ z, p * (P * z) = p * z := fun z => by rw [← mul_assoc, hpP]
  have hqP' : ∀ z, q * (P * z) = q * z := fun z => by rw [← mul_assoc, hqP]
  have hPp' : ∀ z, P * (p * z) = p * z := fun z => by rw [← mul_assoc, hPp]
  have hPq' : ∀ z, P * (q * z) = q * z := fun z => by rw [← mul_assoc, hPq]
  have hPP' : ∀ z, P * (P * z) = P * z := fun z => by rw [← mul_assoc, hPP]
  set f : ℕ → R := fun k =>
    p * (q * p) ^ k + q * (p * q) ^ k - (q * p) ^ (k + 1) - (p * q) ^ (k + 1) with hf
  set g : ℕ → R := fun k =>
    q * (p * q) ^ (k + 1) + p * (q * p) ^ (k + 1) - (q * p) ^ (k + 1) - (p * q) ^ (k + 1 + 1)
    with hg
  have h1 : P * ((P - p) * (P - q)) = P - p - q + p * q := by
    simp only [mul_sub, sub_mul, mul_assoc, hPP', hPp', hPq', hpP', hPP, hPp, hPq, hpP]
    abel
  have h2 : ∀ N : ℕ, (q * p) ^ (N + 1) * ((P - p) * (P - q)) = 0 := by
    intro N
    rw [pow_succ]
    simp only [mul_sub, sub_mul, mul_assoc, hp', hq', hpP', hqP', hp, hq, hpP, hqP]
    abel
  have h3 : ∀ k, f k * ((P - p) * (P - q)) = g k := by
    intro k
    simp only [hf, hg]
    rw [ab_pow p q k, ab_pow q p k, ab_pow q p (k + 1), ab_pow p q (k + 1)]
    simp only [pow_succ]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_assoc, hp', hq', hpP', hqP', hp, hq,
      hpP, hqP]
    abel
  have h4 : ∀ N : ℕ, (∑ k ∈ Finset.range (N + 1), f k) + (q * p) ^ (N + 1) =
      p + q - p * q + ∑ k ∈ Finset.range N, g k := by
    intro N
    induction N with
    | zero =>
      simp only [hf, Finset.sum_range_one, Finset.sum_range_zero, pow_zero, mul_one, zero_add,
        pow_one, add_zero]
      abel
    | succ N ih =>
      rw [Finset.sum_range_succ f (N + 1), Finset.sum_range_succ g N,
        eq_sub_of_add_eq ih]
      simp only [hf, hg]
      abel
  induction n with
  | zero =>
    simp only [zero_add, pow_one, Finset.sum_range_one, hf, pow_zero, mul_one]
    simp only [mul_sub, sub_mul, hPP, hPq, hpP]
    abel
  | succ n ih =>
    rw [pow_succ, ih]
    change (P - ∑ k ∈ Finset.range (n + 1), f k - (q * p) ^ (n + 1)) * ((P - p) * (P - q)) =
      P - ∑ k ∈ Finset.range (n + 1 + 1), f k - (q * p) ^ (n + 1 + 1)
    rw [sub_mul, sub_mul, h1, h2, Finset.sum_mul, Finset.sum_congr rfl (fun k _ => h3 k),
      eq_sub_of_add_eq (h4 (n + 1))]
    abel

end ProjId43c38e6a

open AronszajnRK.SubspaceSum in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) (m : ℕ) (hm : 1 ≤ m) :
    let P : E →L[ℂ] E := sumProjection F₁ F₂
    let P₁ : E →L[ℂ] E := (F₁ : Submodule ℂ E).starProjection
    let P₂ : E →L[ℂ] E := (F₂ : Submodule ℂ E).starProjection
    ((P - P₁) * (P - P₂)) ^ m =
      P - (∑ k ∈ Finset.range m,
        (P₁ * (P₂ * P₁) ^ k + P₂ * (P₁ * P₂) ^ k -
          (P₂ * P₁) ^ (k + 1) - (P₁ * P₂) ^ (k + 1))) -
        (P₂ * P₁) ^ m := by
  intro P P₁ P₂
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have le1 : (F₁ : Submodule ℂ E) ≤ ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E) :=
    ClosedSubmodule.toSubmodule_le_toSubmodule.mpr le_sup_left
  have le2 : (F₂ : Submodule ℂ E) ≤ ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E) :=
    ClosedSubmodule.toSubmodule_le_toSubmodule.mpr le_sup_right
  have idem : ∀ K : ClosedSubmodule ℂ E,
      (K : Submodule ℂ E).starProjection * (K : Submodule ℂ E).starProjection =
        (K : Submodule ℂ E).starProjection :=
    fun K => (K : Submodule ℂ E).isIdempotentElem_starProjection
  have right : ∀ U V : ClosedSubmodule ℂ E, (U : Submodule ℂ E) ≤ (V : Submodule ℂ E) →
      (U : Submodule ℂ E).starProjection * (V : Submodule ℂ E).starProjection =
        (U : Submodule ℂ E).starProjection :=
    fun U V h => Submodule.starProjection_comp_starProjection_of_le h
  have left : ∀ U V : ClosedSubmodule ℂ E, (U : Submodule ℂ E) ≤ (V : Submodule ℂ E) →
      (V : Submodule ℂ E).starProjection * (U : Submodule ℂ E).starProjection =
        (U : Submodule ℂ E).starProjection := by
    intro U V h
    ext x
    show (V : Submodule ℂ E).starProjection ((U : Submodule ℂ E).starProjection x) =
      (U : Submodule ℂ E).starProjection x
    rw [Submodule.starProjection_eq_self_iff]
    exact h (Submodule.starProjection_apply_mem _ x)
  exact ProjId43c38e6a.key P P₁ P₂ (idem F₁) (idem F₂) (right _ _ le1) (right _ _ le2)
    (left _ _ le1) (left _ _ le2) (idem _) n
