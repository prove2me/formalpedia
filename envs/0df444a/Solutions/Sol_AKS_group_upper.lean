-- Prove2me | solution 1 for AKS.group_upper
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:23:10.722458+00:00
-- url     : https://prove2.me/submissions/dceb804d-323c-47a9-abd0-cc6c4e74dd61

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg

open Polynomial AKS

noncomputable def g80a_h : Polynomial (ZMod 2) := X ^ 3 + X + 1

theorem g80a_two : (2 : Polynomial (ZMod 2)) = 0 := by
  exact CharTwo.two_eq_zero

theorem g80a_natDeg : g80a_h.natDegree = 3 := by
  unfold g80a_h; compute_degree!

theorem g80a_irr : Irreducible g80a_h := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [g80a_natDeg]; decide
  · intro x hx
    rw [IsRoot.def] at hx
    simp only [g80a_h, eval_add, eval_pow, eval_X, eval_one] at hx
    revert hx; revert x; decide

theorem g80a_dvd : g80a_h ∣ (X ^ 7 - 1 : Polynomial (ZMod 2)) := by
  refine ⟨X ^ 4 + X ^ 2 + X + 1, ?_⟩
  have e : (X ^ 7 - 1 : Polynomial (ZMod 2)) = g80a_h * (X ^ 4 + X ^ 2 + X + 1)
      - 2 * (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) := by
    unfold g80a_h; ring
  rw [e, g80a_two]; ring

theorem g80a_frob (j : ℕ) (f : Polynomial (ZMod 2)) : f ^ (2 ^ j) = f.comp (X ^ (2 ^ j)) := by
  rw [← expand_eq_comp_X_pow]
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih, ← ZMod.expand_card, expand_expand, mul_comm]

theorem g80a_not_dvd {d : ℕ} (hd0 : 0 < d) (hd : d ≤ 3) :
    ¬ g80a_h ∣ (X ^ d - 1 : Polynomial (ZMod 2)) := by
  intro hdvd
  have e1 : (X ^ d - 1 : Polynomial (ZMod 2)) = X ^ d - C 1 := by simp
  have hne : (X ^ d - 1 : Polynomial (ZMod 2)) ≠ 0 := by
    rw [e1]; exact X_pow_sub_C_ne_zero hd0 1
  have hdeg := natDegree_le_of_dvd hdvd hne
  rw [g80a_natDeg, e1, natDegree_X_pow_sub_C] at hdeg
  have hd3 : d = 3 := by omega
  subst hd3
  -- X^3 - 1 = h - X in characteristic two
  have e : (X ^ 3 - 1 : Polynomial (ZMod 2)) = g80a_h - X - 2 * (X ^ 0 : Polynomial (ZMod 2)) := by
    unfold g80a_h; ring
  rw [e, g80a_two, zero_mul, sub_zero] at hdvd
  have h2 : g80a_h ∣ X := by
    have := dvd_sub (dvd_refl g80a_h) hdvd
    simpa using this
  have := natDegree_le_of_dvd h2 X_ne_zero
  rw [g80a_natDeg, natDegree_X] at this
  omega

theorem solution : ¬ (∀ (n p r t ℓ : ℕ) [Fact (Nat.Prime p)]
    (h : Polynomial (ZMod p)) [Fact (Irreducible h)],
    h ∣ (Polynomial.X ^ r - 1 : Polynomial (ZMod p)) →
    (∀ m, inI n p m → ∀ f, inP p ℓ f → introspective p r f m) →
    (¬ ∃ k, 0 < k ∧ n = p ^ k) →
    t = (Gfin n p r).card →
    (Nat.gcd (n / p) r = 1 ∧ Nat.gcd p r = 1) →
    ∃ m₁ m₂ : ℕ, m₂ < m₁ ∧ m₁ ≤ n ^ (Nat.sqrt t) ∧
      ∀ f, inP p ℓ f →
        Polynomial.aeval (AdjoinRoot.root h) f ^ m₁
          = Polynomial.aeval (AdjoinRoot.root h) f ^ m₂) := by
  intro H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Irreducible g80a_h) := ⟨g80a_irr⟩
  have hintros : ∀ m, inI 3 2 m → ∀ f, inP 2 0 f → introspective 2 7 f m := by
    rintro m ⟨i, j, rfl⟩ f -
    unfold introspective
    have : (3 / 2 : ℕ) = 1 := by norm_num
    rw [this, one_pow, one_mul, g80a_frob j f, sub_self]
    exact dvd_zero _
  have hnpow : ¬ ∃ k, 0 < k ∧ 3 = 2 ^ k := by
    rintro ⟨k, hk, h3⟩
    have := congrArg (· % 2) h3
    rw [Nat.pow_mod] at this
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [pow_succ] at this
  have hcard : (Gfin 3 2 7).card = 3 := by decide
  obtain ⟨m₁, m₂, hlt, hle, hall⟩ := H 3 2 7 3 0 g80a_h g80a_dvd hintros hnpow hcard.symm
    (by norm_num)
  have hsq : Nat.sqrt 3 = 1 := by norm_num [Nat.sqrt]
  rw [hsq, pow_one] at hle
  have hX : inP 2 0 (X : Polynomial (ZMod 2)) := ⟨fun _ => 1, by simp⟩
  have h1 := hall X hX
  rw [aeval_X] at h1
  set ξ := AdjoinRoot.root g80a_h
  have hξ0 : ξ ≠ 0 := by
    intro h0
    have : g80a_h ∣ X := by
      rw [← AdjoinRoot.mk_eq_zero]; simpa [ξ] using h0
    have := natDegree_le_of_dvd this X_ne_zero
    rw [g80a_natDeg, natDegree_X] at this; omega
  have hd : ξ ^ (m₁ - m₂) = 1 := by
    have e : ξ ^ m₁ = ξ ^ (m₁ - m₂) * ξ ^ m₂ := by rw [← pow_add]; congr 1; omega
    rw [e] at h1
    exact mul_right_cancel₀ (pow_ne_zero _ hξ0) (h1.trans (one_mul _).symm)
  have : g80a_h ∣ (X ^ (m₁ - m₂) - 1 : Polynomial (ZMod 2)) := by
    rw [← AdjoinRoot.mk_eq_zero]
    simp only [map_sub, map_pow, AdjoinRoot.mk_X, map_one]
    rw [hd, sub_self]
  exact g80a_not_dvd (by omega) (by omega) this
