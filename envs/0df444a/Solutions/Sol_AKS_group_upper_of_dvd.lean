-- Prove2me | solution 1 for AKS.group_upper_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:09:05.408878+00:00
-- url     : https://prove2.me/submissions/53f92942-f15d-4231-88e0-ecece3b5d57a

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg
open AKS

open Polynomial in
/-- If X^r - 1 divides f^m - f(X^m) then in AdjoinRoot h (h ∣ X^r - 1) f(ζ)^m = f(ζ^m). -/
theorem g71b_intro_eval {p r : ℕ} (h f : Polynomial (ZMod p))
    (hdiv : h ∣ (X ^ r - 1 : Polynomial (ZMod p))) {m : ℕ} (hm : introspective p r f m) :
    aeval (AdjoinRoot.root h) f ^ m = aeval (AdjoinRoot.root h ^ m) f := by
  have h1 : h ∣ f ^ m - f.comp (X ^ m) := dvd_trans hdiv hm
  have h2 : aeval (AdjoinRoot.root h) (f ^ m - f.comp (X ^ m)) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]; exact h1
  rw [map_sub, map_pow, aeval_comp, map_pow, aeval_X, sub_eq_zero] at h2
  exact h2

open Polynomial in
theorem g71b_root_pow_r {p r : ℕ} (h : Polynomial (ZMod p))
    (hdiv : h ∣ (X ^ r - 1 : Polynomial (ZMod p))) : AdjoinRoot.root h ^ r = 1 := by
  have h2 : aeval (AdjoinRoot.root h) (X ^ r - 1 : Polynomial (ZMod p)) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]; exact hdiv
  rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h2
  exact h2

theorem g71b_pow_mod {M : Type*} [Monoid M] (x : M) (r m : ℕ) (hx : x ^ r = 1) :
    x ^ m = x ^ (m % r) := by
  conv_lhs => rw [← Nat.mod_add_div m r, pow_add, pow_mul, hx, one_pow, mul_one]

theorem g71b_inj (a p : ℕ) (hp : p.Prime) (ha : 0 < a) (hapow : ∀ c, a ≠ p ^ c)
    (i j i' j' : ℕ) (hlt : i' < i) (heq : a ^ i * p ^ j = a ^ i' * p ^ j') : False := by
  have hai : a ^ i = a ^ i' * a ^ (i - i') := by rw [← pow_add]; congr 1; omega
  rw [hai, mul_assoc] at heq
  have hpos : 0 < a ^ i' := pow_pos ha _
  have h2 : a ^ (i - i') * p ^ j = p ^ j' := Nat.eq_of_mul_eq_mul_left hpos heq
  have h3 : a ∣ p ^ j' := by
    rw [← h2]; exact Dvd.dvd.mul_right (dvd_pow_self a (by omega)) _
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).1 h3
  exact hapow c hc

theorem solution (n p r t ℓ : ℕ) [Fact (Nat.Prime p)]
    (hpn : p ∣ n) (hn : 0 < n)
    (h : Polynomial (ZMod p)) [Fact (Irreducible h)]
    (hdiv : h ∣ (Polynomial.X ^ r - 1 : Polynomial (ZMod p)))
    (hintros : ∀ m, inI n p m → ∀ f, inP p ℓ f → introspective p r f m)
    (hnpow : ¬ ∃ k, 0 < k ∧ n = p ^ k)
    (ht : t = (Gfin n p r).card)
    (hcop : Nat.gcd (n / p) r = 1 ∧ Nat.gcd p r = 1) :
    ∃ m₁ m₂ : ℕ, m₂ < m₁ ∧ m₁ ≤ n ^ (Nat.sqrt t) ∧
      ∀ f, inP p ℓ f →
        Polynomial.aeval (AdjoinRoot.root h) f ^ m₁
          = Polynomial.aeval (AdjoinRoot.root h) f ^ m₂ := by
  have hp : p.Prime := Fact.out
  set a := n / p with ha_def
  have hna : n = p * a := (Nat.mul_div_cancel' hpn).symm
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0] at hna; omega
    · exact h0
  have hapow : ∀ c, a ≠ p ^ c := by
    intro c hc
    exact hnpow ⟨c + 1, by omega, by rw [hna, hc, pow_succ, mul_comm]⟩
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · have h2 := hcop.2; rw [h0, Nat.gcd_zero_right] at h2; exact absurd h2 hp.one_lt.ne'
    · exact h0
  set S := Nat.sqrt t with hS
  -- Gfin ⊆ range r so t ≤ r
  have hsub : Gfin n p r ⊆ Finset.range r := by
    intro x hx
    simp only [Gfin, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, -, j, -, rfl⟩ := hx
    exact Finset.mem_range.2 (Nat.mod_lt _ hr)
  have htr : t ≤ r := by rw [ht]; simpa using Finset.card_le_card hsub
  have hmaps : Set.MapsTo (fun q : ℕ × ℕ => (a ^ q.1 * p ^ q.2) % r)
      ↑(Finset.range (S + 1) ×ˢ Finset.range (S + 1)) ↑(Gfin n p r) := by
    intro q hq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hq
    simp only [Finset.mem_coe, Gfin, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
    by_cases hSr : S < r
    · exact ⟨q.1, by omega, q.2, by omega, rfl⟩
    · have hSS : S * S ≤ t := Nat.sqrt_le t
      have hr1 : r = 1 := by
        have : r ≤ S := by omega
        nlinarith
      refine ⟨0, by omega, 0, by omega, ?_⟩
      rw [hr1, Nat.mod_one, Nat.mod_one]
  have hcard : (Gfin n p r).card < (Finset.range (S + 1) ×ˢ Finset.range (S + 1)).card := by
    rw [Finset.card_product, Finset.card_range, ← ht]
    exact Nat.lt_succ_sqrt t
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [Finset.mem_product, Finset.mem_range] at hx hy
  -- the key consequence
  have key : ∀ m₁ m₂ : ℕ, inI n p m₁ → inI n p m₂ → m₁ % r = m₂ % r → ∀ f, inP p ℓ f →
      Polynomial.aeval (AdjoinRoot.root h) f ^ m₁
          = Polynomial.aeval (AdjoinRoot.root h) f ^ m₂ := by
    intro m₁ m₂ h1 h2 hmod f hf
    rw [g71b_intro_eval h f hdiv (hintros m₁ h1 f hf), g71b_intro_eval h f hdiv (hintros m₂ h2 f hf),
      g71b_pow_mod _ r m₁ (g71b_root_pow_r h hdiv), g71b_pow_mod _ r m₂ (g71b_root_pow_r h hdiv), hmod]
  have hbound : ∀ q : ℕ × ℕ, q.1 < S + 1 → q.2 < S + 1 → a ^ q.1 * p ^ q.2 ≤ n ^ S := by
    intro q h1 h2
    rw [hna, mul_pow, mul_comm (p ^ S)]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right ha (by omega))
      (Nat.pow_le_pow_right hp.pos (by omega))
  have hne : a ^ x.1 * p ^ x.2 ≠ a ^ y.1 * p ^ y.2 := by
    intro heq
    rcases lt_trichotomy x.1 y.1 with hlt | heq1 | hgt
    · exact g71b_inj a p hp ha hapow _ _ _ _ hlt heq.symm
    · rw [heq1] at heq
      have := Nat.eq_of_mul_eq_mul_left (pow_pos ha _) heq
      have := Nat.pow_right_injective hp.two_le this
      exact hxy (Prod.ext heq1 this)
    · exact g71b_inj a p hp ha hapow _ _ _ _ hgt heq
  have hIx : inI n p (a ^ x.1 * p ^ x.2) := ⟨x.1, x.2, rfl⟩
  have hIy : inI n p (a ^ y.1 * p ^ y.2) := ⟨y.1, y.2, rfl⟩
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact ⟨_, _, hl, hbound y hy.1 hy.2, key _ _ hIy hIx hfxy.symm⟩
  · exact ⟨_, _, hl, hbound x hx.1 hx.2, key _ _ hIx hIy hfxy⟩
