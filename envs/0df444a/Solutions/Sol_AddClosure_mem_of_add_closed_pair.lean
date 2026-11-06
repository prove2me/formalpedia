-- Prove2me | solution 1 for AddClosure.mem_of_add_closed_pair
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-05T20:18:14.392728+00:00
-- url     : https://prove2.me/submissions/d9722cad-f751-47f5-9a7f-43b11a7f4532

import Mathlib

namespace AddClosure

/-- Path lemma: from `s ∈ S`, bounded closure under `+p`, `+q` reaches `s + a p + b q`. -/
theorem mem_add_mul_add_mul {S : Set ℕ} {s p q N : ℕ} (hs : s ∈ S)
    (hP : ∀ x ∈ S, x + p ≤ N → x + p ∈ S) (hQ : ∀ x ∈ S, x + q ≤ N → x + q ∈ S) :
    ∀ a b : ℕ, s + a * p + b * q ≤ N → s + a * p + b * q ∈ S := by
  intro a
  induction a with
  | zero =>
    intro b
    induction b with
    | zero => intro _; simpa using hs
    | succ b ih =>
      intro h
      have h' : s + 0 * p + b * q + q = s + 0 * p + (b + 1) * q := by ring
      rw [← h'] at h ⊢
      exact hQ _ (ih (by omega)) h
  | succ a ih =>
    intro b h
    have h' : s + a * p + b * q + p = s + (a + 1) * p + b * q := by ring
    rw [← h'] at h ⊢
    exact hP _ (ih b (by omega)) h

/-- Coprime representation: if `p, q` are coprime, `0 < p`, and `p * q ≤ k`, then
`k = a p + b q` for some naturals `a, b`. -/
theorem exists_mul_add_mul_of_coprime {p q k : ℕ} (hp : 0 < p) (hc : Nat.Coprime p q)
    (hk : p * q ≤ k) : ∃ a b : ℕ, a * p + b * q = k := by
  have : NeZero p := ⟨hp.ne'⟩
  set b : ℕ := ((k : ZMod p) * (q : ZMod p)⁻¹).val with hb
  have hblt : b < p := ZMod.val_lt _
  have hbq : b * q ≤ k := by
    calc b * q ≤ p * q := Nat.mul_le_mul_right _ hblt.le
      _ ≤ k := hk
  have hmod : ((b * q : ℕ) : ZMod p) = (k : ZMod p) := by
    rw [Nat.cast_mul, hb, ZMod.natCast_zmod_val, mul_assoc, mul_comm ((q : ZMod p)⁻¹),
      ZMod.coe_mul_inv_eq_one q hc.symm, mul_one]
  have hdvd : p ∣ k - b * q := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hbq, hmod, sub_self]
  obtain ⟨a, ha⟩ := hdvd
  exact ⟨a, b, by rw [mul_comm a p, ← ha]; omega⟩

/-- Two-generator closure (bounded Frobenius form). Let `S ⊆ ℕ` contain `s` and be closed under
adding `p` and adding `q` whenever the result is at most `N`, with `p > 0`. Then every `m` with
`s + p q ≤ m ≤ N` and `gcd(p, q) ∣ m - s` lies in `S`. -/
theorem mem_of_add_closed_pair {S : Set ℕ} {s p q N : ℕ} (hp : 0 < p)
    (hs : s ∈ S) (hP : ∀ x ∈ S, x + p ≤ N → x + p ∈ S)
    (hQ : ∀ x ∈ S, x + q ≤ N → x + q ∈ S) {m : ℕ} (hm : s + p * q ≤ m) (hmN : m ≤ N)
    (hg : Nat.gcd p q ∣ m - s) : m ∈ S := by
  set g := Nat.gcd p q with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left q hp
  obtain ⟨p', hp'⟩ : g ∣ p := Nat.gcd_dvd_left p q
  obtain ⟨q', hq'⟩ : g ∣ q := Nat.gcd_dvd_right p q
  obtain ⟨k, hk⟩ := hg
  have hp'0 : 0 < p' := by
    rcases Nat.eq_zero_or_pos p' with h | h
    · rw [h, mul_zero] at hp'; omega
    · exact h
  have hcop : Nat.Coprime p' q' := by
    have := Nat.coprime_div_gcd_div_gcd (m := p) (n := q) hg0
    rwa [← hgdef, hp', hq', Nat.mul_div_cancel_left _ hg0,
      Nat.mul_div_cancel_left _ hg0] at this
  have hkge : p' * q' ≤ k := by
    have h1 : g * (g * (p' * q')) ≤ g * k := by
      have : p * q = g * (g * (p' * q')) := by rw [hp', hq']; ring
      rw [← this, ← hk]; omega
    have h2 := Nat.le_of_mul_le_mul_left h1 hg0
    calc p' * q' ≤ g * (p' * q') := Nat.le_mul_of_pos_left _ hg0
      _ ≤ k := h2
  obtain ⟨a, b, hab⟩ := exists_mul_add_mul_of_coprime hp'0 hcop hkge
  have hrep : m = s + a * p + b * q := by
    have : a * p + b * q = m - s := by
      rw [hk, ← hab, hp', hq']; ring
    omega
  rw [hrep] at hmN ⊢
  exact mem_add_mul_add_mul hs hP hQ a b hmN

end AddClosure

open AddClosure in
theorem solution {S : Set ℕ} {s p q N : ℕ} (hp : 0 < p)
    (hs : s ∈ S) (hP : ∀ x ∈ S, x + p ≤ N → x + p ∈ S)
    (hQ : ∀ x ∈ S, x + q ≤ N → x + q ∈ S) {m : ℕ} (hm : s + p * q ≤ m) (hmN : m ≤ N)
    (hg : Nat.gcd p q ∣ m - s) : m ∈ S :=
  AddClosure.mem_of_add_closed_pair hp hs hP hQ hm hmN hg
