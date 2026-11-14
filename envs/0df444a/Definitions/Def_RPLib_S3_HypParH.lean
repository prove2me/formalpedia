-- Prove2me | Definitions.Def_RPLib_S3_HypParH
-- name    : RPLib_S3_HypParH
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:32:40.32249+00:00
-- url     : https://prove2.me/theorems/7542507b-230b-44da-a969-6927bd90c8b0
-- title:
--   The Eichler-Selberg trace formula, hyperbolic part H: arithmetic lemmas
-- statement:
--   The character sum $\sum_{\chi(-1) = \varepsilon} \chi(z) = \frac{\varphi(L)}{2}([L \mid z - 1] + \varepsilon [L \mid z + 1])$ for $L \ge 1$, $\varepsilon = \pm 1$, $\operatorname{lcm}(\tau, M/\tau) = M/\gcd(\tau, M/\tau)$, $\varphi(g)\varphi(M/g) = \varphi(\tau)\varphi(M/\tau)$ for $g = \gcd(\tau, M/\tau)$, and residue counts.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   T. M. Apostol, Introduction to Analytic Number Theory, Springer 1976, Chapters 2 and 6

import Mathlib
import Definitions.Def_RPLib_S3_HypParG

/-!
# S3-HypParTerms, part H (O8, steps H2-H4): arithmetic for the `hypG1` match

* `charSum_eq`: for `L ≥ 1`, `ε = ±1`, `charSum L z ε = φ(L)/2 ([L ∣ z - 1] + ε [L ∣ z + 1])`.
* `lcm_div_eq`, `intDvd_lcm_iff`: `lcm(τ, M/τ) = M / gcd(τ, M/τ)` and `lcm ∣ y ↔ τ ∣ y ∧ M/τ ∣ y`.
* `totient_gcd_mul_totient_div`: `φ(g) φ(M/g) = φ(τ) φ(M/τ)` for `g = gcd(τ, M/τ)`.
* `card_residue`: `#{x < M : L ∣ x - c} = M / L` for `L ∣ M`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

section ArithH

lemma gcd_two_eq_one_iff (z : ℤ) : Int.gcd z 2 = 1 ↔ (2 : ℤ) ∣ z - 1 := by
  rcases Int.emod_two_eq_zero_or_one z with h | h
  · have hz : z = 2 * (z / 2) := by omega
    constructor
    · intro hg
      obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.2 hg
      exfalso
      have h2 : (2 : ℤ) ∣ 1 := ⟨u * (z / 2) + v, by rw [← huv]; nth_rewrite 1 [hz]; ring⟩
      norm_num at h2
    · intro hd
      exfalso
      omega
  · constructor
    · intro _
      omega
    · intro _
      exact Int.isCoprime_iff_gcd_eq_one.1 ⟨1, -(z / 2), by omega⟩

/-- **H2.** Closed form of `charSum` for `ε = ±1`, valid for every level `L ≥ 1`. -/
lemma charSum_eq (L : ℕ) (hL : 1 ≤ L) (z ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    S3.charSum L z ε = (Nat.totient L : ℚ) / 2 *
      ((if (L : ℤ) ∣ z - 1 then 1 else 0) + ε * (if (L : ℤ) ∣ z + 1 then 1 else 0)) := by
  unfold S3.charSum
  by_cases h2 : L ≤ 2
  · rw [if_pos h2]
    interval_cases L
    · rcases hε with rfl | rfl <;> norm_num
    · have k2 : (2 : ℤ) ∣ z + 1 ↔ (2 : ℤ) ∣ z - 1 := by
        constructor <;> intro h <;> omega
      simp only [Nat.cast_ofNat, Nat.totient_two, gcd_two_eq_one_iff, k2]
      by_cases hz : (2 : ℤ) ∣ z - 1 <;> rcases hε with rfl | rfl <;> simp [hz] <;> norm_num
  · rw [if_neg h2]
    have hL0 : (L : ℤ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
    have e1 : ((z : ZMod L) = 1) ↔ (L : ℤ) ∣ z - 1 := by
      rw [show (1 : ZMod L) = ((1 : ℤ) : ZMod L) by simp, ZMod.intCast_eq_intCast_iff_dvd_sub,
        ← dvd_neg, neg_sub]
    have e2 : ((z : ZMod L) = -1) ↔ (L : ℤ) ∣ z + 1 := by
      rw [show (-1 : ZMod L) = ((-1 : ℤ) : ZMod L) by simp, ZMod.intCast_eq_intCast_iff_dvd_sub,
        ← dvd_neg, show -(-1 - z) = z + 1 by ring]
    simp only [e1, e2]

/-- `lcm(τ, M/τ) = M / gcd(τ, M/τ)`. -/
lemma lcm_div_eq {M τ : ℕ} (hτ : τ ∣ M) : Nat.lcm τ (M / τ) = M / Nat.gcd τ (M / τ) := by
  unfold Nat.lcm
  rw [Nat.mul_div_cancel' hτ]

lemma intDvd_lcm_iff (a b : ℕ) (y : ℤ) :
    ((Nat.lcm a b : ℕ) : ℤ) ∣ y ↔ (a : ℤ) ∣ y ∧ (b : ℤ) ∣ y := by
  simp only [Int.natCast_dvd, Nat.lcm_dvd_iff]

/-- **H4.** `φ(gcd(τ, M/τ)) φ(M / gcd(τ, M/τ)) = φ(τ) φ(M/τ)`. -/
lemma totient_gcd_mul_totient_div {M τ : ℕ} (hM : 0 < M) (hτ : τ ∣ M) :
    Nat.totient (Nat.gcd τ (M / τ)) * Nat.totient (M / Nat.gcd τ (M / τ)) =
      Nat.totient τ * Nat.totient (M / τ) := by
  have hτM : τ * (M / τ) = M := Nat.mul_div_cancel' hτ
  have hτ0 : 0 < τ := Nat.pos_of_dvd_of_pos hτ hM
  have hg0 : 0 < Nat.gcd τ (M / τ) := Nat.gcd_pos_of_pos_left _ hτ0
  have hgM : Nat.gcd τ (M / τ) ∣ M := (Nat.gcd_dvd_left _ _).trans hτ
  have hgL : Nat.gcd τ (M / τ) ∣ M / Nat.gcd τ (M / τ) := by
    rw [← lcm_div_eq hτ]
    exact (Nat.gcd_dvd_left _ _).trans (Nat.dvd_lcm_left _ _)
  have h1 := Nat.totient_gcd_mul_totient_mul τ (M / τ)
  rw [hτM] at h1
  have h2 := Nat.totient_gcd_mul_totient_mul (M / Nat.gcd τ (M / τ)) (Nat.gcd τ (M / τ))
  rw [Nat.gcd_eq_right hgL, Nat.div_mul_cancel hgM] at h2
  have h3 : (Nat.totient (M / Nat.gcd τ (M / τ)) * Nat.totient (Nat.gcd τ (M / τ))) * Nat.gcd τ (M / τ) =
      (Nat.totient τ * Nat.totient (M / τ)) * Nat.gcd τ (M / τ) := by
    rw [← h2, h1]
  have h4 := Nat.eq_of_mul_eq_mul_right hg0 h3
  rw [mul_comm]
  exact h4

/-- Residue count: `#{x < M : L ∣ x - c} = M / L` for `L ∣ M`. -/
lemma card_residue {M L : ℕ} (hM : 0 < M) (hL : L ∣ M) (c : ℤ) :
    ((range M).filter fun x : ℕ => (L : ℤ) ∣ (x : ℤ) - c).card = M / L := by
  have hL0 : 0 < L := Nat.pos_of_dvd_of_pos hL hM
  have e : range M = range (M / L * L) := by rw [Nat.div_mul_cancel hL]
  rw [e, card_filter_range_periodic (fun x : ℕ => (L : ℤ) ∣ (x : ℤ) - c) L ?_ (M / L)]
  · have hc0 : 0 ≤ c % (L : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hL0.ne')
    have hc1 : c % (L : ℤ) < L := Int.emod_lt_of_pos _ (by exact_mod_cast hL0)
    have h1 : ((range L).filter fun x : ℕ => (L : ℤ) ∣ (x : ℤ) - c) = {(c % (L : ℤ)).toNat} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hd⟩
        have hmod : c % (L : ℤ) = (x : ℤ) % L := Int.modEq_iff_dvd.2 hd
        have hx' : (x : ℤ) % (L : ℤ) = x :=
          Int.emod_eq_of_lt (Int.natCast_nonneg x) (by exact_mod_cast hx)
        rw [hx'] at hmod
        rw [hmod, Int.toNat_natCast]
      · rintro rfl
        constructor
        · have h5 := Int.toNat_of_nonneg hc0
          generalize c % (L : ℤ) = r at hc0 hc1 h5 ⊢
          omega
        · rw [Int.toNat_of_nonneg hc0, Int.emod_def]
          exact ⟨-(c / L), by ring⟩
    rw [h1, Finset.card_singleton, mul_one]
  · intro x
    show (L : ℤ) ∣ ((x + L : ℕ) : ℤ) - c ↔ (L : ℤ) ∣ (x : ℤ) - c
    rw [show ((x + L : ℕ) : ℤ) - c = ((x : ℤ) - c) + L by push_cast; ring]
    exact dvd_add_self_right

end ArithH

end RamanujanPetersson.HypPar


