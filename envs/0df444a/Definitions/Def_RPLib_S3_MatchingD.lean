-- Prove2me | Definitions.Def_RPLib_S3_MatchingD
-- name    : RPLib_S3_MatchingD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:24:07.919013+00:00
-- url     : https://prove2.me/theorems/b66125f5-be0a-4a98-867b-94065d4808fb
-- title:
--   Weight-two Ramanujan-Petersson library: hyperbolic telescoping
-- statement:
--   Hyperbolic telescoping.
--
--   With `c = p^{k-1}` and `p ∤ M`, the divisor `p^{i+1}` of `p^{m+2}` (weight `min(p^{i+1}, p^{m+1-i}) = p · min(p^i, p^{m-i})`)
--   matches the divisor `p^i` of `p^m` at `δ = p`: the `x`-sums agree under `x ↦ p x (mod M)` (`hypX_shift`).
--   * `hyp_diff`: `hypG1(p^{m+2}, 1) - c · hypG1(p^m, p) = -1/2 (hypX(…, 1) + hypX(…, p^{m+2}))` (exact).
--   * `abs_hyp_diff_le`: `|hypG1(p^{m+2}, 1) - c · hypG1(p^m, p)| ≤ hypB M`; `abs_hypG1_prime_le`: `|hypG1(p, 1)| ≤ hypB M`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_MatchingC

/-!
# S3-Matching, part D: hyperbolic telescoping

With `c = p^{k-1}` and `p ∤ M`, the divisor `p^{i+1}` of `p^{m+2}` (weight `min(p^{i+1}, p^{m+1-i}) = p · min(p^i, p^{m-i})`)
matches the divisor `p^i` of `p^m` at `δ = p`: the `x`-sums agree under `x ↦ p x (mod M)` (`hypX_shift`).
* `hyp_diff`: `hypG1(p^{m+2}, 1) - c · hypG1(p^m, p) = -1/2 (hypX(…, 1) + hypX(…, p^{m+2}))` (exact).
* `abs_hyp_diff_le`: `|hypG1(p^{m+2}, 1) - c · hypG1(p^m, p)| ≤ hypB M`; `abs_hypG1_prime_le`: `|hypG1(p, 1)| ≤ hypB M`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Match

/-- `y ≡ P x (mod M')`, `u P ≡ 1 (mod M')`, `d ∣ M'`: `y ≡ P a (mod d) ↔ x ≡ a (mod d)`. -/
lemma modEq_mul_iff {P d u x y a M' : ℤ} (hd : d ∣ M') (hu : u * P ≡ 1 [ZMOD M'])
    (hy : y ≡ P * x [ZMOD M']) : y ≡ P * a [ZMOD d] ↔ x ≡ a [ZMOD d] := by
  have hu' := hu.of_dvd hd
  have hy' := hy.of_dvd hd
  constructor
  · intro h
    calc x = 1 * x := (one_mul x).symm
      _ ≡ (u * P) * x [ZMOD d] := (hu'.symm).mul_right x
      _ = u * (P * x) := by ring
      _ ≡ u * y [ZMOD d] := (hy'.mul_left u).symm
      _ ≡ u * (P * a) [ZMOD d] := h.mul_left u
      _ = (u * P) * a := by ring
      _ ≡ 1 * a [ZMOD d] := hu'.mul_right a
      _ = a := one_mul a
  · intro h
    exact hy'.trans (h.mul_left P)

variable {M : ℕ} [NeZero M] {p : ℕ}

lemma hypX_shift (hM : 1 < M) (hp : p.Prime) (hpM : ¬ p ∣ M) (k m i : ℕ) (hi : i ≤ m) :
    hypX M k (p ^ (m + 2)) 1 (p ^ (i + 1)) = hypX M k (p ^ m) (p : ZMod M) (p ^ i) := by
  have : Fact (1 < M) := ⟨hM⟩
  have hp0 : 0 < p := hp.pos
  have hdiv1 : p ^ (m + 2) / p ^ (i + 1) = p ^ (m - i + 1) := by
    rw [Nat.pow_div (by omega) hp0]; congr 1; omega
  have hdiv2 : p ^ m / p ^ i = p ^ (m - i) := Nat.pow_div hi hp0
  have hpu : IsUnit (p : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hpM
  set u : ZMod M := (p : ZMod M)⁻¹
  have hup : u * p = 1 := ZMod.inv_mul_of_unit _ hpu
  have hu : ((u.val : ℤ) * p) ≡ 1 [ZMOD (M : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast; rw [ZMod.natCast_zmod_val]; exact hup
  have hy : ∀ x : ℕ, ((((p : ZMod M) * x).val : ℕ) : ℤ) ≡ p * x [ZMOD M] := fun x => by
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast; rw [ZMod.natCast_zmod_val]
  have hx : ∀ y : ℕ, (y : ℤ) ≡ p * (((u * y).val : ℕ) : ℤ) [ZMOD M] := fun y => by
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast
    rw [ZMod.natCast_zmod_val, ← mul_assoc, mul_comm (p : ZMod M) u, hup, one_mul]
  have hpow : ∀ j : ℕ, ((p ^ (j + 1) : ℕ) : ℤ) = p * ((p ^ j : ℕ) : ℤ) := fun j => by push_cast; ring
  unfold hypX
  rw [hdiv1, hdiv2]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  congr 1
  have hτM : (τ : ℤ) ∣ (M : ℤ) := by exact_mod_cast Nat.dvd_of_mem_divisors hτ
  have hτ'M : ((M / τ : ℕ) : ℤ) ∣ (M : ℤ) := by
    exact_mod_cast Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hτ)
  have hLM : ((M / Nat.gcd τ (M / τ) : ℕ) : ℤ) ∣ (M : ℤ) := by
    exact_mod_cast Nat.div_dvd_of_dvd ((Nat.gcd_dvd_left _ _).trans (Nat.dvd_of_mem_divisors hτ))
  symm
  refine Finset.sum_nbij' (fun x => ((p : ZMod M) * x).val) (fun y => (u * y).val) ?_ ?_ ?_ ?_ ?_
  · intro x hx'
    simp only [Finset.mem_filter, Finset.mem_range] at hx' ⊢
    refine ⟨ZMod.val_lt _, ?_, ?_⟩
    · rw [hpow]; exact (modEq_mul_iff hτM hu (hy x)).2 hx'.2.1
    · rw [hpow]; exact (modEq_mul_iff hτ'M hu (hy x)).2 hx'.2.2
  · intro y hy'
    simp only [Finset.mem_filter, Finset.mem_range] at hy' ⊢
    rw [hpow, hpow] at hy'
    refine ⟨ZMod.val_lt _, ?_, ?_⟩
    · exact (modEq_mul_iff hτM hu (hx y)).1 hy'.2.1
    · exact (modEq_mul_iff hτ'M hu (hx y)).1 hy'.2.2
  · intro x hx'
    have hxM : x < M := Finset.mem_range.mp (Finset.mem_filter.mp hx').1
    rw [ZMod.natCast_zmod_val, ← mul_assoc, hup, one_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hxM]
  · intro y hy'
    have hyM : y < M := Finset.mem_range.mp (Finset.mem_filter.mp hy').1
    rw [ZMod.natCast_zmod_val, ← mul_assoc, mul_comm (p : ZMod M) u, hup, one_mul, ZMod.val_natCast,
      Nat.mod_eq_of_lt hyM]
  · intro x _
    rw [ZMod.val_one, Nat.cast_one, one_mul]
    apply charSum_congr
    refine Int.ModEq.of_dvd hLM ?_
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

lemma hyp_weight (hp : p.Prime) (m i : ℕ) (hi : i ≤ m) :
    (if p ^ (i + 1) ≤ p ^ (m + 2) / p ^ (i + 1) then p ^ (i + 1) else p ^ (m + 2) / p ^ (i + 1) : ℕ) =
      p * (if p ^ i ≤ p ^ m / p ^ i then p ^ i else p ^ m / p ^ i : ℕ) := by
  have hdiv1 : p ^ (m + 2) / p ^ (i + 1) = p ^ (m - i + 1) := by
    rw [Nat.pow_div (by omega) hp.pos]; congr 1; omega
  rw [hdiv1, Nat.pow_div hi hp.pos]
  have hiff : p ^ (i + 1) ≤ p ^ (m - i + 1) ↔ p ^ i ≤ p ^ (m - i) := by
    rw [pow_le_pow_iff_right₀ hp.one_lt, pow_le_pow_iff_right₀ hp.one_lt]; omega
  by_cases h : p ^ i ≤ p ^ (m - i)
  · rw [if_pos (hiff.2 h), if_pos h]; ring
  · rw [if_neg (mt hiff.1 h), if_neg h]; ring

lemma hyp_term (hM : 1 < M) (hp : p.Prime) (hpM : ¬ p ∣ M) (k m i : ℕ) (hi : i ≤ m) :
    ((if p ^ (i + 1) ≤ p ^ (m + 2) / p ^ (i + 1) then p ^ (i + 1) else p ^ (m + 2) / p ^ (i + 1) : ℕ) : ℚ) ^ (k - 1) *
        hypX M k (p ^ (m + 2)) 1 (p ^ (i + 1)) =
      (p : ℚ) ^ (k - 1) * (((if p ^ i ≤ p ^ m / p ^ i then p ^ i else p ^ m / p ^ i : ℕ) : ℚ) ^ (k - 1) *
        hypX M k (p ^ m) (p : ZMod M) (p ^ i)) := by
  rw [hyp_weight hp m i hi, hypX_shift hM hp hpM k m i hi]
  push_cast; ring

lemma sum_range_three (f : ℕ → ℚ) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 2 + 1), f i = f 0 + ∑ i ∈ Finset.range (m + 1), f (i + 1) + f (m + 2) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ']; ring

lemma weight_self (n : ℕ) (hn : 1 ≤ n) : (if n ≤ n / n then n else n / n : ℕ) = 1 := by
  rw [Nat.div_self hn]; split_ifs <;> omega

lemma weight_one (p n : ℕ) (hn : 1 ≤ n) : (if p ^ 0 ≤ n / p ^ 0 then p ^ 0 else n / p ^ 0 : ℕ) = 1 := by
  rw [pow_zero, Nat.div_one]; split_ifs <;> omega

/-- **Hyperbolic telescoping** (exact). -/
lemma hyp_diff (hM : 1 < M) (hp : p.Prime) (hpM : ¬ p ∣ M) (k m : ℕ) :
    hypG1 M k (p ^ (m + 2)) 1 - (p : ℚ) ^ (k - 1) * hypG1 M k (p ^ m) (p : ZMod M) =
      -(1 / 2) * (hypX M k (p ^ (m + 2)) 1 (p ^ 0) + hypX M k (p ^ (m + 2)) 1 (p ^ (m + 2))) := by
  rw [hypG1_eq, hypG1_eq, Nat.sum_divisors_prime_pow hp, Nat.sum_divisors_prime_pow hp, sum_range_three,
    Finset.sum_congr rfl fun i hi => hyp_term hM hp hpM k m i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),
    ← Finset.mul_sum, weight_one p _ (Nat.one_le_pow _ _ hp.pos), weight_self _ (Nat.one_le_pow _ _ hp.pos)]
  push_cast; ring

lemma abs_hyp_diff_le (hM : 1 < M) (hp : p.Prime) (hpM : ¬ p ∣ M) (k m : ℕ) :
    |hypG1 M k (p ^ (m + 2)) 1 - (p : ℚ) ^ (k - 1) * hypG1 M k (p ^ m) (p : ZMod M)| ≤ hypB M := by
  rw [hyp_diff hM hp hpM k m, abs_mul]
  have h1 := abs_hypX_le M k (p ^ (m + 2)) 1 (p ^ 0)
  have h2 := abs_hypX_le M k (p ^ (m + 2)) 1 (p ^ (m + 2))
  have h3 := abs_add_le (hypX M k (p ^ (m + 2)) 1 (p ^ 0)) (hypX M k (p ^ (m + 2)) 1 (p ^ (m + 2)))
  rw [show |(-(1 / 2) : ℚ)| = 1 / 2 by norm_num]
  linarith

omit [NeZero M] in
lemma abs_hypG1_prime_le (hp : p.Prime) (k : ℕ) (δ : ZMod M) : |hypG1 M k (p ^ 1) δ| ≤ hypB M := by
  rw [hypG1_eq, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_one,
    weight_one p _ (Nat.one_le_pow _ _ hp.pos), weight_self _ (Nat.one_le_pow _ _ hp.pos)]
  push_cast
  rw [one_pow, one_mul, one_mul, abs_mul]
  have h1 := abs_hypX_le M k (p ^ 1) δ (p ^ 0)
  have h2 := abs_hypX_le M k (p ^ 1) δ (p ^ 1)
  have h3 := abs_add_le (hypX M k (p ^ 1) δ (p ^ 0)) (hypX M k (p ^ 1) δ (p ^ 1))
  rw [show |(-(1 / 2) : ℚ)| = 1 / 2 by norm_num]
  linarith

end RamanujanPetersson.S3.Match


