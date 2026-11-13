-- Prove2me | Definitions.Def_RPLib_S1_HeckeAlgebra
-- name    : RPLib_S1_HeckeAlgebra
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:23:40.809193+00:00
-- url     : https://prove2.me/theorems/cb7ccb55-5ca6-4a9b-ac2c-f5c1cf78c17d
-- title:
--   Commutation of Hecke operators, the operators $T_n$, and their coefficient formula
-- statement:
--   The Hecke operators $T_p$ and $U_p$ on $S_k(\Gamma_1(M))$ commute pairwise. With $T_n$ defined multiplicatively from prime powers via $T_{p^{r+1}} = T_pT_{p^r} - p^{k-1}\langle p\rangle T_{p^{r-1}}$, one has for $f \in S_k(M,\chi)$ $$a_m(T_n f) = \sum_{d \mid \gcd(m,n),\ (d,M)=1} \chi(d)\, d^{k-1}\, a_{mn/d^2}(f),$$ in particular $a_1(T_n f) = a_n(f)$. The file also proves compatibility of $T_p$ and the diamond operators with the level-raising maps for $p \nmid M$.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 5.3 (Proposition 5.3.1)

import Mathlib
import Definitions.Def_RPLib_S1_Hecke
import Definitions.Def_RPLib_S1_Level

/-!
# S1-HALG: Hecke algebra relations, `T_n`, level-map compatibility (coefficient method)

(A) formal operators on coefficient sequences (`tP`, `tPow`, `tN`); (B) `T_p T_q = T_q T_p`, `T_n`,
the coefficient formula on `S_k(M, χ)`; (C) compatibility with `incl` and `ι_e`; (D) eigen corollaries.
-/

open UpperHalfPlane ModularForm MatrixGroups CongruenceSubgroup
open scoped Pointwise

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HeckeAlgebra

open RamanujanPetersson.Diamond RamanujanPetersson.QExp RamanujanPetersson.Hecke

/-! ## (A) Formal operators on coefficient sequences -/

section formal

/-- `T_p` on sequences: `n ↦ a(pn) + c [p ∣ n] a(n/p)`. -/
def tP (p : ℕ) (c : ℂ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (p * n) + c * (if p ∣ n then a (n / p) else 0)

lemma ite_add_zero' {P : Prop} [Decidable P] (x y : ℂ) :
    (if P then x + y else 0) = (if P then x else 0) + (if P then y else 0) := by
  split_ifs <;> simp

lemma ite_mul_zero' {P : Prop} [Decidable P] (e y : ℂ) :
    (if P then e * y else 0) = e * (if P then y else 0) := by
  split_ifs <;> simp

lemma ite_dvd_mul_div {p q : ℕ} (hqp : q.Coprime p) (b : ℕ → ℂ) (n : ℕ) :
    (if q ∣ p * n then b (p * n / q) else 0) = if q ∣ n then b (p * (n / q)) else 0 := by
  by_cases h : q ∣ n
  · rw [if_pos (dvd_mul_of_dvd_right h p), if_pos h, Nat.mul_div_assoc p h]
  · rw [if_neg h, if_neg (fun h' => h (hqp.dvd_of_dvd_mul_left h'))]

lemma ite_dvd_div_div (p q : ℕ) (b : ℕ → ℂ) (n : ℕ) :
    (if p ∣ n then (if q ∣ n / p then b (n / p / q) else 0) else 0) =
      if p * q ∣ n then b (n / (p * q)) else 0 := by
  by_cases h : p ∣ n
  · rw [if_pos h, Nat.div_div_eq_div_mul]
    by_cases h2 : p * q ∣ n
    · rw [if_pos ((Nat.dvd_div_iff_mul_dvd h).2 h2), if_pos h2]
    · rw [if_neg (fun h3 => h2 ((Nat.dvd_div_iff_mul_dvd h).1 h3)), if_neg h2]
  · rw [if_neg h, if_neg (fun h2 => h (dvd_of_mul_right_dvd h2))]

theorem tP_comm {p q : ℕ} (hpq : p.Coprime q) (c d : ℂ) (a : ℕ → ℂ) (n : ℕ) :
    tP p c (tP q d a) n = tP q d (tP p c a) n := by
  simp only [tP, ite_add_zero', ite_mul_zero', ite_dvd_mul_div hpq.symm a n,
    ite_dvd_mul_div hpq a n, ite_dvd_div_div p q a n, ite_dvd_div_div q p a n]
  simp only [mul_comm q p, mul_left_comm q p n]
  ring

/-- Closed form of `T_{p^r}` on sequences: `Σ_{i ≤ r} [p^i ∣ n] c^i a(n/p^i · p^(r-i))`. -/
def tPow (p : ℕ) (c : ℂ) (r : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (r + 1), if p ^ i ∣ n then c ^ i * a (n / p ^ i * p ^ (r - i)) else 0

lemma tPow_zero (p : ℕ) (c : ℂ) (a : ℕ → ℂ) (n : ℕ) : tPow p c 0 a n = a n := by
  simp [tPow]

lemma tPow_one (p : ℕ) (c : ℂ) (a : ℕ → ℂ) (n : ℕ) : tPow p c 1 a n = tP p c a n := by
  rw [tPow, Finset.sum_range_succ, Finset.sum_range_one, tP]
  simp only [pow_zero, one_dvd, ↓reduceIte, Nat.div_one, pow_one, one_mul, Nat.sub_zero,
    Nat.sub_self, mul_one]
  rw [mul_comm n p, mul_ite, mul_zero]

theorem tPow_succ_succ {p : ℕ} (hp : 0 < p) (c : ℂ) (a : ℕ → ℂ) (r n : ℕ) :
    tPow p c (r + 2) a n = tP p c (tPow p c (r + 1) a) n - c * tPow p c r a n := by
  have hA : tPow p c (r + 1) a (p * n) = c * tPow p c r a n + a (n * p ^ (r + 2)) := by
    rw [tPow, Finset.sum_range_succ', tPow, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : p ^ i ∣ n
      · rw [if_pos (by rw [pow_succ' p i]; exact Nat.mul_dvd_mul_left p h), if_pos h, pow_succ' p i,
          Nat.mul_div_mul_left n (p ^ i) hp, show r + 1 - (i + 1) = r - i by omega]
        ring
      · rw [if_neg (fun h' => h (by rw [pow_succ' p i] at h'; exact (Nat.mul_dvd_mul_iff_left hp).1 h')),
          if_neg h, mul_zero]
    · simp only [pow_zero, one_dvd, ↓reduceIte, one_mul, Nat.div_one, Nat.sub_zero]
      congr 1
      ring
  have hB : (if p ∣ n then tPow p c (r + 1) a (n / p) else 0) =
      ∑ i ∈ Finset.range (r + 2),
        if p ^ (i + 1) ∣ n then c ^ i * a (n / p ^ (i + 1) * p ^ (r + 1 - i)) else 0 := by
    by_cases hpn : p ∣ n
    · rw [if_pos hpn, tPow]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : p ^ (i + 1) ∣ n
      · rw [if_pos ((Nat.dvd_div_iff_mul_dvd hpn).2 (by rwa [← pow_succ'])), if_pos h,
          Nat.div_div_eq_div_mul, ← pow_succ']
      · rw [if_neg (fun h' => h (by rw [pow_succ']; exact (Nat.dvd_div_iff_mul_dvd hpn).1 h')),
          if_neg h]
    · rw [if_neg hpn]
      symm
      exact Finset.sum_eq_zero fun i _ =>
        if_neg (fun h => hpn (dvd_trans (dvd_pow_self p (Nat.succ_ne_zero i)) h))
  have hC : tPow p c (r + 2) a n = c * (∑ i ∈ Finset.range (r + 2),
        if p ^ (i + 1) ∣ n then c ^ i * a (n / p ^ (i + 1) * p ^ (r + 1 - i)) else 0) +
      a (n * p ^ (r + 2)) := by
    rw [tPow, Finset.sum_range_succ', Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [show r + 2 - (i + 1) = r + 1 - i by omega]
      split_ifs <;> ring
    · simp only [pow_zero, one_dvd, ↓reduceIte, one_mul, Nat.div_one, Nat.sub_zero]
  rw [hC, tP, hA, hB]
  ring

/-- The `T_n` coefficient operator: `m ↦ Σ_{d ∣ gcd(m,n)} w(d) a(mn/d²)`. -/
def tN (w : ℕ → ℂ) (n : ℕ) (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ d ∈ (Nat.gcd m n).divisors, w d * a (m * n / d ^ 2)

lemma tN_of_coprime {w : ℕ → ℂ} (hw1 : w 1 = 1) {m n : ℕ} (h : m.Coprime n) (a : ℕ → ℂ) :
    tN w n a m = a (m * n) := by
  rw [tN, show Nat.gcd m n = 1 from h]
  simp [hw1]

lemma tN_one {w : ℕ → ℂ} (hw1 : w 1 = 1) (a : ℕ → ℂ) (m : ℕ) : tN w 1 a m = a m := by
  rw [tN_of_coprime hw1 (Nat.coprime_one_right m), mul_one]

theorem tPow_eq_tN {w : ℕ → ℂ} {p : ℕ} (hp : p.Prime) (hw : ∀ i, w (p ^ i) = w p ^ i)
    (r : ℕ) (a : ℕ → ℂ) (m : ℕ) : tN w (p ^ r) a m = tPow p (w p) r a m := by
  obtain ⟨j, hjr, hj⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right m (p ^ r))
  have key : ∀ i, i ≤ r → (p ^ i ∣ m ↔ i ≤ j) := by
    intro i hi
    rw [← Nat.pow_dvd_pow_iff_le_right hp.one_lt, ← hj, Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨h, Nat.pow_dvd_pow p hi⟩, fun h => h.1⟩
  have hfilt : (Finset.range (r + 1)).filter (fun i => p ^ i ∣ m) = Finset.range (j + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hd⟩
      have := (key i (by omega)).1 hd
      omega
    · intro hi
      exact ⟨by omega, (key i (by omega)).2 (by omega)⟩
  rw [tN, hj, Nat.sum_divisors_prime_pow hp, tPow, ← Finset.sum_filter]
  symm
  refine Finset.sum_congr hfilt fun i hi => ?_
  have hij : i ≤ j := by simp only [Finset.mem_range] at hi; omega
  have hir : i ≤ r := le_trans hij hjr
  obtain ⟨m', rfl⟩ := (key i hir).2 hij
  have hpi : 0 < p ^ i := pow_pos hp.pos i
  have hr : p ^ r = p ^ i * p ^ (r - i) := by rw [← pow_add, Nat.add_sub_cancel' hir]
  rw [hw, hr, show p ^ i * m' * (p ^ i * p ^ (r - i)) = (p ^ i) ^ 2 * (m' * p ^ (r - i)) by ring,
    Nat.mul_div_cancel_left _ (pow_pos hpi 2), Nat.mul_div_cancel_left _ hpi]

lemma sum_divisors_mul_coprime {m n : ℕ} (h : m.Coprime n) (F : ℕ → ℂ) :
    ∑ d ∈ (m * n).divisors, F d = ∑ d1 ∈ m.divisors, ∑ d2 ∈ n.divisors, F (d1 * d2) := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image h.mul_injOn_divisors, Finset.sum_product]

lemma gcd_div_sq {x m n d : ℕ} (hd : 0 < d) (h1x : d ∣ x) (h1m : d ∣ m) (hmn : m.Coprime n) :
    Nat.gcd (x * m / d ^ 2) n = Nat.gcd x n := by
  obtain ⟨x', rfl⟩ := h1x
  obtain ⟨m', rfl⟩ := h1m
  have hdn : d.Coprime n := hmn.coprime_dvd_left (dvd_mul_right d m')
  have hm'n : m'.Coprime n := hmn.coprime_dvd_left (dvd_mul_left m' d)
  rw [show d * x' * (d * m') = d ^ 2 * (x' * m') by ring, Nat.mul_div_cancel_left _ (pow_pos hd 2),
    Nat.Coprime.gcd_mul_right_cancel x' hm'n, Nat.Coprime.gcd_mul_left_cancel x' hdn]

lemma idx_mul {x m n d1 d2 : ℕ} (hd1 : 0 < d1) (hd2 : 0 < d2) (h1x : d1 ∣ x) (h1m : d1 ∣ m)
    (h2x : d2 ∣ x) (h2n : d2 ∣ n) (hc : d1.Coprime d2) :
    x * m / d1 ^ 2 * n / d2 ^ 2 = x * (m * n) / (d1 * d2) ^ 2 := by
  obtain ⟨x', rfl⟩ := hc.mul_dvd_of_dvd_of_dvd h1x h2x
  obtain ⟨m', rfl⟩ := h1m
  obtain ⟨n', rfl⟩ := h2n
  rw [show d1 * d2 * x' * (d1 * m') = d1 ^ 2 * (d2 * x' * m') by ring,
    Nat.mul_div_cancel_left _ (pow_pos hd1 2),
    show d2 * x' * m' * (d2 * n') = d2 ^ 2 * (x' * m' * n') by ring,
    Nat.mul_div_cancel_left _ (pow_pos hd2 2),
    show d1 * d2 * x' * (d1 * m' * (d2 * n')) = (d1 * d2) ^ 2 * (x' * m' * n') by ring,
    Nat.mul_div_cancel_left _ (pow_pos (Nat.mul_pos hd1 hd2) 2)]

theorem tN_mul {w : ℕ → ℂ} (hw : ∀ d e, w (d * e) = w d * w e) {m n : ℕ} (hmn : m.Coprime n)
    (a : ℕ → ℂ) (x : ℕ) : tN w m (tN w n a) x = tN w (m * n) a x := by
  have hg : Nat.gcd x (m * n) = Nat.gcd x m * Nat.gcd x n := Nat.Coprime.gcd_mul x hmn
  have hc : (Nat.gcd x m).Coprime (Nat.gcd x n) :=
    (hmn.coprime_dvd_left (Nat.gcd_dvd_right x m)).coprime_dvd_right (Nat.gcd_dvd_right x n)
  unfold tN
  rw [hg, sum_divisors_mul_coprime hc]
  refine Finset.sum_congr rfl fun d1 hd1 => ?_
  have hd1' := Nat.dvd_of_mem_divisors hd1
  have h1x : d1 ∣ x := hd1'.trans (Nat.gcd_dvd_left x m)
  have h1m : d1 ∣ m := hd1'.trans (Nat.gcd_dvd_right x m)
  have hp1 : 0 < d1 := Nat.pos_of_mem_divisors hd1
  rw [gcd_div_sq hp1 h1x h1m hmn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d2 hd2 => ?_
  have hd2' := Nat.dvd_of_mem_divisors hd2
  have h2x : d2 ∣ x := hd2'.trans (Nat.gcd_dvd_left x n)
  have h2n : d2 ∣ n := hd2'.trans (Nat.gcd_dvd_right x n)
  have hp2 : 0 < d2 := Nat.pos_of_mem_divisors hd2
  have hc12 : d1.Coprime d2 := (hmn.coprime_dvd_left h1m).coprime_dvd_right h2n
  rw [hw, idx_mul hp1 hp2 h1x h1m h2x h2n hc12]
  ring

end formal

/-! ## (B) Operators on `S_k(Γ₁(M))` -/

section forms

variable {M : ℕ}

variable (M) in
/-- The width-1 coefficient sequence as a linear map. -/
def csL (k : ℤ) : S1 M k →ₗ[ℂ] (ℕ → ℂ) :=
  LinearMap.pi fun n => (PowerSeries.coeff n).comp (qExpansionGamma1 M k)

lemma csL_apply (k : ℤ) (f : S1 M k) (n : ℕ) : csL M k f n = (qExpansion 1 f).coeff n := rfl

lemma eq_of_csL (k : ℤ) {f g : S1 M k} (h : csL M k f = csL M k g) : f = g :=
  qExpansionGamma1_injective M k (PowerSeries.ext fun n => congrFun h n)

variable [NeZero M]

theorem ext_chi (k : ℤ) {S T : Module.End ℂ (S1 M k)}
    (h : ∀ χ : DirichletCharacter ℂ M, ∀ f ∈ chiSubspace k χ, S f = T f) : S = T := by
  refine LinearMap.ext fun f => ?_
  rw [← sum_proj k f, map_sum, map_sum]
  exact Finset.sum_congr rfl fun χ _ => h χ _ (proj_mem k χ f)

lemma csL_heckeT_chi (k : ℤ) {p : ℕ} [Fact p.Prime] {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) :
    csL M k (heckeT p k f) = tP p (χ p * (p : ℂ) ^ (k - 1)) (csL M k f) :=
  funext fun n => coeff_heckeT_chi (p := p) k hf n

/-- `T_p` for every `p` (`U_p` when `p ∣ M`), and `1` when `p` is not prime. -/
def heckeTP (k : ℤ) (p : ℕ) : Module.End ℂ (S1 M k) :=
  if hp : p.Prime then haveI : Fact p.Prime := ⟨hp⟩; heckeT p k else 1

lemma heckeTP_eq (k : ℤ) (p : ℕ) [hp : Fact p.Prime] : heckeTP (M := M) k p = heckeT p k := by
  rw [heckeTP, dif_pos hp.out]

lemma heckeTP_of_not_prime (k : ℤ) {p : ℕ} (hp : ¬ p.Prime) : heckeTP (M := M) k p = 1 := by
  rw [heckeTP, dif_neg hp]

/-- The correction term `[p ∤ M] p^(k-1) ⟨p⟩` of the `T_{p^r}` recursion. -/
def heckeCorr (k : ℤ) (p : ℕ) : Module.End ℂ (S1 M k) :=
  if h : p.Coprime M then ((p : ℂ) ^ (k - 1)) • diamond k (ZMod.unitOfCoprime p h) else 0

lemma heckeCorr_chi (k : ℤ) (p : ℕ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) : heckeCorr k p f = (χ p * (p : ℂ) ^ (k - 1)) • f := by
  unfold heckeCorr
  split_ifs with h
  · rw [LinearMap.smul_apply, (mem_chiSubspace_iff_diamond k χ f).1 hf, ZMod.coe_unitOfCoprime,
      smul_smul, mul_comm ((p : ℂ) ^ (k - 1))]
  · have : χ (p : ZMod M) = 0 :=
      MulChar.map_nonunit χ (fun hu => h ((ZMod.isUnit_iff_coprime p M).1 hu))
    rw [LinearMap.zero_apply, this, zero_mul, zero_smul]

lemma heckeTP_commute_diamond (k : ℤ) (p : ℕ) (d : (ZMod M)ˣ) :
    Commute (heckeTP k p) (diamond k d) := by
  by_cases hp : p.Prime
  · haveI := Fact.mk hp
    rw [heckeTP_eq]
    exact heckeT_commute_diamond k d
  · rw [heckeTP_of_not_prime k hp]
    exact Commute.one_left _

lemma heckeCorr_commute_diamond (k : ℤ) (p : ℕ) (d : (ZMod M)ˣ) :
    Commute (heckeCorr k p) (diamond k d) := by
  unfold heckeCorr
  split_ifs with h
  · exact (diamond_commute k _ d).smul_left _
  · exact Commute.zero_left _

lemma heckeTP_commute_heckeCorr (k : ℤ) (p q : ℕ) : Commute (heckeTP (M := M) k p) (heckeCorr k q) := by
  unfold heckeCorr
  split_ifs with h
  · exact (heckeTP_commute_diamond k p _).smul_right _
  · exact Commute.zero_right _

lemma heckeCorr_commute (k : ℤ) (p q : ℕ) : Commute (heckeCorr (M := M) k p) (heckeCorr k q) := by
  unfold heckeCorr
  split_ifs with h1 h2 h2
  · exact ((diamond_commute k _ _).smul_left _).smul_right _
  · exact Commute.zero_right _
  · exact Commute.zero_left _
  · exact Commute.zero_left _

/-- **`T_p T_q = T_q T_p`** for all `p, q` (including `U_p`, `U_q`). -/
theorem heckeTP_commute (k : ℤ) (p q : ℕ) : Commute (heckeTP (M := M) k p) (heckeTP k q) := by
  by_cases hp : p.Prime
  swap
  · rw [heckeTP_of_not_prime k hp]; exact Commute.one_left _
  by_cases hq : q.Prime
  swap
  · rw [heckeTP_of_not_prime k hq]; exact Commute.one_right _
  by_cases hpq : p = q
  · subst hpq; exact Commute.refl _
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  rw [heckeTP_eq k p, heckeTP_eq k q, Commute, SemiconjBy]
  refine ext_chi k fun χ f hf => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  apply eq_of_csL
  have hp' := heckeT_mem_chiSubspace (p := p) k hf
  have hq' := heckeT_mem_chiSubspace (p := q) k hf
  rw [csL_heckeT_chi (p := p) k hq', csL_heckeT_chi (p := q) k hf, csL_heckeT_chi (p := q) k hp',
    csL_heckeT_chi (p := p) k hf]
  funext n
  exact tP_comm ((Nat.coprime_primes hp hq).2 hpq) _ _ _ n

theorem heckeT_commute (k : ℤ) (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    Commute (heckeT (M := M) p k) (heckeT q k) := by
  rw [← heckeTP_eq, ← heckeTP_eq]
  exact heckeTP_commute k p q

/-- `T_{p^r}` by the recursion `T_{p^(r+2)} = T_p T_{p^(r+1)} - [p ∤ M] p^(k-1) ⟨p⟩ T_{p^r}`. -/
def heckePow (k : ℤ) (p : ℕ) : ℕ → Module.End ℂ (S1 M k)
  | 0 => 1
  | 1 => heckeTP k p
  | r + 2 => heckeTP k p * heckePow k p (r + 1) - heckeCorr k p * heckePow k p r

lemma heckePow_zero (k : ℤ) (p : ℕ) : heckePow (M := M) k p 0 = 1 := rfl

lemma heckePow_one (k : ℤ) (p : ℕ) : heckePow (M := M) k p 1 = heckeTP k p := rfl

lemma heckePow_succ_succ (k : ℤ) (p r : ℕ) : heckePow (M := M) k p (r + 2) =
    heckeTP k p * heckePow k p (r + 1) - heckeCorr k p * heckePow k p r := rfl

theorem commute_heckePow (k : ℤ) (p : ℕ) {X : Module.End ℂ (S1 M k)}
    (h1 : Commute X (heckeTP k p)) (h2 : Commute X (heckeCorr k p)) :
    ∀ r, Commute X (heckePow k p r)
  | 0 => Commute.one_right X
  | 1 => h1
  | r + 2 => by
    rw [heckePow_succ_succ]
    exact (h1.mul_right (commute_heckePow k p h1 h2 (r + 1))).sub_right
      (h2.mul_right (commute_heckePow k p h1 h2 r))

theorem heckePow_commute (k : ℤ) (p q a b : ℕ) :
    Commute (heckePow (M := M) k p a) (heckePow k q b) := by
  refine commute_heckePow (M := M) k q ?_ ?_ b
  · exact (commute_heckePow (M := M) k p (heckeTP_commute k q p)
      (heckeTP_commute_heckeCorr k q p) a).symm
  · exact (commute_heckePow (M := M) k p (heckeTP_commute_heckeCorr k p q).symm
      (heckeCorr_commute k q p) a).symm

lemma diamond_commute_heckePow (k : ℤ) (p r : ℕ) (d : (ZMod M)ˣ) :
    Commute (diamond k d) (heckePow k p r) :=
  commute_heckePow k p (heckeTP_commute_diamond k p d).symm (heckeCorr_commute_diamond k p d).symm r

lemma heckePow_mem_chiSubspace (k : ℤ) (p r : ℕ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) : heckePow k p r f ∈ chiSubspace k χ :=
  map_mem_chiSubspace_of_commute k _ (fun d => (diamond_commute_heckePow k p r d).symm) hf

lemma heckePow_pairwise (k : ℤ) (g : ℕ → ℕ) (s : Finset ℕ) :
    (s : Set ℕ).Pairwise (Function.onFun Commute fun p => heckePow (M := M) k p (g p)) :=
  fun p _ q _ _ => heckePow_commute k p q _ _

/-- **`T_n`** `= Π_{p ∣ n} T_{p^(v_p n)}`. -/
def heckeTn (k : ℤ) (n : ℕ) : Module.End ℂ (S1 M k) :=
  n.primeFactors.noncommProd (fun p => heckePow k p (n.factorization p))
    (heckePow_pairwise k (fun p => n.factorization p) _)

lemma heckeTn_congr_set (k : ℤ) {n : ℕ} {s : Finset ℕ} (hs : n.primeFactors = s) :
    heckeTn (M := M) k n = s.noncommProd (fun p => heckePow k p (n.factorization p))
      (heckePow_pairwise k (fun p => n.factorization p) _) :=
  Finset.noncommProd_congr hs (fun _ _ => rfl) _

theorem heckeTn_one (k : ℤ) : heckeTn (M := M) k 1 = 1 := by
  rw [heckeTn_congr_set k Nat.primeFactors_one, Finset.noncommProd_empty]

theorem heckeTn_prime_pow (k : ℤ) {p r : ℕ} (hp : p.Prime) (hr : r ≠ 0) :
    heckeTn (M := M) k (p ^ r) = heckePow k p r := by
  rw [heckeTn_congr_set k (Nat.primeFactors_prime_pow hr hp), Finset.noncommProd_singleton,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]

theorem heckeTn_prime_pow' (k : ℤ) {p : ℕ} (hp : p.Prime) (r : ℕ) :
    heckeTn (M := M) k (p ^ r) = heckePow k p r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [pow_zero, heckeTn_one, heckePow_zero]
  · exact heckeTn_prime_pow k hp hr.ne'

theorem heckeTn_prime (k : ℤ) {p : ℕ} (hp : p.Prime) : heckeTn (M := M) k p = heckeTP k p := by
  have := heckeTn_prime_pow (M := M) k hp one_ne_zero
  rwa [pow_one] at this

/-- **The recursion** `T_{p^(r+2)} = T_p T_{p^(r+1)} - [p ∤ M] p^(k-1) ⟨p⟩ T_{p^r}`. -/
theorem heckeTn_prime_pow_succ_succ (k : ℤ) {p : ℕ} (hp : p.Prime) (r : ℕ) :
    heckeTn (M := M) k (p ^ (r + 2)) =
      heckeTP k p * heckeTn k (p ^ (r + 1)) - heckeCorr k p * heckeTn k (p ^ r) := by
  rw [heckeTn_prime_pow' k hp, heckeTn_prime_pow' k hp, heckeTn_prime_pow' k hp, heckePow_succ_succ]

lemma heckeCorr_of_not_dvd (k : ℤ) {p : ℕ} [Fact p.Prime] (hpM : ¬ p ∣ M) :
    heckeCorr (M := M) k p = ((p : ℂ) ^ (k - 1)) • diamond k (unitP hpM) := by
  rw [heckeCorr, dif_pos (coprime_of_not_dvd hpM)]

lemma heckeCorr_of_dvd (k : ℤ) {p : ℕ} [hp : Fact p.Prime] (hpM : p ∣ M) :
    heckeCorr (M := M) k p = 0 := by
  rw [heckeCorr, dif_neg (fun h => (Nat.Prime.coprime_iff_not_dvd hp.out).1 h hpM)]

/-- **Multiplicativity** `T_{mn} = T_m T_n` for coprime `m, n`. -/
theorem heckeTn_mul (k : ℤ) {m n : ℕ} (hmn : m.Coprime n) :
    heckeTn (M := M) k (m * n) = heckeTn k m * heckeTn k n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [(Nat.coprime_zero_left n).1 hmn, heckeTn_one, mul_one, mul_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(Nat.coprime_zero_right m).1 hmn, heckeTn_one, one_mul, one_mul]
  rw [heckeTn_congr_set k (Nat.Coprime.primeFactors_mul hmn)]
  refine (Finset.noncommProd_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hmn) _ _).trans ?_
  congr 1
  · refine Finset.noncommProd_congr rfl (fun p hp => ?_) _
    have hpn : ¬ p ∣ n := (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors hp)).1
      (hmn.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp))
    rw [Nat.factorization_mul hm.ne' hn.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpn, add_zero]
  · refine Finset.noncommProd_congr rfl (fun p hp => ?_) _
    have hpm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors hp)).1
      (hmn.symm.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp))
    rw [Nat.factorization_mul hm.ne' hn.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpm, zero_add]

lemma diamond_commute_heckeTn (k : ℤ) (n : ℕ) (d : (ZMod M)ˣ) :
    Commute (diamond k d) (heckeTn k n) :=
  Finset.noncommProd_commute _ _ _ _ fun p _ => diamond_commute_heckePow k p _ d

lemma heckeTn_mem_chiSubspace (k : ℤ) (n : ℕ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) : heckeTn k n f ∈ chiSubspace k χ :=
  map_mem_chiSubspace_of_commute k _ (fun d => (diamond_commute_heckeTn k n d).symm) hf

/-- The completely multiplicative weight `d ↦ χ(d) d^(k-1)`. -/
def wt (χ : DirichletCharacter ℂ M) (k : ℤ) (d : ℕ) : ℂ := χ d * (d : ℂ) ^ (k - 1)

lemma wt_mul (χ : DirichletCharacter ℂ M) (k : ℤ) (d e : ℕ) : wt χ k (d * e) = wt χ k d * wt χ k e := by
  simp only [wt, Nat.cast_mul, map_mul, mul_zpow]
  ring

lemma wt_one (χ : DirichletCharacter ℂ M) (k : ℤ) : wt χ k 1 = 1 := by simp [wt]

lemma wt_pow (χ : DirichletCharacter ℂ M) (k : ℤ) (p : ℕ) : ∀ i, wt χ k (p ^ i) = wt χ k p ^ i
  | 0 => by rw [pow_zero, pow_zero, wt_one]
  | i + 1 => by rw [pow_succ, wt_mul, wt_pow χ k p i, pow_succ]

theorem csL_heckePow_chi (k : ℤ) {p : ℕ} (hp : p.Prime) {χ : DirichletCharacter ℂ M}
    {f : S1 M k} (hf : f ∈ chiSubspace k χ) :
    ∀ r, csL M k (heckePow k p r f) = tPow p (χ p * (p : ℂ) ^ (k - 1)) r (csL M k f)
  | 0 => funext fun n => (tPow_zero _ _ _ n).symm
  | 1 => by
    haveI := Fact.mk hp
    funext n
    rw [tPow_one, heckePow_one, heckeTP_eq, csL_heckeT_chi k hf]
  | r + 2 => by
    haveI := Fact.mk hp
    have h1 := heckePow_mem_chiSubspace k p (r + 1) hf
    have h0 := heckePow_mem_chiSubspace k p r hf
    rw [heckePow_succ_succ, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      heckeTP_eq, heckeCorr_chi k p h0, map_sub, map_smul, csL_heckeT_chi k h1,
      csL_heckePow_chi k hp hf (r + 1), csL_heckePow_chi k hp hf r]
    funext n
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, tPow_succ_succ hp.pos]

/-- The coefficients of `T_n f` for `f ∈ S_k(M, χ)`, as sequences. -/
theorem csL_heckeTn_chi (k : ℤ) (χ : DirichletCharacter ℂ M) :
    ∀ n, 0 < n → ∀ f ∈ chiSubspace k χ, csL M k (heckeTn k n f) = tN (wt χ k) n (csL M k f) := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p r hp hr =>
    intro _ f hf
    rw [heckeTn_prime_pow k hp hr.ne', csL_heckePow_chi k hp hf r]
    funext m
    exact (tPow_eq_tN hp (wt_pow χ k p) r _ m).symm
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ f _
    rw [heckeTn_one]
    funext m
    exact (tN_one (wt_one χ k) _ m).symm
  | coprime a b ha hb hab iha ihb =>
    intro _ f hf
    rw [heckeTn_mul k hab, Module.End.mul_apply, iha (by omega) _ (heckeTn_mem_chiSubspace k b hf),
      ihb (by omega) f hf]
    funext m
    exact tN_mul (wt_mul χ k) hab _ m

/-- **Coefficient formula on `S_k(M, χ)`**: `a_m(T_n f) = Σ_{d ∣ (m,n)} χ(d) d^(k-1) a(mn/d²)`. -/
theorem coeff_heckeTn_chi (k : ℤ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) {n : ℕ} (hn : 0 < n) (m : ℕ) :
    (qExpansion 1 (heckeTn k n f)).coeff m = ∑ d ∈ (Nat.gcd m n).divisors,
      χ d * (d : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (m * n / d ^ 2) :=
  congrFun (csL_heckeTn_chi k χ n hn f hf) m

/-- The same formula with the sum restricted to `gcd(d, M) = 1`. -/
theorem coeff_heckeTn_chi' (k : ℤ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) {n : ℕ} (hn : 0 < n) (m : ℕ) :
    (qExpansion 1 (heckeTn k n f)).coeff m = ∑ d ∈ (Nat.gcd m n).divisors with d.Coprime M,
      χ d * (d : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (m * n / d ^ 2) := by
  rw [coeff_heckeTn_chi k hf hn m, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs with hd
  · rfl
  · rw [MulChar.map_nonunit χ (fun hu => hd ((ZMod.isUnit_iff_coprime d M).1 hu)), zero_mul, zero_mul]

/-- `a_m(T_n f) = a_{mn}(f)` for coprime `m, n`, every `f`. -/
theorem coeff_heckeTn_of_coprime (k : ℤ) {m n : ℕ} (hn : 0 < n) (hmn : m.Coprime n) (f : S1 M k) :
    (qExpansion 1 (heckeTn k n f)).coeff m = (qExpansion 1 f).coeff (m * n) := by
  show csL M k (heckeTn k n f) m = csL M k f (m * n)
  rw [← sum_proj k f, map_sum, map_sum, map_sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [csL_heckeTn_chi k χ n hn _ (proj_mem k χ f), tN_of_coprime (wt_one χ k) hmn]

/-- **`a_1(T_n f) = a_n(f)`** for every `f`. -/
theorem coeff_one_heckeTn (k : ℤ) {n : ℕ} (hn : 0 < n) (f : S1 M k) :
    (qExpansion 1 (heckeTn k n f)).coeff 1 = (qExpansion 1 f).coeff n := by
  rw [coeff_heckeTn_of_coprime k hn (Nat.coprime_one_left n), one_mul]

end forms

/-! ## (C) Compatibility with the level maps -/

section level

variable {L M : ℕ} [NeZero L] [NeZero M]

theorem diamond_inclCF (hLM : L ∣ M) (k : ℤ) (d : (ZMod M)ˣ) (f : S1 L k) :
    diamond k d (Level.inclCF hLM k f) = Level.inclCF hLM k (diamond k (ZMod.unitsMap hLM d) f) := by
  apply DFunLike.coe_injective
  have hγ : ((lift0 d : Gamma0 M) : SL(2, ℤ)) ∈ Gamma0 M := (lift0 d).2
  have hd : (d : ZMod M) = ((((lift0 d : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) := by
    rw [← coe_unitMap, unitMap_lift0]
  have hdL : ((ZMod.unitsMap hLM d : (ZMod L)ˣ) : ZMod L) =
      ((((lift0 d : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod L) := by
    rw [ZMod.unitsMap_val, hd, ZMod.cast_intCast hLM]
  rw [coe_diamond_of_mem k hγ d hd, Level.coe_inclCF, Level.coe_inclCF,
    coe_diamond_of_mem k (Level.Gamma0_le_of_dvd hLM hγ) _ hdL]

/-- **`⟨d⟩ ∘ ι_e = ι_e ∘ ⟨d⟩`**. -/
theorem diamond_iotaCF (e : ℕ) [NeZero e] (h : e * L ∣ M) (k : ℤ) (d : (ZMod M)ˣ) (f : S1 L k) :
    diamond k d (Level.iotaCF e h k f) =
      Level.iotaCF e h k (diamond k (ZMod.unitsMap (Level.dvd_of_mul_dvd' h) d) f) := by
  apply DFunLike.coe_injective
  have hγ : ((lift0 d : Gamma0 M) : SL(2, ℤ)) ∈ Gamma0 M := (lift0 d).2
  have hd : (d : ZMod M) = ((((lift0 d : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) := by
    rw [← coe_unitMap, unitMap_lift0]
  obtain ⟨y, hyΓ, hy11, hy⟩ := Level.exists_conj_dg_Gamma0 h hγ
  have hdL : ((ZMod.unitsMap (Level.dvd_of_mul_dvd' h) d : (ZMod L)ˣ) : ZMod L) =
      ((y 1 1 : ℤ) : ZMod L) := by
    rw [ZMod.unitsMap_val, hd, hy11, ZMod.cast_intCast (Level.dvd_of_mul_dvd' h)]
  have hmul : Level.dg e * Matrix.SpecialLinearGroup.mapGL ℝ ((lift0 d : Gamma0 M) : SL(2, ℤ)) =
      Matrix.SpecialLinearGroup.mapGL ℝ y * Level.dg e := by
    rw [hy, inv_mul_cancel_right]
  rw [coe_diamond_of_mem k hγ d hd, Level.coe_iotaCF, Level.coe_iotaCF, ModularForm.SL_smul_slash,
    coe_diamond_of_mem k hyΓ _ hdL]
  congr 1
  show (⇑f ∣[k] Level.dg e) ∣[k]
      (Matrix.SpecialLinearGroup.mapGL ℝ ((lift0 d : Gamma0 M) : SL(2, ℤ))) =
    (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ y)) ∣[k] Level.dg e
  rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul]

lemma unitsMap_unitP (hLM : L ∣ M) {p : ℕ} [Fact p.Prime] (hpM : ¬ p ∣ M) (hpL : ¬ p ∣ L) :
    ZMod.unitsMap hLM (unitP hpM) = unitP hpL := by
  apply Units.ext
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hLM]

/-- **`T_p ∘ incl = incl ∘ T_p`** for `p ∤ M`. -/
theorem heckeT_inclCF (hLM : L ∣ M) (k : ℤ) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (f : S1 L k) :
    heckeT p k (Level.inclCF hLM k f) = Level.inclCF hLM k (heckeT p k f) := by
  have hpL : ¬ p ∣ L := fun h => hpM (h.trans hLM)
  apply eq_of_csL
  funext n
  rw [csL_apply, coeff_heckeT_of_not_dvd k hpM, diamond_inclCF hLM, unitsMap_unitP hLM hpM hpL]
  exact (coeff_heckeT_of_not_dvd k hpL f n).symm

/-- `U_p ∘ incl = incl ∘ U_p` for `p ∣ L`. -/
theorem heckeT_inclCF_of_dvd (hLM : L ∣ M) (k : ℤ) (p : ℕ) [Fact p.Prime] (hpL : p ∣ L)
    (f : S1 L k) : heckeT p k (Level.inclCF hLM k f) = Level.inclCF hLM k (heckeT p k f) := by
  apply eq_of_csL
  funext n
  exact (coeff_heckeT_of_dvd k (hpL.trans hLM) _ n).trans (coeff_heckeT_of_dvd k hpL f n).symm

lemma seq_iota {p e : ℕ} (hpe : p.Coprime e) (A B : ℕ → ℂ) (c : ℂ) (n : ℕ) :
    (if e ∣ p * n then A (p * n / e) else 0) +
        c * (if p ∣ n then (if e ∣ n / p then B (n / p / e) else 0) else 0) =
      if e ∣ n then A (p * (n / e)) + c * (if p ∣ n / e then B (n / e / p) else 0) else 0 := by
  rw [ite_dvd_mul_div hpe.symm A n, ite_add_zero', ite_mul_zero', ite_dvd_div_div p e B n,
    ite_dvd_div_div e p B n, mul_comm e p]

/-- **`T_p ∘ ι_e = ι_e ∘ T_p`** for `p ∤ M`. -/
theorem heckeT_iotaCF (e : ℕ) [NeZero e] (h : e * L ∣ M) (k : ℤ) (p : ℕ) [hp : Fact p.Prime]
    (hpM : ¬ p ∣ M) (f : S1 L k) :
    heckeT p k (Level.iotaCF e h k f) = Level.iotaCF e h k (heckeT p k f) := by
  have hLM := Level.dvd_of_mul_dvd' h
  have hpL : ¬ p ∣ L := fun h' => hpM (h'.trans hLM)
  have hpe : p.Coprime e := (Nat.Prime.coprime_iff_not_dvd hp.out).2
    (fun h' => hpM (h'.trans ((dvd_mul_right e L).trans h)))
  apply eq_of_csL
  funext n
  rw [csL_apply, csL_apply, coeff_heckeT_of_not_dvd k hpM, diamond_iotaCF e h,
    unitsMap_unitP hLM hpM hpL]
  simp only [Level.coeff_iotaCF]
  rw [coeff_heckeT_of_not_dvd k hpL]
  exact seq_iota hpe (fun m => (qExpansion 1 f).coeff m)
    (fun m => (qExpansion 1 (diamond k (unitP hpL) f)).coeff m) _ n

end level

/-! ## (D) Eigenforms -/

section eigen

variable {M : ℕ} [NeZero M]

/-- A `T_p`-eigenform in `S_k(M, χ)` with `a_1 = 1` has eigenvalue `a_p` and satisfies
`a(pn) = a_p a_n - χ(p) p^(k-1) [p ∣ n] a(n/p)`. -/
theorem eigen_coeff (k : ℤ) {p : ℕ} [hp : Fact p.Prime] {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) {c : ℂ} (he : heckeT p k f = c • f)
    (h1 : (qExpansion 1 f).coeff 1 = 1) :
    c = (qExpansion 1 f).coeff p ∧ ∀ n, (qExpansion 1 f).coeff (p * n) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff n -
        χ p * (p : ℂ) ^ (k - 1) * (if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0) := by
  have key : ∀ n, c * (qExpansion 1 f).coeff n = (qExpansion 1 f).coeff (p * n) +
      χ p * (p : ℂ) ^ (k - 1) * (if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0) := by
    intro n
    rw [← coeff_smul_Gamma1, ← he, coeff_heckeT_chi k hf]
  have hc : c = (qExpansion 1 f).coeff p := by
    have := key 1
    rw [h1, mul_one, mul_one, if_neg (Nat.Prime.not_dvd_one hp.out), mul_zero, add_zero] at this
    exact this
  refine ⟨hc, fun n => ?_⟩
  rw [← hc]
  linear_combination (key n).symm

lemma chi_prime_of_dvd {p : ℕ} (hp : p.Prime) (χ : DirichletCharacter ℂ M) (hpM : p ∣ M) :
    χ (p : ZMod M) = 0 :=
  MulChar.map_nonunit χ (fun hu => (Nat.Prime.coprime_iff_not_dvd hp).1
    ((ZMod.isUnit_iff_coprime p M).1 hu) hpM)

/-- **The N2 recursion** for an eigenform of every `T_p` (`U_p` included) with `a_1 = 1`. -/
theorem eigen_recursion (k : ℤ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) (h1 : (qExpansion 1 f).coeff 1 = 1)
    (he : ∀ p : ℕ, p.Prime → ∃ c : ℂ, heckeTP k p f = c • f) :
    ∀ p n : ℕ, p.Prime → (qExpansion 1 f).coeff (p * n) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff n -
        (if p ∣ M then 0 else χ (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0)) := by
  intro p n hp
  haveI := Fact.mk hp
  obtain ⟨c, hc⟩ := he p hp
  rw [heckeTP_eq] at hc
  rw [(eigen_coeff k hf hc h1).2 n]
  by_cases hpM : p ∣ M
  · rw [if_pos hpM, chi_prime_of_dvd hp χ hpM]; ring
  · rw [if_neg hpM]

/-- **The good-prime recursion**: eigenform of `T_p` for all `p ∤ M`, `a_1 = 1`. -/
theorem eigen_recursion_good (k : ℤ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) (h1 : (qExpansion 1 f).coeff 1 = 1)
    (he : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∃ c : ℂ, heckeTP k p f = c • f) :
    ∀ p n : ℕ, p.Prime → ¬ p ∣ M → (qExpansion 1 f).coeff (p * n) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff n -
        (if p ∣ M then 0 else χ (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0)) := by
  intro p n hp hpM
  haveI := Fact.mk hp
  obtain ⟨c, hc⟩ := he p hp hpM
  rw [heckeTP_eq] at hc
  rw [(eigen_coeff k hf hc h1).2 n, if_neg hpM]

lemma eigen_heckePow (k : ℤ) (p : ℕ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) (he : ∃ c : ℂ, heckeTP k p f = c • f) :
    ∀ r, ∃ μ : ℂ, heckePow k p r f = μ • f
  | 0 => ⟨1, by rw [one_smul]; rfl⟩
  | 1 => he
  | r + 2 => by
    obtain ⟨μ1, h1⟩ := eigen_heckePow k p hf he (r + 1)
    obtain ⟨μ0, h0⟩ := eigen_heckePow k p hf he r
    obtain ⟨c, hc⟩ := he
    refine ⟨c * μ1 - χ p * (p : ℂ) ^ (k - 1) * μ0, ?_⟩
    rw [heckePow_succ_succ, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, h1, h0,
      map_smul, map_smul, hc, heckeCorr_chi k p hf, smul_smul, smul_smul, sub_smul, mul_comm μ1 c,
      mul_comm μ0]

/-- **`T_n f = a_n(f) f`** for a normalized eigenform of all `T_p`. -/
theorem heckeTn_eigen (k : ℤ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) (h1 : (qExpansion 1 f).coeff 1 = 1)
    (he : ∀ p : ℕ, p.Prime → ∃ c : ℂ, heckeTP k p f = c • f) {n : ℕ} (hn : 0 < n) :
    heckeTn k n f = (qExpansion 1 f).coeff n • f := by
  have hP : ∃ μ : ℂ, heckeTn k n f = μ • f := by
    unfold heckeTn
    refine Finset.noncommProd_induction _ _ _ (fun X : Module.End ℂ (S1 M k) => ∃ μ : ℂ, X f = μ • f) ?_
      ⟨1, by rw [one_smul]; rfl⟩
      (fun p hp => eigen_heckePow k p hf (he p (Nat.prime_of_mem_primeFactors hp)) _)
    rintro X Y ⟨μ, hX⟩ ⟨ν, hY⟩
    exact ⟨ν * μ, by rw [Module.End.mul_apply, hY, map_smul, hX, smul_smul]⟩
  obtain ⟨μ, hμ⟩ := hP
  have := coeff_one_heckeTn k hn f
  rw [hμ, coeff_smul_Gamma1, h1, mul_one] at this
  rw [hμ, this]

end eigen

end RamanujanPetersson.HeckeAlgebra

end


