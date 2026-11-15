-- Prove2me | Definitions.Def_RPLib_S3_KloostermanC
-- name    : RPLib_S3_KloostermanC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:28:38.15313+00:00
-- url     : https://prove2.me/theorems/8303d31f-ec18-4c8b-aed1-f30f64cc3493
-- title:
--   The Eichler-Selberg trace formula in weight two: summing restricted Kloosterman sums over the modulus
-- statement:
--   Summing restricted Kloosterman sums over the modulus.
--
--   * `fp f n = Π_{p ∣ n} f p (v_p n)` (`fp_mul`, `fp_prime_pow`, `fp_prod_prime_pow`).
--   * `sPart N c` / `rPart N c`: the parts of `c` built from primes `< N` / `≥ N`.
--   * `hfun N m r` (multiplicative majorant), `norm_klR_div_le`: `‖klR M c u m r‖ / c^2 ≤ hfun N m r c`
--     (`0 < M < N`, `11 ≤ N`, `M ∣ c`).
--   * `sum_range_hfun_le`, `summable_hfun`, `tsum_hfun_le`: for `(m, r) ≠ (0, 0)`,
--     `Σ_c hfun N m r c ≤ CK N * gcd(m, r)^(1/8)` (Euler product over primes).
--   * `summable_klR_div`: `Σ_{c' : ℕ} ‖klR M (M(c'+1)) u m r‖ / (M(c'+1))^2` converges and is
--     `≤ CK (M + 11) * gcd(m, r)^(1/8)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; A. Weil, On some exponential sums, Proc. Nat. Acad. Sci. USA 34 (1948), 204-207; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_KloostermanB

/-!
# S3-ES-Wt2 (O4, KL_C): summing restricted Kloosterman sums over the modulus

* `fp f n = Π_{p ∣ n} f p (v_p n)` (`fp_mul`, `fp_prime_pow`, `fp_prod_prime_pow`).
* `sPart N c` / `rPart N c`: the parts of `c` built from primes `< N` / `≥ N`.
* `hfun N m r` (multiplicative majorant), `norm_klR_div_le`: `‖klR M c u m r‖ / c^2 ≤ hfun N m r c`
  (`0 < M < N`, `11 ≤ N`, `M ∣ c`).
* `sum_range_hfun_le`, `summable_hfun`, `tsum_hfun_le`: for `(m, r) ≠ (0, 0)`,
  `Σ_c hfun N m r c ≤ CK N * gcd(m, r)^(1/8)` (Euler product over primes).
* `summable_klR_div`: `Σ_{c' : ℕ} ‖klR M (M(c'+1)) u m r‖ / (M(c'+1))^2` converges and is
  `≤ CK (M + 11) * gcd(m, r)^(1/8)`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KL

/-! ### Products over the factorization -/

/-- `fp f n = Π_{p ∣ n} f p (v_p n)`. -/
def fp (f : ℕ → ℕ → ℝ) (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, f p (n.factorization p)

lemma fp_zero (f : ℕ → ℕ → ℝ) : fp f 0 = 1 := by simp [fp]

lemma fp_one (f : ℕ → ℕ → ℝ) : fp f 1 = 1 := by simp [fp]

lemma fp_prime_pow (f : ℕ → ℕ → ℝ) {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    fp f (p ^ e) = f p e := by
  rw [fp, Nat.primeFactors_prime_pow he hp, Finset.prod_singleton, Nat.factorization_pow,
    Finsupp.smul_apply, hp.factorization_self, smul_eq_mul, mul_one]

lemma fp_mul (f : ℕ → ℕ → ℝ) {a b : ℕ} (h : a.Coprime b) : fp f (a * b) = fp f a * fp f b := by
  unfold fp
  rw [Nat.Coprime.primeFactors_mul h, Finset.prod_union h.disjoint_primeFactors]
  congr 1
  · refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpb : p ∉ b.primeFactors := Finset.disjoint_left.1 h.disjoint_primeFactors hp
    have : b.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
    rw [Nat.factorization_mul_of_coprime h, Finsupp.add_apply, this, add_zero]
  · refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpa : p ∉ a.primeFactors := Finset.disjoint_right.1 h.disjoint_primeFactors hp
    have : a.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
    rw [Nat.factorization_mul_of_coprime h, Finsupp.add_apply, this, zero_add]

lemma fp_prod_prime_pow (f : ℕ → ℕ → ℝ) (e : ℕ → ℕ) (S : Finset ℕ) :
    (∀ p ∈ S, p.Prime) → (∀ p ∈ S, e p ≠ 0) → fp f (∏ p ∈ S, p ^ e p) = ∏ p ∈ S, f p (e p) := by
  induction S using Finset.induction with
  | empty => intro _ _; simp [fp_one]
  | insert q S hq ih =>
    intro hS he
    have hqp : q.Prime := hS q (Finset.mem_insert_self _ _)
    have hcop : (q ^ e q).Coprime (∏ p ∈ S, p ^ e p) := Nat.Coprime.prod_right (fun p hp =>
      Nat.coprime_pow_primes _ _ hqp (hS p (Finset.mem_insert_of_mem hp)) (by rintro rfl; exact hq hp))
    rw [Finset.prod_insert hq, Finset.prod_insert hq, fp_mul f hcop,
      fp_prime_pow f hqp (he q (Finset.mem_insert_self _ _)),
      ih (fun p hp => hS p (Finset.mem_insert_of_mem hp)) (fun p hp => he p (Finset.mem_insert_of_mem hp))]

/-! ### Smooth and rough parts -/

/-- The part of `c` built from the primes below `N`. -/
def sPart (N c : ℕ) : ℕ := ∏ p ∈ c.primeFactors with p < N, p ^ c.factorization p

/-- The part of `c` built from the primes at least `N`. -/
def rPart (N c : ℕ) : ℕ := ∏ p ∈ c.primeFactors with ¬ p < N, p ^ c.factorization p

lemma factorization_ne_zero_of_mem {c p : ℕ} (hp : p ∈ c.primeFactors) : c.factorization p ≠ 0 :=
  Finsupp.mem_support_iff.1 (by rw [Nat.support_factorization]; exact hp)

lemma sPart_mul_rPart (N : ℕ) {c : ℕ} (hc : c ≠ 0) : sPart N c * rPart N c = c := by
  rw [sPart, rPart, Finset.prod_filter_mul_prod_filter_not]
  exact (Nat.prod_primeFactors_pow_factorization hc).symm

lemma coprime_sPart_rPart (N c : ℕ) : (sPart N c).Coprime (rPart N c) := by
  refine Nat.Coprime.prod_left (fun p hp => Nat.Coprime.prod_right (fun q hq => ?_))
  rw [Finset.mem_filter] at hp hq
  exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp.1)
    (Nat.prime_of_mem_primeFactors hq.1) (by rintro rfl; exact hq.2 hp.2)

lemma le_of_mem_primeFactors_rPart {N c q : ℕ} (hq : q ∈ (rPart N c).primeFactors) : N ≤ q := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  rw [rPart] at hqd
  obtain ⟨p, hp, hdvd⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 hqd
  rw [Finset.mem_filter] at hp
  have hpq := (Nat.prime_dvd_prime_iff_eq hqp (Nat.prime_of_mem_primeFactors hp.1)).1
    (hqp.dvd_of_dvd_pow hdvd)
  subst hpq
  omega

lemma dvd_sPart {M N c : ℕ} (hM : 0 < M) (hMN : M < N) (hc : c ≠ 0) (hMc : M ∣ c) :
    M ∣ sPart N c := by
  have hcop : M.Coprime (rPart N c) := by
    refine Nat.Coprime.prod_right (fun q hq => Nat.Coprime.pow_right _ ?_)
    rw [Finset.mem_filter] at hq
    have hqp := Nat.prime_of_mem_primeFactors hq.1
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hqp).2 (fun hd => ?_))
    have := Nat.le_of_dvd hM hd
    omega
  rw [← sPart_mul_rPart N hc] at hMc
  exact hcop.dvd_of_dvd_mul_right hMc

/-! ### The majorant -/

/-- Local factor of the majorant `hfun`. -/
def hloc (N : ℕ) (m r : ℤ) (p e : ℕ) : ℝ :=
  if p < N then ((p : ℝ) ^ e)⁻¹ else ((p : ℝ) ^ (2 * e))⁻¹ * bp p e m r

/-- Multiplicative majorant of `‖klR M c u m r‖ / c^2`. -/
def hfun (N : ℕ) (m r : ℤ) (c : ℕ) : ℝ := fp (hloc N m r) c

lemma hloc_nonneg (N : ℕ) (m r : ℤ) (p e : ℕ) : 0 ≤ hloc N m r p e := by
  unfold hloc
  split_ifs
  · positivity
  · exact mul_nonneg (by positivity) (bp_nonneg _ _ _ _)

lemma hfun_nonneg (N : ℕ) (m r : ℤ) (c : ℕ) : 0 ≤ hfun N m r c := by
  unfold hfun fp
  exact Finset.prod_nonneg (fun _ _ => hloc_nonneg _ _ _ _ _)

lemma hfun_one (N : ℕ) (m r : ℤ) : hfun N m r 1 = 1 := fp_one _

lemma hfun_mul (N : ℕ) (m r : ℤ) {a b : ℕ} (h : a.Coprime b) :
    hfun N m r (a * b) = hfun N m r a * hfun N m r b := fp_mul _ h

lemma hloc_zero (N : ℕ) (m r : ℤ) (p : ℕ) : hloc N m r p 0 = 1 := by
  simp [hloc, bp]

lemma hfun_prime_pow (N : ℕ) (m r : ℤ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    hfun N m r (p ^ e) = hloc N m r p e := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, hfun, fp_one, hloc_zero]
  · exact fp_prime_pow _ hp he.ne'

lemma hfun_eq (N : ℕ) (m r : ℤ) (c : ℕ) :
    hfun N m r c = ((sPart N c : ℕ) : ℝ)⁻¹ * (((rPart N c : ℕ) : ℝ) ^ 2)⁻¹ * Bnd (rPart N c) m r := by
  have hB : Bnd (rPart N c) m r = ∏ p ∈ c.primeFactors with ¬ p < N, bp p (c.factorization p) m r := by
    have := fp_prod_prime_pow (fun p e => bp p e m r) (fun p => c.factorization p)
      (c.primeFactors.filter (fun p => ¬ p < N))
      (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)
      (fun p hp => factorization_ne_zero_of_mem (Finset.mem_filter.1 hp).1)
    exact this
  have h1 : ∏ p ∈ c.primeFactors with p < N, hloc N m r p (c.factorization p) =
      ((sPart N c : ℕ) : ℝ)⁻¹ := by
    rw [sPart, Nat.cast_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [hloc, if_pos (Finset.mem_filter.1 hp).2, Nat.cast_pow]
  have h2 : ∏ p ∈ c.primeFactors with ¬ p < N, hloc N m r p (c.factorization p) =
      (((rPart N c : ℕ) : ℝ) ^ 2)⁻¹ * Bnd (rPart N c) m r := by
    rw [hB, rPart, Nat.cast_prod, ← Finset.prod_pow, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [hloc, if_neg (Finset.mem_filter.1 hp).2, Nat.cast_pow, ← pow_mul,
      mul_comm (c.factorization p) 2]
  unfold hfun fp
  rw [← Finset.prod_filter_mul_prod_filter_not c.primeFactors (fun p => p < N), h1, h2, mul_assoc]

lemma exists_split {M N c : ℕ} (hM : 0 < M) (hMN : M < N) (hc : c ≠ 0) (hMc : M ∣ c) (m r : ℤ) :
    ∃ c1 c2 : ℕ, c1 * c2 = c ∧ M ∣ c1 ∧ c1.Coprime c2 ∧ (∀ q ∈ c2.primeFactors, N ≤ q) ∧
      hfun N m r c = ((c1 : ℝ))⁻¹ * (((c2 : ℝ)) ^ 2)⁻¹ * Bnd c2 m r :=
  ⟨sPart N c, rPart N c, sPart_mul_rPart N hc, dvd_sPart hM hMN hc hMc, coprime_sPart_rPart N c,
    fun _ hq => le_of_mem_primeFactors_rPart hq, hfun_eq N m r c⟩

/-- The per-modulus bound. -/
theorem norm_klR_div_le {M N : ℕ} (hM : 0 < M) (hMN : M < N) (h11 : 11 ≤ N) (c : ℕ) [NeZero c]
    (hMc : M ∣ c) (u : ZMod M) (m r : ℤ) :
    ‖klR M c u (m : ZMod c) (r : ZMod c)‖ / (c : ℝ) ^ 2 ≤ hfun N m r c := by
  obtain ⟨c1, c2, rfl, hM1, hcop, hpf, hh⟩ := exists_split hM hMN (NeZero.ne c) hMc m r
  rw [hh]
  have h1 : c1 ≠ 0 := left_ne_zero_of_mul (NeZero.ne (c1 * c2))
  have h2 : c2 ≠ 0 := right_ne_zero_of_mul (NeZero.ne (c1 * c2))
  have : NeZero c1 := ⟨h1⟩
  have : NeZero c2 := ⟨h2⟩
  obtain ⟨α, β, hαβ⟩ : IsCoprime (c2 : ℤ) (c1 : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
  have hαβ' : α * c2 + β * c1 = 1 := hαβ
  have hub : IsUnit ((β : ZMod c2)) := by
    refine IsUnit.of_mul_eq_one (c1 : ZMod c2) ?_
    have := congrArg (fun z : ℤ => (z : ZMod c2)) hαβ'
    push_cast at this
    simpa using this
  have e2 : ∀ t : ℤ, ZMod.castHom (Dvd.intro_left c1 rfl) (ZMod c2) (t : ZMod (c1 * c2)) =
      (t : ZMod c2) := fun t => map_intCast _ t
  rw [klR_crt hM1 hcop hαβ' u, e2, e2, norm_mul]
  have hA := norm_klR_le M c1 u
    ((α : ZMod c1) * ZMod.castHom (Dvd.intro c2 rfl) (ZMod c1) (m : ZMod (c1 * c2)))
    ((α : ZMod c1) * ZMod.castHom (Dvd.intro c2 rfl) (ZMod c1) (r : ZMod (c1 * c2)))
  have hB := norm_kl_le_Bnd m r c2 h2 (fun q hq => h11.trans (hpf q hq)) (β : ZMod c2) hub
  have hc1 : (0 : ℝ) < c1 := by exact_mod_cast Nat.pos_of_ne_zero h1
  have hc2 : (0 : ℝ) < c2 := by exact_mod_cast Nat.pos_of_ne_zero h2
  have hrw : (c1 : ℝ)⁻¹ * ((c2 : ℝ) ^ 2)⁻¹ * Bnd c2 m r =
      ((c1 : ℝ) * Bnd c2 m r) / ((c1 : ℝ) * c2) ^ 2 := by
    field_simp
  rw [hrw, Nat.cast_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul hA hB (norm_nonneg _) hc1.le) (by positivity)

/-! ### Local factors of the Euler product -/

lemma bp_le_pow {p : ℕ} (hp : 1 ≤ p) (e : ℕ) (m r : ℤ) : bp p e m r ≤ (p : ℝ) ^ e := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  unfold bp
  split_ifs with h1 h2
  · subst h1; simp
  · subst h1
    calc (p : ℝ) ^ ((7 : ℝ) / 8) ≤ (p : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hp' (by norm_num)
      _ = (p : ℝ) ^ 1 := by rw [Real.rpow_one, pow_one]
  · exact le_rfl

lemma hloc_le {N p : ℕ} (hp : 1 ≤ p) (e : ℕ) (m r : ℤ) : hloc N m r p e ≤ ((p : ℝ) ^ e)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  unfold hloc
  split_ifs
  · exact le_rfl
  · calc ((p : ℝ) ^ (2 * e))⁻¹ * bp p e m r ≤ ((p : ℝ) ^ (2 * e))⁻¹ * (p : ℝ) ^ e :=
          mul_le_mul_of_nonneg_left (bp_le_pow hp e m r) (by positivity)
      _ = ((p : ℝ) ^ e)⁻¹ := by
          rw [two_mul, pow_add, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0.ne'), mul_one]

lemma hfun_pp_le (N : ℕ) (m r : ℤ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    hfun N m r (p ^ e) ≤ ((p : ℝ)⁻¹) ^ e := by
  rw [hfun_prime_pow N m r hp, inv_pow]
  exact hloc_le hp.one_lt.le e m r

lemma summable_hfun_pp (N : ℕ) (m r : ℤ) {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => hfun N m r (p ^ e)) :=
  Summable.of_nonneg_of_le (fun _ => hfun_nonneg N m r _) (hfun_pp_le N m r hp)
    (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)))

lemma summable_norm_hfun_pp (N : ℕ) (m r : ℤ) {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => ‖hfun N m r (p ^ e)‖) :=
  (summable_hfun_pp N m r hp).congr (fun _ => (Real.norm_of_nonneg (hfun_nonneg N m r _)).symm)

lemma tsum_pp_small {N : ℕ} (m r : ℤ) {p : ℕ} (hp : p.Prime) (hpN : p < N) :
    ∑' e, hfun N m r (p ^ e) ≤ 2 := by
  have h : ∀ e, hfun N m r (p ^ e) = ((p : ℝ)⁻¹) ^ e := by
    intro e; rw [hfun_prime_pow N m r hp, hloc, if_pos hpN, inv_pow]
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  rw [tsum_congr h, tsum_geometric_of_lt_one (by positivity) (by linarith)]
  calc (1 - (p : ℝ)⁻¹)⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    _ = 2 := by norm_num

lemma tsum_pp_large_eq {N : ℕ} (m r : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p < N) :
    ∑' e, hfun N m r (p ^ e) =
      1 + ((p : ℝ) ^ 2)⁻¹ * bp p 1 m r + ((p : ℝ)⁻¹) ^ 2 * (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hs := summable_hfun_pp N m r hp
  rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).2 hs).tsum_eq_zero_add]
  have h0 : hfun N m r (p ^ 0) = 1 := by rw [pow_zero, hfun, fp_one]
  have h1 : hfun N m r (p ^ (0 + 1)) = ((p : ℝ) ^ 2)⁻¹ * bp p 1 m r := by
    rw [zero_add, hfun_prime_pow N m r hp 1, hloc, if_neg hpN, mul_one]
  have h2 : ∀ e : ℕ, hfun N m r (p ^ (e + 1 + 1)) = ((p : ℝ)⁻¹) ^ 2 * ((p : ℝ)⁻¹) ^ e := by
    intro e
    rw [hfun_prime_pow N m r hp, hloc, if_neg hpN, bp, if_neg (show ¬ (e + 1 + 1 = 1) by omega),
      two_mul, pow_add (p : ℝ) (e + 1 + 1) (e + 1 + 1), mul_inv, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hp0.ne'), mul_one, ← inv_pow]
    ring
  rw [h0, h1, tsum_congr h2, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hp1]
  ring

/-- `3 n^(-9/8)`. -/
def xs (n : ℕ) : ℝ := 3 * (n : ℝ) ^ (-(9 / 8 : ℝ))

lemma xs_nonneg (n : ℕ) : 0 ≤ xs n := by unfold xs; positivity

lemma summable_xs : Summable xs := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-(9 / 8 : ℝ))) := Real.summable_nat_rpow.2 (by norm_num)
  exact h.mul_left 3

def dF (g p : ℕ) : ℝ := if p ∣ g then (p : ℝ) ^ ((1 : ℝ) / 8) else 1

def aF (N p : ℕ) : ℝ := if p < N then 2 else 1

lemma one_le_dF {p : ℕ} (hp : p.Prime) (g : ℕ) : 1 ≤ dF g p := by
  unfold dF
  split_ifs
  · exact Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) (by norm_num)
  · exact le_rfl

lemma tsum_pp_large_le {N : ℕ} (h11 : 11 ≤ N) (m r : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p < N) :
    ∑' e, hfun N m r (p ^ e) ≤ Real.exp (xs p) * dF (Int.gcd m r) p := by
  rw [tsum_pp_large_eq m r hp hpN]
  have hp11 : (11 : ℝ) ≤ p := by exact_mod_cast (show 11 ≤ p by omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hq : (p : ℝ)⁻¹ ≤ 1 / 11 := by
    rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp11
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have htail : ((p : ℝ)⁻¹) ^ 2 * (1 - (p : ℝ)⁻¹)⁻¹ ≤ 2 * ((p : ℝ) ^ 2)⁻¹ := by
    rw [inv_pow, mul_comm (2 : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (1 - (p : ℝ)⁻¹)⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
      _ = 2 := by norm_num
  have hsq : ((p : ℝ) ^ 2)⁻¹ ≤ (p : ℝ) ^ (-(9 / 8 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hp0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hsq2 : ((p : ℝ) ^ 2)⁻¹ ≤ 1 / 121 := by
    rw [← inv_pow]
    calc ((p : ℝ)⁻¹) ^ 2 ≤ (1 / 11) ^ 2 := pow_le_pow_left₀ hq0 hq 2
      _ = 1 / 121 := by norm_num
  have hxs : xs p = 3 * (p : ℝ) ^ (-(9 / 8 : ℝ)) := rfl
  have hexp := Real.add_one_le_exp (xs p)
  have hE : 1 ≤ Real.exp (xs p) := Real.one_le_exp (xs_nonneg p)
  unfold bp
  rw [if_pos (rfl : (1 : ℕ) = 1)]
  by_cases hd : (p : ℤ) ∣ m ∧ (p : ℤ) ∣ r
  · rw [if_pos hd, dF, if_pos (Int.dvd_gcd hd.1 hd.2)]
    have hpp : ((p : ℝ) ^ 2)⁻¹ * p = (p : ℝ)⁻¹ := by
      rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ hp0.ne', mul_one]
    have h54 : (5 / 4 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 8) := by
      have h8 : ((5 / 4 : ℝ) ^ 8) ^ ((1 : ℝ) / 8) = 5 / 4 := by
        rw [show ((1 : ℝ) / 8) = ((8 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
      rw [← h8]
      exact Real.rpow_le_rpow (by positivity)
        (by linarith [show (5 / 4 : ℝ) ^ 8 ≤ 11 by norm_num]) (by norm_num)
    rw [hpp]
    calc 1 + (p : ℝ)⁻¹ + ((p : ℝ)⁻¹) ^ 2 * (1 - (p : ℝ)⁻¹)⁻¹ ≤ 5 / 4 := by linarith
      _ ≤ (p : ℝ) ^ ((1 : ℝ) / 8) := h54
      _ ≤ Real.exp (xs p) * (p : ℝ) ^ ((1 : ℝ) / 8) := le_mul_of_one_le_left (by positivity) hE
  · rw [if_neg hd]
    have hr : ((p : ℝ) ^ 2)⁻¹ * (p : ℝ) ^ ((7 : ℝ) / 8) = (p : ℝ) ^ (-(9 / 8 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hp0.le, ← Real.rpow_add hp0]
      norm_num
    have hD : 1 ≤ dF (Int.gcd m r) p := one_le_dF hp _
    rw [hr]
    calc 1 + (p : ℝ) ^ (-(9 / 8 : ℝ)) + ((p : ℝ)⁻¹) ^ 2 * (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (xs p) := by
          linarith
      _ ≤ Real.exp (xs p) * dF (Int.gcd m r) p := le_mul_of_one_le_right (by positivity) hD

lemma tsum_pp_le {N : ℕ} (h11 : 11 ≤ N) (m r : ℤ) {p : ℕ} (hp : p.Prime) :
    ∑' e, hfun N m r (p ^ e) ≤ aF N p * Real.exp (xs p) * dF (Int.gcd m r) p := by
  have hD := one_le_dF hp (Int.gcd m r)
  have hE : 1 ≤ Real.exp (xs p) := Real.one_le_exp (xs_nonneg p)
  by_cases hpN : p < N
  · rw [aF, if_pos hpN]
    have h1 : 1 ≤ Real.exp (xs p) * dF (Int.gcd m r) p := one_le_mul_of_one_le_of_one_le hE hD
    calc _ ≤ 2 := tsum_pp_small m r hp hpN
      _ ≤ 2 * Real.exp (xs p) * dF (Int.gcd m r) p := by nlinarith
  · rw [aF, if_neg hpN, one_mul]
    exact tsum_pp_large_le h11 m r hp hpN

lemma prod_aF_le (N : ℕ) (s : Finset ℕ) : ∏ p ∈ s with p.Prime, aF N p ≤ 2 ^ N := by
  unfold aF
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  refine pow_le_pow_right₀ (by norm_num) ?_
  calc _ ≤ (Finset.range N).card :=
        Finset.card_le_card (fun p hp => Finset.mem_range.2 (Finset.mem_filter.1 hp).2)
    _ = N := Finset.card_range N

lemma prod_dF_le (s : Finset ℕ) {g : ℕ} (hg : g ≠ 0) :
    ∏ p ∈ s with p.Prime, dF g p ≤ (g : ℝ) ^ ((1 : ℝ) / 8) := by
  unfold dF
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one,
    Real.finsetProd_rpow _ (fun p : ℕ => (p : ℝ)) (fun p _ => Nat.cast_nonneg p)]
  refine Real.rpow_le_rpow (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)) ?_ (by norm_num)
  rw [← Nat.cast_prod]
  have hsub : {x ∈ {p ∈ s | p.Prime} | x ∣ g} ⊆ g.primeFactors := fun p hp => by
    rw [Finset.mem_filter, Finset.mem_filter] at hp
    exact Nat.mem_primeFactors.2 ⟨hp.1.2, hp.2, hg⟩
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hg)
    (dvd_trans (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) hsub) (Nat.prod_primeFactors_dvd g))

lemma prod_pp_le {N : ℕ} (h11 : 11 ≤ N) (m r : ℤ) (hmr : m ≠ 0 ∨ r ≠ 0) (s : Finset ℕ) :
    ∏ p ∈ s with p.Prime, ∑' e, hfun N m r (p ^ e) ≤
      2 ^ N * Real.exp (∑' n, xs n) * (Int.gcd m r : ℝ) ^ ((1 : ℝ) / 8) := by
  have hg0 : Int.gcd m r ≠ 0 := (Int.gcd_pos_iff.2 hmr).ne'
  calc ∏ p ∈ s with p.Prime, ∑' e, hfun N m r (p ^ e)
      ≤ ∏ p ∈ s with p.Prime, (aF N p * Real.exp (xs p) * dF (Int.gcd m r) p) :=
        Finset.prod_le_prod (fun p _ => tsum_nonneg (fun e => hfun_nonneg N m r _))
          (fun p hp => tsum_pp_le h11 m r (Finset.mem_filter.1 hp).2)
    _ = (∏ p ∈ s with p.Prime, aF N p) * (∏ p ∈ s with p.Prime, Real.exp (xs p)) *
          ∏ p ∈ s with p.Prime, dF (Int.gcd m r) p := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ ≤ 2 ^ N * Real.exp (∑' n, xs n) * (Int.gcd m r : ℝ) ^ ((1 : ℝ) / 8) := by
        have hE : ∏ p ∈ s with p.Prime, Real.exp (xs p) ≤ Real.exp (∑' n, xs n) := by
          rw [← Real.exp_sum]
          exact Real.exp_le_exp.2 (Summable.sum_le_tsum _ (fun i _ => xs_nonneg i) summable_xs)
        have hA := prod_aF_le N s
        have hD := prod_dF_le s hg0
        have hA0 : 0 ≤ ∏ p ∈ s with p.Prime, aF N p :=
          Finset.prod_nonneg (fun p _ => by unfold aF; split_ifs <;> norm_num)
        have hE0 : 0 ≤ ∏ p ∈ s with p.Prime, Real.exp (xs p) :=
          Finset.prod_nonneg (fun p _ => (Real.exp_pos _).le)
        have hD0 : 0 ≤ ∏ p ∈ s with p.Prime, dF (Int.gcd m r) p :=
          Finset.prod_nonneg (fun p hp => le_trans zero_le_one (one_le_dF (Finset.mem_filter.1 hp).2 _))
        exact mul_le_mul (mul_le_mul hA hE hE0 (by positivity)) hD hD0 (by positivity)

/-! ### Summation -/

/-- The constant of the `c`-sum bound. -/
def CK (N : ℕ) : ℝ := 1 + 2 ^ N * Real.exp (∑' n, xs n)

theorem sum_range_hfun_le {N : ℕ} (h11 : 11 ≤ N) (m r : ℤ) (hmr : m ≠ 0 ∨ r ≠ 0) (n : ℕ) :
    ∑ i ∈ range n, hfun N m r i ≤ CK N * (Int.gcd m r : ℝ) ^ ((1 : ℝ) / 8) := by
  have hg0 : Int.gcd m r ≠ 0 := (Int.gcd_pos_iff.2 hmr).ne'
  have hg1 : (1 : ℝ) ≤ (Int.gcd m r : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hg0) (by norm_num)
  obtain ⟨-, hS⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := hfun N m r) (hfun_one N m r) (fun hc => hfun_mul N m r hc)
    (fun hp => summable_norm_hfun_pp N m r hp) (range n)
  have hS' := hasSum_subtype_iff_indicator.mp hS
  have hle : ∑ i ∈ range n, Set.indicator (Nat.factoredNumbers (range n)) (hfun N m r) i ≤
      ∏ p ∈ range n with p.Prime, ∑' e, hfun N m r (p ^ e) :=
    sum_le_hasSum _ (fun i _ => Set.indicator_nonneg (fun j _ => hfun_nonneg N m r j) i) hS'
  have hpt : ∀ i ∈ range n, hfun N m r i ≤
      (if i = 0 then 1 else 0) + Set.indicator (Nat.factoredNumbers (range n)) (hfun N m r) i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have := Set.indicator_nonneg (fun j _ => hfun_nonneg N m r j) 0
        (s := Nat.factoredNumbers (range n))
      rw [if_pos rfl, hfun, fp_zero]
      linarith
    · have hmem : i ∈ Nat.factoredNumbers (range n) := by
        rw [Nat.mem_factoredNumbers']
        intro p _ hpi
        exact Finset.mem_range.2 (lt_of_le_of_lt (Nat.le_of_dvd hi0 hpi) (Finset.mem_range.1 hi))
      simp only [if_neg hi0.ne', zero_add, Set.indicator_of_mem hmem, le_refl]
  have hfirst : ∑ i ∈ range n, (if i = 0 then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  calc ∑ i ∈ range n, hfun N m r i
      ≤ ∑ i ∈ range n, ((if i = 0 then (1 : ℝ) else 0) +
          Set.indicator (Nat.factoredNumbers (range n)) (hfun N m r) i) := Finset.sum_le_sum hpt
    _ = (∑ i ∈ range n, (if i = 0 then (1 : ℝ) else 0)) +
          ∑ i ∈ range n, Set.indicator (Nat.factoredNumbers (range n)) (hfun N m r) i :=
        Finset.sum_add_distrib
    _ ≤ 1 + 2 ^ N * Real.exp (∑' n, xs n) * (Int.gcd m r : ℝ) ^ ((1 : ℝ) / 8) :=
        add_le_add hfirst (hle.trans (prod_pp_le h11 m r hmr (range n)))
    _ ≤ CK N * (Int.gcd m r : ℝ) ^ ((1 : ℝ) / 8) := by
        unfold CK
        nlinarith [Real.exp_pos (∑' n, xs n), pow_pos (two_pos : (0 : ℝ) < 2) N]

theorem summable_hfun {N : ℕ} (h11 : 11 ≤ N) (m r : ℤ) (hmr : m ≠ 0 ∨ r ≠ 0) :
    Summable (hfun N m r) :=
  summable_of_sum_range_le (hfun_nonneg N m r) (sum_range_hfun_le h11 m r hmr)

theorem tsum_hfun_le {N : ℕ} (h11 : 11 ≤ N) (m r : ℤ) (hmr : m ≠ 0 ∨ r ≠ 0) :
    ∑' c, hfun N m r c ≤ CK N * (Int.gcd m r : ℝ) ^ ((1 : ℝ) / 8) :=
  Real.tsum_le_of_sum_range_le (hfun_nonneg N m r) (sum_range_hfun_le h11 m r hmr)

/-- The `c`-sum of restricted Kloosterman sums over the moduli `c = M (c' + 1)`. -/
theorem summable_klR_div {M : ℕ} [NeZero M] (u : ZMod M) (m r : ℤ) (hmr : m ≠ 0 ∨ r ≠ 0) :
    Summable (fun c' : ℕ => ‖klR M (M * (c' + 1)) u (m : ZMod (M * (c' + 1)))
        (r : ZMod (M * (c' + 1)))‖ / ((M * (c' + 1) : ℕ) : ℝ) ^ 2) ∧
    ∑' c' : ℕ, ‖klR M (M * (c' + 1)) u (m : ZMod (M * (c' + 1))) (r : ZMod (M * (c' + 1)))‖ /
        ((M * (c' + 1) : ℕ) : ℝ) ^ 2 ≤ CK (M + 11) * (Int.gcd m r : ℝ) ^ ((1 : ℝ) / 8) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hsum := summable_hfun (N := M + 11) (by omega) m r hmr
  have hinj : Function.Injective (fun c' : ℕ => M * (c' + 1)) := fun a b h => by
    have := Nat.eq_of_mul_eq_mul_left hM h
    omega
  have hle : ∀ c' : ℕ, ‖klR M (M * (c' + 1)) u (m : ZMod (M * (c' + 1))) (r : ZMod (M * (c' + 1)))‖ /
      ((M * (c' + 1) : ℕ) : ℝ) ^ 2 ≤ hfun (M + 11) m r (M * (c' + 1)) :=
    fun c' => norm_klR_div_le hM (by omega) (by omega) (M * (c' + 1)) (dvd_mul_right M _) u m r
  have hs2 : Summable (fun c' : ℕ => hfun (M + 11) m r (M * (c' + 1))) := hsum.comp_injective hinj
  have hs1 := Summable.of_nonneg_of_le (fun c' => by positivity) hle hs2
  refine ⟨hs1, ?_⟩
  calc _ ≤ ∑' c' : ℕ, hfun (M + 11) m r (M * (c' + 1)) := Summable.tsum_le_tsum hle hs1 hs2
    _ ≤ ∑' c, hfun (M + 11) m r c := tsum_comp_le_tsum_of_inj hsum (hfun_nonneg _ _ _) hinj
    _ ≤ _ := tsum_hfun_le (by omega) m r hmr

end RamanujanPetersson.KL


