-- Prove2me | Definitions.Def_RPLib_S3_HypParI
-- name    : RPLib_S3_HypParI
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:16:03.872456+00:00
-- url     : https://prove2.me/theorems/0a78bc7b-1b42-4edd-aeab-a6440d05f94e
-- title:
--   The Eichler-Selberg trace formula, hyperbolic part I: the index and the scalar term
-- statement:
--   A vector of $(\mathbb{Z}/M)^2$ has exact order $M$ iff its coordinates are coprime to $M$ jointly; there are $\psi(M)\varphi(M)$ of them, and $2\,[SL_2(\mathbb{Z}) : \pm\Gamma_1(M)] = \psi(M)\varphi(M)$ for $M \ge 3$. Consequently the scalar contribution equals the Cohen-Oesterlé term $A_1$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 3.9

import Mathlib
import Definitions.Def_RPLib_S3_HypParC

/-!
# S3-HypParTerms, part I: the index `[SL₂(ℤ) : ±Γ₁(M)]` and the scalar term

* `isExact_iff_coprime`: `v` has exact order `M` iff `gcd(v₀, v₁, M) = 1`.
* `card_exact_eq`: `#{v exact} = Σ_{d ∣ M} μ(d) (M/d)²` (Möbius).
* `sum_moebius_div_sq`, `psi_mul_totient`: `Σ_{d ∣ M} μ(d) (M/d)² = M² ∏_{p ∣ M} (1 - p⁻²) = ψ(M) φ(M)`.
* **`two_mul_index`** (`M ≥ 3`): `2 [SL₂(ℤ) : ±Γ₁(M)] = ψ(M) φ(M)`.
* **`index_mul_scalTrace`** (`M ≥ 3`): `[SL₂(ℤ) : ±Γ₁(M)] · scalTrace = scalarG1`.
-/

open CongruenceSubgroup
open scoped MatrixGroups RamanujanPetersson.S3.Conj

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

open RP.FundDomain RP.Petersson RamanujanPetersson.Kernel RamanujanPetersson.EllTerm ArithmeticFunction
open scoped ArithmeticFunction.Moebius

section Index

variable {M : ℕ} [NeZero M]

/-- Exact order `M` iff `gcd(v₀, v₁)` is coprime to `M`. -/
theorem isExact_iff_coprime (v : Fin 2 → ZMod M) :
    S3.Conj.IsExact M v ↔ Nat.Coprime (Nat.gcd (v 0).val (v 1).val) M := by
  constructor
  · intro hv
    by_contra h
    obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.1 h
    exact S3.Conj.not_dvd_of_isExact hv hp hp2 (hp1.trans (Nat.gcd_dvd_left _ _))
      (hp1.trans (Nat.gcd_dvd_right _ _))
  · intro hc d hd hd0 h
    have hdv : ∀ i, M ∣ d * (v i).val := by
      intro i
      have hi := congr_fun h i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at hi
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val]
      exact hi
    have h2 : M ∣ d * Nat.gcd (v 0).val (v 1).val := by
      rw [← Nat.gcd_mul_left]
      exact Nat.dvd_gcd (hdv 0) (hdv 1)
    have h3 : M ∣ d := hc.symm.dvd_of_dvd_mul_right h2
    exact absurd (Nat.le_of_dvd hd0 h3) (not_le.2 (Finset.mem_range.1 hd))

open Classical in
/-- Exact vectors correspond to pairs `(a, b) ∈ [0, M)²` with `gcd(a, b, M) = 1`. -/
theorem card_exact_eq_pairs :
    (Finset.univ.filter fun v : Fin 2 → ZMod M => S3.Conj.IsExact M v).card =
      ((Finset.range M ×ˢ Finset.range M).filter
        fun p : ℕ × ℕ => Nat.Coprime (Nat.gcd p.1 p.2) M).card := by
  refine Finset.card_nbij' (fun v : Fin 2 → ZMod M => ((v 0).val, (v 1).val))
    (fun p : ℕ × ℕ => ![(p.1 : ZMod M), (p.2 : ZMod M)]) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨ZMod.val_lt _, ZMod.val_lt _⟩, (isExact_iff_coprime v).1 hv⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [isExact_iff_coprime]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hp.1.1, Nat.mod_eq_of_lt hp.1.2]
    exact hp.2
  · intro v _
    ext i
    fin_cases i <;> simp
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hp.1.1, Nat.mod_eq_of_lt hp.1.2]

/-- `Σ_{d ∣ g} μ(d) = [g = 1]`. -/
lemma sum_moebius_divisors (g : ℕ) : (∑ d ∈ g.divisors, (μ d : ℤ)) = if g = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f g) moebius_mul_coe_zeta
  rw [coe_mul_zeta_apply, one_apply] at h
  exact h

omit [NeZero M] in
lemma card_filter_dvd_range {d : ℕ} (hd : d ∣ M) (hd0 : 0 < d) :
    ((Finset.range M).filter fun a => d ∣ a).card = M / d := by
  obtain ⟨m, hm⟩ := hd
  have hmd : M / d = m := by rw [hm, Nat.mul_div_cancel_left _ hd0]
  have : (Finset.range M).filter (fun a => d ∣ a) = (Finset.range m).image (fun i => d * i) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ha, i, rfl⟩
      refine ⟨i, ?_, rfl⟩
      rw [hm] at ha
      by_contra hi
      push Not at hi
      nlinarith
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, dvd_mul_right _ _⟩
      rw [hm]
      nlinarith
  rw [this, Finset.card_image_of_injective _ (mul_right_injective₀ hd0.ne'), Finset.card_range, hmd]

/-- Möbius count of the pairs. -/
theorem card_coprime_pairs :
    ((((Finset.range M ×ˢ Finset.range M).filter
        fun p : ℕ × ℕ => Nat.Coprime (Nat.gcd p.1 p.2) M).card : ℕ) : ℤ) =
      ∑ d ∈ M.divisors, (μ d : ℤ) * ((M / d : ℕ) : ℤ) ^ 2 := by
  have hM0 : M ≠ 0 := NeZero.ne M
  rw [Finset.natCast_card_filter]
  have key : ∀ p : ℕ × ℕ, (if Nat.Coprime (Nat.gcd p.1 p.2) M then (1 : ℤ) else 0) =
      ∑ d ∈ M.divisors, if d ∣ p.1 ∧ d ∣ p.2 then (μ d : ℤ) else 0 := by
    intro p
    rw [← Finset.sum_filter]
    have hg : Nat.gcd (Nat.gcd p.1 p.2) M ≠ 0 :=
      (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hM0)).ne'
    have hfil : M.divisors.filter (fun d => d ∣ p.1 ∧ d ∣ p.2) =
        (Nat.gcd (Nat.gcd p.1 p.2) M).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      tauto
    rw [hfil, sum_moebius_divisors]
  rw [Finset.sum_congr rfl (fun p _ => key p), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdM := Nat.dvd_of_mem_divisors hd
  have hd0 := Nat.pos_of_mem_divisors hd
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Finset.filter_product (fun a => d ∣ a) (fun b => d ∣ b), Finset.card_product,
    card_filter_dvd_range hdM hd0]
  push_cast
  ring

omit [NeZero M] in
/-- `μ(∏_{p ∈ T} p) / (∏ p)² = ∏_{p ∈ T} (-1/p²)` for a set of primes `T ∣ M`. -/
lemma moebius_prod_term (T : Finset ℕ) (hT : T ⊆ M.primeFactors) :
    ((μ (∏ p ∈ T, p) : ℤ) : ℚ) * (1 / ((∏ p ∈ T, p : ℕ) : ℚ) ^ 2) =
      ∏ p ∈ T, (-(1 / (p : ℚ) ^ 2)) := by
  rw [isMultiplicative_moebius.map_prod_of_subset_primeFactors M T hT, Int.cast_prod, Nat.cast_prod,
    ← Finset.prod_pow, one_div, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [moebius_apply_prime (Nat.prime_of_mem_primeFactors (hT hp))]
  push_cast
  ring

theorem sum_moebius_div_sq :
    (∑ d ∈ M.divisors, ((μ d : ℤ) : ℚ) * ((M / d : ℕ) : ℚ) ^ 2) =
      (M : ℚ) ^ 2 * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  have hM0 : M ≠ 0 := NeZero.ne M
  have h1 : ∀ d ∈ M.divisors, ((μ d : ℤ) : ℚ) * ((M / d : ℕ) : ℚ) ^ 2 =
      (M : ℚ) ^ 2 * (((μ d : ℤ) : ℚ) * (1 / (d : ℚ) ^ 2)) := by
    intro d hd
    have hdM := Nat.dvd_of_mem_divisors hd
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    rw [Nat.cast_div hdM hd0]
    field_simp
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_filter_of_ne (p := Squarefree) (fun d _ h => ?_)]
  · rw [Nat.sum_divisors_filter_squarefree hM0]
    have hP : (UniqueFactorizationMonoid.normalizedFactors M).toFinset = M.primeFactors := by
      rw [Nat.factors_eq]
      rfl
    have hsub : ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℚ) ^ 2) =
        ∏ p ∈ M.primeFactors, (1 + -(1 / (p : ℚ) ^ 2)) :=
      Finset.prod_congr rfl (fun p _ => sub_eq_add_neg _ _)
    rw [hP, hsub, Finset.prod_one_add]
    refine Finset.sum_congr rfl (fun T hT => ?_)
    have hv : T.val.prod = ∏ p ∈ T, p := Finset.prod_val T
    rw [hv]
    exact moebius_prod_term T (Finset.mem_powerset.1 hT)
  · by_contra hsq
    exact h (by rw [moebius_eq_zero_of_not_squarefree hsq]; simp)

omit [NeZero M] in
theorem psi_mul_totient :
    S3.dedekindPsi M * (Nat.totient M : ℚ) =
      (M : ℚ) ^ 2 * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  rw [S3.dedekindPsi, Nat.totient_eq_mul_prod_factors]
  have h : ∀ p ∈ M.primeFactors, (1 - 1 / (p : ℚ) ^ 2) = (1 + 1 / (p : ℚ)) * (1 - (p : ℚ)⁻¹) := by
    intro p hp
    have : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp
    ring
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib]
  ring

open Classical in
/-- `#{v ∈ (ℤ/M)² of exact order M} = ψ(M) φ(M)`. -/
theorem card_exact_eq :
    ((Finset.univ.filter fun v : Fin 2 → ZMod M => S3.Conj.IsExact M v).card : ℚ) =
      S3.dedekindPsi M * (Nat.totient M : ℚ) := by
  rw [psi_mul_totient, ← sum_moebius_div_sq, card_exact_eq_pairs]
  have h := card_coprime_pairs (M := M)
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast] at h'
  exact h'

open Classical in
/-- **The index**: `2 [SL₂(ℤ) : ±Γ₁(M)] = ψ(M) φ(M)` for `M ≥ 3`. -/
theorem two_mul_index (hM : 3 ≤ M) :
    (2 * ((pmSL (Gamma1 M)).index : ℚ)) = S3.dedekindPsi M * Nat.totient M := by
  have h1 := card_exact_filter (M := M) hM (fun _ => True) (fun _ => Iff.rfl)
  have h2 : Nat.card {c : SL(2, ℤ) ⧸ pmSL (Gamma1 M) // True} = (pmSL (Gamma1 M)).index := by
    rw [Subgroup.index]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  have h1' : (Finset.univ.filter fun v : Fin 2 → ZMod M => S3.Conj.IsExact M v).card =
      2 * Nat.card {c : SL(2, ℤ) ⧸ pmSL (Gamma1 M) // True} := by
    rw [← h1]
    congr 1
    ext v
    simp
  rw [h2] at h1'
  rw [← card_exact_eq, h1']
  push_cast
  ring

/-- **Obligation O1.** `[SL₂(ℤ) : ±Γ₁(M)] · scalTrace = A1` (the Cohen-Oesterle scalar term), `M ≥ 3`. -/
theorem index_mul_scalTrace (hM : 3 ≤ M) (k n : ℕ) (δ : ZMod M) :
    ((pmSL (Gamma1 M)).index : ℂ) * scalTrace M k n δ = ((S3.scalarG1 M k n δ : ℚ) : ℂ) := by
  have hI := two_mul_index (M := M) hM
  have hI' : ((pmSL (Gamma1 M)).index : ℂ) =
      ((S3.dedekindPsi M * Nat.totient M / 2 : ℚ) : ℂ) := by
    rw [← hI]
    push_cast
    ring
  rw [hI', scalTrace, S3.scalarG1, S3.charSum, if_neg (by omega : ¬ M ≤ 2)]
  by_cases hs : Nat.sqrt n * Nat.sqrt n = n
  · rw [if_pos hs, if_pos hs]
    have e : (((δ.val : ℤ) * ((Nat.sqrt n : ℕ) : ℤ) : ℤ) : ZMod M) = (Nat.sqrt n : ZMod M) * δ := by
      rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm]
    rw [e]
    push_cast
    simp only [apply_ite (Rat.cast : ℚ → ℂ), Rat.cast_one, Rat.cast_zero]
    ring
  · rw [if_neg hs, if_neg hs]
    simp

end Index

end RamanujanPetersson.HypPar


