-- Prove2me | Definitions.Def_RPLib_S3_HypParM
-- name    : RPLib_S3_HypParM
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:37:20.23121+00:00
-- url     : https://prove2.me/theorems/6bf0e8a5-1f5f-4350-98ae-b1612ac1a571
-- title:
--   The Eichler-Selberg trace formula, hyperbolic part M: matching the hyperbolic term
-- statement:
--   Counting residues $x$ mod $M$ with $x \equiv e \pmod \tau$, $x \equiv f \pmod{M/\tau}$ and a divisibility condition, and the resulting identity between the sum of level counts over the pairs $(a, d) = (\sigma e, \sigma n/e)$, $\sigma = \pm 1$, and the inner $\tau$-sum of the hyperbolic term $A_3$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977

import Mathlib
import Definitions.Def_RPLib_S3_HypParH

/-!
# S3-HypParTerms, part M (O8, steps H1, H3, H5, H6): the `hypG1` match

* `LFs M dv σ e f = Σ_{τ ∣ M} [τ ∣ dv e - σ ∧ M/τ ∣ dv f - σ] φ(τ) φ(M/τ)` and its symmetry `LFs_symm`.
* `xcount` (H3): `#{x < M : x ≡ e (τ), x ≡ f (M/τ), M/g ∣ dv x - σ} = g [τ ∣ dv e - σ ∧ M/τ ∣ dv f - σ]`.
* `inner_eq` (H5): the inner `τ`-sum of `hypG1` equals `(1/2)(LFs 1 e f + ε LFs (-1) e f)`.
* `sum_levelCount_LFs` (H1): `Σ_b levelCount M D [[σe, b], [0, σf]] = M LFs σ e f` when `D ≡ e f dv (M)`.
* `sigma_sum`, `sym_min`, **`hyp_pairs_eq`** (H6): the sum over the pairs `(a, d) = (σe, σ n/e)` of
  `(1/2) A(a,d) a^{k-1} (sign(a-d) - sign(a+d))`, `A(a,d) = (1/2M) Σ_b levelCount`, equals `hypG1 M k n δ`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

section ArithM

/-- The level factor `Σ_{τ ∣ M} [τ ∣ dv e - σ ∧ M/τ ∣ dv f - σ] φ(τ) φ(M/τ)`. -/
def LFs (M : ℕ) (dv σ e f : ℤ) : ℕ :=
  ∑ τ ∈ M.divisors, if (τ : ℤ) ∣ dv * e - σ ∧ ((M / τ : ℕ) : ℤ) ∣ dv * f - σ then
    Nat.totient τ * Nat.totient (M / τ) else 0

lemma LFs_symm (M : ℕ) (dv σ e f : ℤ) : LFs M dv σ e f = LFs M dv σ f e := by
  unfold LFs
  conv_lhs => rw [← Nat.sum_div_divisors M]
  refine Finset.sum_congr rfl (fun τ hτ => ?_)
  have hM0 : M ≠ 0 := (Nat.mem_divisors.1 hτ).2
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hτ) hM0]
  exact if_congr and_comm (mul_comm _ _) rfl

/-- `LF = (1/2)(LFs 1 + (-1)^k LFs (-1))`, the full level factor of `hypG1` at `(e, f)`. -/
def LF (M : ℕ) (dv : ℤ) (k : ℕ) (e f : ℤ) : ℚ :=
  1 / 2 * ((LFs M dv 1 e f : ℚ) + (-1 : ℚ) ^ k * (LFs M dv (-1) e f : ℚ))

lemma LF_symm (M : ℕ) (dv : ℤ) (k : ℕ) (e f : ℤ) : LF M dv k e f = LF M dv k f e := by
  unfold LF
  rw [LFs_symm M dv 1 e f, LFs_symm M dv (-1) e f]

lemma mod_iff {N dv U σ e y : ℤ} (hN : N ∣ dv * U - 1) :
    (N ∣ e - y ∧ N ∣ dv * y - σ) ↔ (N ∣ dv * e - σ ∧ N ∣ y - σ * U) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [show dv * e - σ = (dv * y - σ) + dv * (e - y) by ring]
      exact dvd_add h2 (dvd_mul_of_dvd_right h1 _)
    · rw [show y - σ * U = U * (dv * y - σ) - y * (dv * U - 1) by ring]
      exact dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right hN _)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [show e - y = (U * (dv * e - σ) - e * (dv * U - 1)) - (y - σ * U) by ring]
      exact dvd_sub (dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right hN _)) h2
    · rw [show dv * y - σ = dv * (y - σ * U) + σ * (dv * U - 1) by ring]
      exact dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right hN _)

/-- **H3.** The `x`-count of `hypG1`: for `τ ∣ M`, `g = gcd(τ, M/τ)`, `U` an inverse of `dv` mod `M`,
`#{x < M : x ≡ e (τ), x ≡ f (M/τ), M/g ∣ dv x - σ} = g [τ ∣ dv e - σ ∧ M/τ ∣ dv f - σ]`. -/
lemma xcount {M τ : ℕ} (hM : 0 < M) (hτ : τ ∣ M) (dv U σ e f : ℤ) (hU : (M : ℤ) ∣ dv * U - 1) :
    ((range M).filter fun x : ℕ => ((x : ℤ) ≡ e [ZMOD (τ : ℤ)] ∧
        (x : ℤ) ≡ f [ZMOD ((M / τ : ℕ) : ℤ)]) ∧
        ((M / Nat.gcd τ (M / τ) : ℕ) : ℤ) ∣ dv * x - σ).card =
      if (τ : ℤ) ∣ dv * e - σ ∧ ((M / τ : ℕ) : ℤ) ∣ dv * f - σ then Nat.gcd τ (M / τ) else 0 := by
  have hgM : Nat.gcd τ (M / τ) ∣ M := (Nat.gcd_dvd_left _ _).trans hτ
  have hLM : M / Nat.gcd τ (M / τ) ∣ M := Nat.div_dvd_of_dvd hgM
  have hLd : ∀ y : ℤ, ((M / Nat.gcd τ (M / τ) : ℕ) : ℤ) ∣ y ↔
      (τ : ℤ) ∣ y ∧ ((M / τ : ℕ) : ℤ) ∣ y := by
    intro y
    rw [← lcm_div_eq hτ]
    exact intDvd_lcm_iff _ _ y
  have hU1 : (τ : ℤ) ∣ dv * U - 1 := (Int.natCast_dvd_natCast.2 hτ).trans hU
  have hU2 : ((M / τ : ℕ) : ℤ) ∣ dv * U - 1 :=
    (Int.natCast_dvd_natCast.2 (Nat.div_dvd_of_dvd hτ)).trans hU
  have key : ∀ x ∈ range M, (((x : ℤ) ≡ e [ZMOD (τ : ℤ)] ∧ (x : ℤ) ≡ f [ZMOD ((M / τ : ℕ) : ℤ)]) ∧
        ((M / Nat.gcd τ (M / τ) : ℕ) : ℤ) ∣ dv * x - σ) ↔
      (((τ : ℤ) ∣ dv * e - σ ∧ ((M / τ : ℕ) : ℤ) ∣ dv * f - σ) ∧
        ((M / Nat.gcd τ (M / τ) : ℕ) : ℤ) ∣ (x : ℤ) - σ * U) := by
    intro x _
    rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, hLd, hLd]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      obtain ⟨a1, a2⟩ := (mod_iff hU1).1 ⟨h1, h3⟩
      obtain ⟨b1, b2⟩ := (mod_iff hU2).1 ⟨h2, h4⟩
      exact ⟨⟨a1, b1⟩, a2, b2⟩
    · rintro ⟨⟨a1, b1⟩, a2, b2⟩
      obtain ⟨h1, h3⟩ := (mod_iff hU1).2 ⟨a1, a2⟩
      obtain ⟨h2, h4⟩ := (mod_iff hU2).2 ⟨b1, b2⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
  rw [Finset.filter_congr key]
  by_cases hb : (τ : ℤ) ∣ dv * e - σ ∧ ((M / τ : ℕ) : ℤ) ∣ dv * f - σ
  · have e2 : ((range M).filter fun x : ℕ => ((τ : ℤ) ∣ dv * e - σ ∧ ((M / τ : ℕ) : ℤ) ∣ dv * f - σ) ∧
        ((M / Nat.gcd τ (M / τ) : ℕ) : ℤ) ∣ (x : ℤ) - σ * U) =
        (range M).filter fun x : ℕ => ((M / Nat.gcd τ (M / τ) : ℕ) : ℤ) ∣ (x : ℤ) - σ * U :=
      Finset.filter_congr fun x _ => and_iff_right hb
    rw [if_pos hb, e2, card_residue hM hLM, Nat.div_div_self hgM hM.ne']
  · rw [if_neg hb, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    exact hb hx.1

lemma cast_ite_one_mul (B : Prop) [Decidable B] (a : ℕ) :
    (((if B then a else 0 : ℕ)) : ℚ) = (a : ℚ) * (if B then 1 else 0) := by
  split_ifs <;> simp

/-- **H5.** The inner `τ`-sum of `hypG1` at `(e, f)`: `(1/2)(LFs 1 e f + ε LFs (-1) e f)`. -/
lemma inner_eq {M : ℕ} (hM : 0 < M) (dv U ε e f : ℤ) (hU : (M : ℤ) ∣ dv * U - 1)
    (hε : ε = 1 ∨ ε = -1) :
    ∑ τ ∈ M.divisors, (Nat.totient (Nat.gcd τ (M / τ)) : ℚ) / (Nat.gcd τ (M / τ) : ℚ) *
      ∑ x ∈ (range M).filter
          (fun x : ℕ => (x : ℤ) ≡ e [ZMOD (τ : ℤ)] ∧ (x : ℤ) ≡ f [ZMOD ((M / τ : ℕ) : ℤ)]),
        S3.charSum (M / Nat.gcd τ (M / τ)) (dv * x) ε =
    1 / 2 * ((LFs M dv 1 e f : ℚ) + (ε : ℚ) * (LFs M dv (-1) e f : ℚ)) := by
  have hterm : ∀ τ ∈ M.divisors,
      (Nat.totient (Nat.gcd τ (M / τ)) : ℚ) / (Nat.gcd τ (M / τ) : ℚ) *
        ∑ x ∈ (range M).filter
            (fun x : ℕ => (x : ℤ) ≡ e [ZMOD (τ : ℤ)] ∧ (x : ℤ) ≡ f [ZMOD ((M / τ : ℕ) : ℤ)]),
          S3.charSum (M / Nat.gcd τ (M / τ)) (dv * x) ε =
      1 / 2 * (((if (τ : ℤ) ∣ dv * e - 1 ∧ ((M / τ : ℕ) : ℤ) ∣ dv * f - 1 then
            Nat.totient τ * Nat.totient (M / τ) else 0 : ℕ) : ℚ) +
          (ε : ℚ) * ((if (τ : ℤ) ∣ dv * e - -1 ∧ ((M / τ : ℕ) : ℤ) ∣ dv * f - -1 then
            Nat.totient τ * Nat.totient (M / τ) else 0 : ℕ) : ℚ)) := by
    intro τ hτm
    have hτ : τ ∣ M := Nat.dvd_of_mem_divisors hτm
    have hτ0 : 0 < τ := Nat.pos_of_dvd_of_pos hτ hM
    have hg0 : 0 < Nat.gcd τ (M / τ) := Nat.gcd_pos_of_pos_left _ hτ0
    have hgM : Nat.gcd τ (M / τ) ∣ M := (Nat.gcd_dvd_left _ _).trans hτ
    have hL1 : 1 ≤ M / Nat.gcd τ (M / τ) := Nat.div_pos (Nat.le_of_dvd hM hgM) hg0
    have h4 : (Nat.totient (Nat.gcd τ (M / τ)) : ℚ) * (Nat.totient (M / Nat.gcd τ (M / τ)) : ℚ) =
        (Nat.totient τ : ℚ) * (Nat.totient (M / τ) : ℚ) := by
      exact_mod_cast totient_gcd_mul_totient_div hM hτ
    have hx : ∀ σ : ℤ, ∑ x ∈ (range M).filter
          (fun x : ℕ => (x : ℤ) ≡ e [ZMOD (τ : ℤ)] ∧ (x : ℤ) ≡ f [ZMOD ((M / τ : ℕ) : ℤ)]),
        (if ((M / Nat.gcd τ (M / τ) : ℕ) : ℤ) ∣ dv * x - σ then (1 : ℚ) else 0) =
        (Nat.gcd τ (M / τ) : ℚ) *
          (if (τ : ℤ) ∣ dv * e - σ ∧ ((M / τ : ℕ) : ℤ) ∣ dv * f - σ then 1 else 0) := by
      intro σ
      rw [Finset.sum_boole, Finset.filter_filter, xcount hM hτ dv U σ e f hU]
      split_ifs <;> simp
    have hplus : ∑ x ∈ (range M).filter
          (fun x : ℕ => (x : ℤ) ≡ e [ZMOD (τ : ℤ)] ∧ (x : ℤ) ≡ f [ZMOD ((M / τ : ℕ) : ℤ)]),
        (if ((M / Nat.gcd τ (M / τ) : ℕ) : ℤ) ∣ dv * x + 1 then (1 : ℚ) else 0) =
        (Nat.gcd τ (M / τ) : ℚ) *
          (if (τ : ℤ) ∣ dv * e - -1 ∧ ((M / τ : ℕ) : ℤ) ∣ dv * f - -1 then 1 else 0) := by
      rw [← hx (-1)]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [sub_neg_eq_add]
    rw [Finset.sum_congr rfl (fun (x : ℕ) _ => charSum_eq _ hL1 (dv * x) ε hε), ← Finset.mul_sum,
      Finset.sum_add_distrib, ← Finset.mul_sum, hx 1, hplus, cast_ite_one_mul, cast_ite_one_mul,
      Nat.cast_mul, ← h4]
    have hg0' : (Nat.gcd τ (M / τ) : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [LFs, Nat.cast_sum]

/-- **H1.** `Σ_b levelCount M D [[σe, b], [0, σf]] = M LFs σ e f` when `D ≡ e f dv (M)` and `e, f` are
prime to `M`. -/
theorem sum_levelCount_LFs {M : ℕ} [NeZero M] (D dv σ e f : ℤ) (hD : (M : ℤ) ∣ D - e * f * dv)
    (he : IsCoprime e (M : ℤ)) (hf : IsCoprime f (M : ℤ)) :
    ∑ b : ZMod M, S3.levelCount M (D : ZMod M) (ut (σ * e) (b.val : ℤ) (σ * f)) =
      M * LFs M dv σ e f := by
  rw [sum_levelCount_ut]
  congr 1
  unfold LFs
  conv_rhs => rw [← Nat.sum_div_divisors M]
  refine Finset.sum_congr rfl (fun h hh => ?_)
  have hhM : h ∣ M := Nat.dvd_of_mem_divisors hh
  have hM0 : M ≠ 0 := NeZero.ne M
  rw [Nat.div_div_self hhM hM0]
  have hN1 : (h : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.2 hhM
  have hN2 : ((M / h : ℕ) : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.2 (Nat.div_dvd_of_dvd hhM)
  have i1 : (h : ℤ) ∣ D - σ * e ↔ (h : ℤ) ∣ dv * f - σ := by
    have hc : IsCoprime (h : ℤ) e := (he.of_isCoprime_of_dvd_right hN1).symm
    constructor
    · intro hx
      have h2 : (h : ℤ) ∣ e * (dv * f - σ) := by
        rw [show e * (dv * f - σ) = (D - σ * e) - (D - e * f * dv) by ring]
        exact dvd_sub hx (hN1.trans hD)
      exact hc.dvd_of_dvd_mul_left h2
    · intro hx
      rw [show D - σ * e = e * (dv * f - σ) + (D - e * f * dv) by ring]
      exact dvd_add (dvd_mul_of_dvd_right hx _) (hN1.trans hD)
  have i2 : ((M / h : ℕ) : ℤ) ∣ D - σ * f ↔ ((M / h : ℕ) : ℤ) ∣ dv * e - σ := by
    have hc : IsCoprime ((M / h : ℕ) : ℤ) f := (hf.of_isCoprime_of_dvd_right hN2).symm
    constructor
    · intro hx
      have h2 : ((M / h : ℕ) : ℤ) ∣ f * (dv * e - σ) := by
        rw [show f * (dv * e - σ) = (D - σ * f) - (D - e * f * dv) by ring]
        exact dvd_sub hx (hN2.trans hD)
      exact hc.dvd_of_dvd_mul_left h2
    · intro hx
      rw [show D - σ * f = f * (dv * e - σ) + (D - e * f * dv) by ring]
      exact dvd_add (dvd_mul_of_dvd_right hx _) (hN2.trans hD)
  exact if_congr (by rw [i1, i2]; exact and_comm) (mul_comm _ _) rfl

/-- The two signs `σ = ±1` of one divisor pair. -/
lemma sigma_sum {M : ℕ} (hM : 0 < M) (k : ℕ) (hk : 1 ≤ k) (e f : ℕ) (he : 0 < e) (hf : 0 < f)
    (S : ℤ → ℕ) (L1 L2 : ℕ) (hS1 : S 1 = M * L1) (hS2 : S (-1) = M * L2) :
    ∑ σ ∈ ({1, -1} : Finset ℤ), (1 / 2 : ℚ) * ((S σ : ℚ) / (2 * (M : ℚ))) *
        ((σ * e : ℤ) : ℚ) ^ (k - 1) *
        (((σ * e - σ * f : ℤ).sign : ℚ) - ((σ * e + σ * f : ℤ).sign : ℚ)) =
      1 / 4 * (e : ℚ) ^ (k - 1) * ((((e : ℤ) - f).sign : ℚ) - 1) * ((L1 : ℚ) + (-1) ^ k * (L2 : ℚ)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_pair (by norm_num : (1 : ℤ) ≠ -1), hS1, hS2, Nat.add_sub_cancel]
  have s1 : (1 * (e : ℤ) + 1 * f).sign = 1 := Int.sign_eq_one_of_pos (by omega)
  have s2 : (-1 * (e : ℤ) + -1 * f).sign = -1 := Int.sign_eq_neg_one_of_neg (by omega)
  have s3 : (-1 * (e : ℤ) - -1 * f).sign = -((e : ℤ) - f).sign := by
    rw [show -1 * (e : ℤ) - -1 * f = -((e : ℤ) - f) by ring, Int.sign_neg]
  have s4 : 1 * (e : ℤ) - 1 * f = (e : ℤ) - f := by ring
  have hp : (((-1 * (e : ℤ)) : ℤ) : ℚ) ^ j = (-1) ^ j * (e : ℚ) ^ j := by
    push_cast
    rw [mul_pow]
  rw [s1, s2, s3, s4, hp]
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  field_simp
  ring

/-- Symmetrisation over `e ↦ n/e`: `Σ_e e^m (1 - sign(e - n/e)) F e = Σ_e min(e, n/e)^m F e` when
`F (n/e) = F e`. -/
lemma sym_min (n m : ℕ) (hn : 0 < n) (F : ℕ → ℚ) (hF : ∀ e ∈ n.divisors, F (n / e) = F e) :
    ∑ e ∈ n.divisors, (e : ℚ) ^ m * (1 - (((e : ℤ) - ((n / e : ℕ) : ℤ)).sign : ℚ)) * F e =
      ∑ e ∈ n.divisors, ((if e ≤ n / e then e else n / e : ℕ) : ℚ) ^ m * F e := by
  have h2 := Nat.sum_div_divisors n
    (fun e : ℕ => (e : ℚ) ^ m * (1 - (((e : ℤ) - ((n / e : ℕ) : ℤ)).sign : ℚ)) * F e)
  have key : ∀ e ∈ n.divisors,
      (e : ℚ) ^ m * (1 - (((e : ℤ) - ((n / e : ℕ) : ℤ)).sign : ℚ)) * F e +
        ((n / e : ℕ) : ℚ) ^ m * (1 - ((((n / e : ℕ) : ℤ) - ((n / (n / e) : ℕ) : ℤ)).sign : ℚ)) *
          F (n / e) =
      2 * (((if e ≤ n / e then e else n / e : ℕ) : ℚ) ^ m * F e) := by
    intro e he
    have hen : e ∣ n := Nat.dvd_of_mem_divisors he
    rw [Nat.div_div_self hen hn.ne', hF e he]
    rcases lt_trichotomy e (n / e) with h | h | h
    · have s1 : ((e : ℤ) - ((n / e : ℕ) : ℤ)).sign = -1 :=
        Int.sign_eq_neg_one_of_neg (sub_neg.2 (by exact_mod_cast h))
      have s2 : (((n / e : ℕ) : ℤ) - (e : ℤ)).sign = 1 :=
        Int.sign_eq_one_of_pos (sub_pos.2 (by exact_mod_cast h))
      rw [s1, s2, if_pos h.le]
      push_cast
      ring
    · rw [← h, if_pos le_rfl]
      simp only [sub_self, Int.sign_zero, Int.cast_zero, sub_zero, mul_one]
      ring
    · have s1 : ((e : ℤ) - ((n / e : ℕ) : ℤ)).sign = 1 :=
        Int.sign_eq_one_of_pos (sub_pos.2 (by exact_mod_cast h))
      have s2 : (((n / e : ℕ) : ℤ) - (e : ℤ)).sign = -1 :=
        Int.sign_eq_neg_one_of_neg (sub_neg.2 (by exact_mod_cast h))
      rw [s1, s2, if_neg (not_le.2 h)]
      push_cast
      ring
  calc ∑ e ∈ n.divisors, (e : ℚ) ^ m * (1 - (((e : ℤ) - ((n / e : ℕ) : ℤ)).sign : ℚ)) * F e
      = 1 / 2 * ∑ e ∈ n.divisors, ((e : ℚ) ^ m * (1 - (((e : ℤ) - ((n / e : ℕ) : ℤ)).sign : ℚ)) * F e +
        ((n / e : ℕ) : ℚ) ^ m * (1 - ((((n / e : ℕ) : ℤ) - ((n / (n / e) : ℕ) : ℤ)).sign : ℚ)) *
          F (n / e)) := by
        rw [Finset.sum_add_distrib, h2]
        ring
    _ = 1 / 2 * ∑ e ∈ n.divisors, 2 * (((if e ≤ n / e then e else n / e : ℕ) : ℚ) ^ m * F e) := by
        rw [Finset.sum_congr rfl key]
    _ = _ := by
        rw [← Finset.mul_sum]
        ring

/-- **H6.** The sum over the divisor pairs `(a, d) = (σ e, σ n/e)` (`e ∣ n`, `σ = ±1`) of
`(1/2) A(a,d) a^{k-1} (sign(a - d) - sign(a + d))`, with `A(a,d) = (1/(2M)) Σ_b levelCount M δ'' [[a,b],[0,d]]`
and `δ'' ≡ n δ`, is the Cohen-Oesterle term `hypG1 M k n δ`. -/
theorem hyp_pairs_eq {M : ℕ} [NeZero M] {k n : ℕ} (hk : 1 ≤ k) (hn : 0 < n) (hnM : Nat.Coprime n M)
    (δ : ZMod M) (U : ℤ) (hU : (M : ℤ) ∣ (δ.val : ℤ) * U - 1) (D : ℤ)
    (hD : (M : ℤ) ∣ D - n * (δ.val : ℤ)) :
    ∑ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
      (1 / 2 : ℚ) * (((∑ b : ZMod M, S3.levelCount M (D : ZMod M)
          (ut (σ * e) (b.val : ℤ) (σ * ((n / e : ℕ) : ℤ))) : ℕ) : ℚ) / (2 * (M : ℚ))) *
        ((σ * e : ℤ) : ℚ) ^ (k - 1) *
        (((σ * e - σ * ((n / e : ℕ) : ℤ)).sign : ℚ) - ((σ * e + σ * ((n / e : ℕ) : ℤ)).sign : ℚ)) =
    S3.hypG1 M k n δ := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have step1 : ∀ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
      (1 / 2 : ℚ) * (((∑ b : ZMod M, S3.levelCount M (D : ZMod M)
          (ut (σ * e) (b.val : ℤ) (σ * ((n / e : ℕ) : ℤ))) : ℕ) : ℚ) / (2 * (M : ℚ))) *
        ((σ * e : ℤ) : ℚ) ^ (k - 1) *
        (((σ * e - σ * ((n / e : ℕ) : ℤ)).sign : ℚ) - ((σ * e + σ * ((n / e : ℕ) : ℤ)).sign : ℚ)) =
      -(1 / 2) * ((e : ℚ) ^ (k - 1) * (1 - (((e : ℤ) - ((n / e : ℕ) : ℤ)).sign : ℚ)) *
        LF M (δ.val : ℤ) k e ((n / e : ℕ) : ℤ)) := by
    intro e he
    have hen : e ∣ n := Nat.dvd_of_mem_divisors he
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos hen hn
    have hf0 : 0 < n / e := Nat.div_pos (Nat.le_of_dvd hn hen) he0
    have hce : IsCoprime (e : ℤ) (M : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_dvd_left hen hnM)
    have hcf : IsCoprime ((n / e : ℕ) : ℤ) (M : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hen) hnM)
    have hn' : (n : ℤ) = (e : ℤ) * ((n / e : ℕ) : ℤ) := by
      exact_mod_cast (Nat.mul_div_cancel' hen).symm
    have hD' : (M : ℤ) ∣ D - (e : ℤ) * ((n / e : ℕ) : ℤ) * (δ.val : ℤ) := by
      rw [← hn']
      exact hD
    have hsig := sigma_sum hM k hk e (n / e) he0 hf0
      (fun σ : ℤ => ∑ b : ZMod M, S3.levelCount M (D : ZMod M)
        (ut (σ * e) (b.val : ℤ) (σ * ((n / e : ℕ) : ℤ))))
      (LFs M (δ.val : ℤ) 1 e ((n / e : ℕ) : ℤ)) (LFs M (δ.val : ℤ) (-1) e ((n / e : ℕ) : ℤ))
      (sum_levelCount_LFs D (δ.val : ℤ) 1 e ((n / e : ℕ) : ℤ) hD' hce hcf)
      (sum_levelCount_LFs D (δ.val : ℤ) (-1) e ((n / e : ℕ) : ℤ) hD' hce hcf)
    refine hsig.trans ?_
    unfold LF
    ring
  have hF : ∀ e ∈ n.divisors,
      LF M (δ.val : ℤ) k ((n / e : ℕ) : ℤ) ((n / (n / e) : ℕ) : ℤ) =
        LF M (δ.val : ℤ) k (e : ℤ) ((n / e : ℕ) : ℤ) := by
    intro e he
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) hn.ne', LF_symm]
  rw [Finset.sum_congr rfl step1, ← Finset.mul_sum,
    sym_min n (k - 1) hn (fun e : ℕ => LF M (δ.val : ℤ) k (e : ℤ) ((n / e : ℕ) : ℤ)) hF]
  unfold S3.hypG1
  congr 1
  refine Finset.sum_congr rfl (fun e _ => ?_)
  congr 1
  rw [inner_eq hM (δ.val : ℤ) U ((-1) ^ k) (e : ℤ) ((n / e : ℕ) : ℤ) hU (neg_one_pow_eq_or ℤ k)]
  unfold LF
  push_cast
  ring

end ArithM

end RamanujanPetersson.HypPar


