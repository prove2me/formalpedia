-- Prove2me | Definitions.Def_RPLib_S4_TsenZero
-- name    : RPLib_S4_TsenZero
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T01:28:32.975429+00:00
-- url     : https://prove2.me/theorems/83d109d4-2fee-4206-b750-c8478036fff4
-- title:
--   Tsen's theorem, part 1: common nonzero zeros over an algebraically closed field; the $C_1$ property
-- statement:
--   Over an algebraically closed field $k$, $m$ polynomials without constant term in $n > m$ variables have a common nonzero zero in $k^n$ (Krull's height theorem and the Nullstellensatz). Definition of the (strong) $C_1$ property `IsC1 K`. Here a field $K$ is called $C_1$ (in the strong sense) if every polynomial $f \in K[x_1,\dots,x_n]$ of total degree $< n$ with $f(0) = 0$ has a zero $x \ne 0$ in $K^n$ (`RamanujanPetersson.Tsen.IsC1`); for forms this is the classical $C_1$ property (`IsC1.exists_zero_of_isHomogeneous`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (field-theory layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   S. Lang, On quasi algebraic closure, Ann. of Math. (2) 55 (1952), 373-390, doi:10.2307/1969785; M. J. Greenberg, Lectures on Forms in Many Variables, Benjamin 1969, Chapter 2

import Mathlib

set_option autoImplicit false

/-!
# S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property

* `exists_common_zero`: over an algebraically closed field `k`, `m` polynomials in `n > m` variables without constant
  term have a common nonzero zero (Krull's height theorem + the Nullstellensatz).
* `IsC1 K`: every polynomial in `n` variables over `K` with total degree `< n` and constant term `0` has a nonzero zero.
  (`IsC1.exists_zero_of_isHomogeneous`: the classical `C₁` property for forms.)
-/

namespace RamanujanPetersson.Tsen

open MvPolynomial

section Zero

variable {k : Type*} [Field k]

theorem ringKrullDim_mvPolynomial_fin (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem finiteRingKrullDim_mvPolynomial_fin (n : ℕ) :
    FiniteRingKrullDim (MvPolynomial (Fin n) k) := by
  rw [FiniteRingKrullDim, Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top]
  have h := ringKrullDim_mvPolynomial_fin (k := k) n
  rw [ringKrullDim] at h
  rw [h]
  exact ⟨WithBot.natCast_ne_bot n, by
    intro h'
    have : ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by simpa using h'
    exact ENat.natCast_ne_top n (WithBot.coe_injective this)⟩

/-- Evaluation after the translation `X j ↦ X j - a j`. -/
theorem eval_translate {n : ℕ} (a x : Fin n → k) (p : MvPolynomial (Fin n) k) :
    eval x (aeval (fun j => X j - C (a j)) p) = eval (fun j => x j - a j) p := by
  have h := congrArg (fun φ : MvPolynomial (Fin n) k →ₐ[k] k => φ p)
    (MvPolynomial.comp_aeval (fun j => (X j - C (a j) : MvPolynomial (Fin n) k)) (aeval x))
  simp only [AlgHom.comp_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply] at h
  rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
  exact h

/-- **Common zeros.** Over an algebraically closed field, `m` polynomials without constant term in `n > m` variables
have a common nonzero zero. -/
theorem exists_common_zero [IsAlgClosed k] {n m : ℕ} (hmn : m < n) (f : Fin m → MvPolynomial (Fin n) k)
    (hf : ∀ i, constantCoeff (f i) = 0) : ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, eval x (f i) = 0 := by
  classical
  by_contra hne
  push Not at hne
  have := finiteRingKrullDim_mvPolynomial_fin (k := k) n
  obtain ⟨M, hM, hMh⟩ := Ideal.exists_isMaximal_height (R := MvPolynomial (Fin n) k)
  obtain ⟨a, rfl⟩ := eq_vanishingIdeal_singleton_of_isMaximal k hM
  set τ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k := aeval (fun j => X j - C (a j))
  set s : Finset (MvPolynomial (Fin n) k) := Finset.univ.image (fun i => τ (f i))
  -- the zero locus of `span s` is `{a}`
  have hZ : zeroLocus k (Ideal.span (s : Set (MvPolynomial (Fin n) k))) = {a} := by
    ext x
    rw [zeroLocus_span, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hxa
      have hsub : (fun j => x j - a j) ≠ 0 := by
        intro h0
        apply hxa
        funext j
        have := congrFun h0 j
        simpa [sub_eq_zero] using this
      obtain ⟨i, hi⟩ := hne _ hsub
      apply hi
      have := hx (τ (f i)) (by simp [s])
      rw [aeval_eq_eval, eval_translate] at this
      exact this
    · rintro rfl p hp
      simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hp
      obtain ⟨i, rfl⟩ := hp
      rw [aeval_eq_eval, eval_translate]
      have : (fun j => x j - x j) = (0 : Fin n → k) := by funext j; simp
      rw [this, eval_zero]
      exact hf i
  have hrad : (Ideal.span (s : Set (MvPolynomial (Fin n) k))).radical = vanishingIdeal k {a} := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k), hZ]
  have hmin : vanishingIdeal k {a} ∈ (Ideal.span (s : Set (MvPolynomial (Fin n) k))).minimalPrimes := by
    refine ⟨⟨hM.isPrime, hrad ▸ Ideal.le_radical⟩, ?_⟩
    rintro q ⟨hq, hsq⟩ _
    rw [← hrad]
    exact (Ideal.IsPrime.radical_le_iff hq).2 hsq
  have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have h2 : s.card ≤ m := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := fun i => τ (f i)))
  rw [ringKrullDim_mvPolynomial_fin] at hMh
  have h3 : (vanishingIdeal k {a}).height = (n : ℕ∞) := by exact_mod_cast hMh
  rw [h3] at h1
  have h4 : n ≤ s.card := by exact_mod_cast h1
  omega

end Zero

/-- The (strong) **`C₁` property**: every polynomial in `n` variables of total degree `< n` without constant term has a
nonzero zero. Over a field it implies the classical `C₁` property for forms (`IsC1.exists_zero_of_isHomogeneous`). -/
def IsC1 (K : Type*) [Field K] : Prop :=
  ∀ (n : ℕ) (f : MvPolynomial (Fin n) K), f.totalDegree < n → constantCoeff f = 0 →
    ∃ x : Fin n → K, x ≠ 0 ∧ eval x f = 0

theorem IsC1.exists_zero_of_isHomogeneous {K : Type*} [Field K] (hK : IsC1 K) {n d : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) (hd : 0 < d) (hdn : d < n) :
    ∃ x : Fin n → K, x ≠ 0 ∧ eval x f = 0 := by
  refine hK n f (lt_of_le_of_lt hf.totalDegree_le hdn) ?_
  have := hf.coeff_eq_zero (d := 0) (by simp; omega)
  simpa [constantCoeff] using this

end RamanujanPetersson.Tsen


