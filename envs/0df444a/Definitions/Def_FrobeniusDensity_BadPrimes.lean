-- Prove2me | Definitions.Def_FrobeniusDensity_BadPrimes
-- name    : FrobeniusDensity_BadPrimes
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/c4925a6c-3da6-58cc-92ed-d3748c60ec56
-- title:
--   Ramified rational primes and Frobenius conjugacy helpers
-- statement:
--   Fix a number field $L$. The section on ramification first records two elementary counts: `card_quotient_ratPrimeIdeal` says that for any $\ell \in \mathbb{N}$ the quotient of $\mathbb{Z}$ by `ratPrimeIdeal ℓ` $= (\ell)$ has cardinality $\ell$ (with the `Nat.card` convention giving $0$ for infinite quotients), and `card_quotient_under_int` transfers this to any ideal $Q$ of $\mathcal{O}_L$ lying over $(\ell)$: $\#\bigl(\mathbb{Z}/(Q \cap \mathbb{Z})\bigr) = \ell$. Two finiteness lemmas follow: `finite_setOf_dvd`, that only finitely many height-one primes of $\mathcal{O}_K$ divide a given nonzero ideal (via normalised factors), and `exists_smul_ne`, that any $g \neq 1$ in $\mathrm{Aut}_{\mathbb{Q}}(L)$ moves some algebraic integer, since $L$ is the fraction field of $\mathcal{O}_L$. Combining them, `finite_setOf_inertia_ne_bot_heightOneSpectrum` shows that the set of $v$ in the height-one spectrum of $\mathcal{O}_L$ with nontrivial inertia subgroup $I(v) \le (L \simeq_{\mathbb{Q}} L)$ is finite. The definition `badPrimes L : Finset ℕ` is then the image of that finite set under $v \mapsto \#(\mathbb{Z}/(v \cap \mathbb{Z}))$, i.e. the residue characteristics of the ramified primes, with $0$ and $1$ inserted as padding. Accordingly `inertia_eq_bot_of_notMem_badPrimes`: for $\ell$ prime with $\ell \notin$ `badPrimes L`, every prime $Q$ of $\mathcal{O}_L$ over $(\ell)$ has trivial inertia.
--
--   Two further groups of lemmas unfold imported notions. `degOneCount_of_prime` and `degOneCount_of_not_prime` unfold the `if`-definition of `degOneCount K ℓ`, namely the `ncard` of the set of primes of $\mathcal{O}_K$ over $(\ell)$ with residue cardinality exactly $\ell$ when $\ell$ is prime, and $0$ otherwise. For $L/\mathbb{Q}$ Galois, `isConj_arithFrobAt_of_liesOver` says the arithmetic Frobenius elements at any two primes $Q_1, Q_2$ over $(\ell)$ are conjugate in $\mathrm{Gal}(L/\mathbb{Q})$, and `realizesCyclicAt_of_exists` deduces the project's predicate `RealizesCyclicAt L σ ℓ` (for every prime over $(\ell)$, some $\sigma^k$ with $k$ coprime to $\mathrm{ord}(\sigma)$ is conjugate to the Frobenius there) from the existence of a single prime $Q_0$ over $(\ell)$ with that property.
--
--   **Relation to Mathlib.** The inertia subgroup `Ideal.inertia` and the arithmetic Frobenius `arithFrobAt`, together with the conjugacy of Frobenius elements over a common base prime, are taken from Mathlib; the finite set `badPrimes` of ramified residue characteristics and its finiteness proof (via moved integers and divisors of a nonzero ideal, rather than via the discriminant) are the project's own.
--
--   **Where it is used.** These are the ramification bookkeeping and Frobenius-conjugacy inputs for the Frobenius density argument that supplies Taylor–Wiles primes: the counting of degree-one primes and its Möbius-weighted Dirichlet series are analysed only at primes $\ell$ outside a given finite set together with `badPrimes L`, where all primes of $L$ above $\ell$ are unramified and Frobenius is a well-defined conjugacy class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FrobeniusDensity_BadPrimes.lean

import Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Data.ZMod.QuotientRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace FrobeniusDensity

open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid

theorem card_quotient_ratPrimeIdeal (ℓ : ℕ) :
    Nat.card (ℤ ⧸ ratPrimeIdeal ℓ) = ℓ := by
  rw [ratPrimeIdeal, Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]

theorem card_quotient_under_int {L : Type*} [Field L] [NumberField L] {ℓ : ℕ}
    (Q : Ideal (𝓞 L)) [Q.LiesOver (ratPrimeIdeal ℓ)] :
    Nat.card (ℤ ⧸ Q.under ℤ) = ℓ := by
  rw [← Q.over_def (ratPrimeIdeal ℓ), card_quotient_ratPrimeIdeal]

section Ramified

variable {K : Type*} [Field K] [NumberField K]

lemma finite_setOf_dvd {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ I}.Finite := by
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      {v | v.asIdeal ∣ I} := fun v _ w _ h => HeightOneSpectrum.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine (normalizedFactors I).toFinset.finite_toSet.subset ?_
  rintro J ⟨v, hv, rfl⟩
  simpa [Multiset.mem_toFinset] using
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨v.prime, hv⟩

variable (L : Type*) [Field L] [NumberField L]

theorem exists_smul_ne {g : L ≃ₐ[ℚ] L} (hg : g ≠ 1) :
    ∃ x : 𝓞 L, g • x ≠ x := by
  by_contra hcon'
  have hcon : ∀ x : 𝓞 L, g • x = x := fun x => not_not.mp fun h => hcon' ⟨x, h⟩
  refine hg (AlgEquiv.ext fun z => ?_)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (K := L) z
  have hx : g (algebraMap (𝓞 L) L x) = algebraMap (𝓞 L) L x :=
    congrArg (algebraMap (𝓞 L) L) (hcon x)
  have hy' : g (algebraMap (𝓞 L) L y) = algebraMap (𝓞 L) L y :=
    congrArg (algebraMap (𝓞 L) L) (hcon y)
  rw [← hxy, map_div₀, hx, hy', AlgEquiv.one_apply]

theorem finite_setOf_inertia_ne_bot_heightOneSpectrum :
    {v : HeightOneSpectrum (𝓞 L) | v.asIdeal.inertia (L ≃ₐ[ℚ] L) ≠ ⊥}.Finite := by
  classical
  choose x hx using fun g : {g : L ≃ₐ[ℚ] L // g ≠ 1} => exists_smul_ne L g.2
  refine Set.Finite.subset (Set.Finite.biUnion
    (Set.finite_univ (α := {g : L ≃ₐ[ℚ] L // g ≠ 1}))
    (fun g _ => finite_setOf_dvd (I := Ideal.span {g.1 • x g - x g}) ?_)) ?_
  · rw [Ne, Ideal.span_singleton_eq_bot, sub_eq_zero]
    exact hx g
  · intro v hv
    simp only [Set.mem_setOf_eq] at hv
    obtain ⟨g, hgmem, hgne⟩ := (v.asIdeal.inertia (L ≃ₐ[ℚ] L)).bot_or_exists_ne_one.resolve_left hv
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨⟨g, hgne⟩, Set.mem_univ _, ?_⟩
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hgmem (x ⟨g, hgne⟩)

noncomputable def badPrimes : Finset ℕ :=
  insert 0 (insert 1 (((finite_setOf_inertia_ne_bot_heightOneSpectrum L).image
    (fun v => Nat.card (ℤ ⧸ v.asIdeal.under ℤ))).toFinset))

theorem inertia_eq_bot_of_notMem_badPrimes {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓbad : ℓ ∉ badPrimes L) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] :
    Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  by_contra hcon
  apply hℓbad
  have hQbot : Q ≠ ⊥ := ne_bot_of_liesOver_ratPrimeIdeal hℓ
  refine Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr ?_)))
  rw [Set.Finite.mem_toFinset]
  exact ⟨⟨Q, inferInstance, hQbot⟩, hcon, card_quotient_under_int (ℓ := ℓ) Q⟩

end Ramified

section DegOneCount

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
theorem degOneCount_of_not_prime {ℓ : ℕ} (hℓ : ¬ ℓ.Prime) : degOneCount K ℓ = 0 := by
  rw [degOneCount, if_neg hℓ]

omit [NumberField K] in
theorem degOneCount_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) :
    degOneCount K ℓ
      = {𝔮 ∈ (ratPrimeIdeal ℓ).primesOver (𝓞 K) | Nat.card ((𝓞 K) ⧸ 𝔮) = ℓ}.ncard := by
  rw [degOneCount, if_pos hℓ]

end DegOneCount

section Frob

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

theorem isConj_arithFrobAt_of_liesOver {ℓ : ℕ} (hℓ : ℓ.Prime) (Q₁ Q₂ : Ideal (𝓞 L))
    [Q₁.IsPrime] [Q₂.IsPrime] [Q₁.LiesOver (ratPrimeIdeal ℓ)] [Q₂.LiesOver (ratPrimeIdeal ℓ)] :
    letI : Finite (𝓞 L ⧸ Q₁) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    letI : Finite (𝓞 L ⧸ Q₂) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    IsConj (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₁) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₂) := by
  letI : Finite (𝓞 L ⧸ Q₁) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  letI : Finite (𝓞 L ⧸ Q₂) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  exact isConj_arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₁ Q₂
    ((Q₁.over_def (ratPrimeIdeal ℓ)).symm.trans (Q₂.over_def (ratPrimeIdeal ℓ)))

variable (L)

theorem realizesCyclicAt_of_exists (σ : L ≃ₐ[ℚ] L) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q₀ : Ideal (𝓞 L)) [Q₀.IsPrime] [Q₀.LiesOver (ratPrimeIdeal ℓ)]
    (h : ∀ _ : Finite (𝓞 L ⧸ Q₀),
      ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀)) :
    RealizesCyclicAt L σ ℓ := by
  refine ⟨hℓ, fun Q hQp hQl hQf => ?_⟩
  haveI : Finite (𝓞 L ⧸ Q₀) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  obtain ⟨k, hk, hconj⟩ := h ‹_›
  exact ⟨k, hk, hconj.trans (isConj_arithFrobAt_of_liesOver hℓ Q₀ Q)⟩

end Frob

end FrobeniusDensity


