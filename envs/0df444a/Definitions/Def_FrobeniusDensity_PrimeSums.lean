-- Prove2me | Definitions.Def_FrobeniusDensity_PrimeSums
-- name    : FrobeniusDensity_PrimeSums
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/178a3260-2597-5502-9684-ad2d7a84fe0e
-- title:
--   ENNReal-valued ideal and prime norm sums for a number field
-- statement:
--   Throughout, $K$ is a number field with ring of integers $\mathcal{O}_K$, and all sums are unconditional $[0,\infty]$-valued `tsum`s, so no summability hypothesis is needed. The basic term is `normRpow K s I` $= (\mathrm{N}I)^{-s}$, the real power $-s$ of the absolute norm $\mathrm{Ideal.absNorm}\,I$ taken in $\mathbb{R}_{\ge0}^\infty$. From it: `idealSum K s` sums $(\mathrm{N}I)^{-s}$ over all nonzero ideals $I$; `primeSum K s` sums $(\mathrm{N}v)^{-s}$ over the height-one spectrum of $\mathcal{O}_K$; `primeSqSum K s` sums the squares $(\mathrm{N}v)^{-2s}$. The predicate `IsFactoredBy T I`, for a finite set $T$ of height-one primes, says that $I \neq 0$ and every height-one prime dividing $I$ belongs to $T$; `factoredSum K T s` sums $(\mathrm{N}I)^{-s}$ over the ideals so supported. `primeFactors K I` is the finite set of height-one primes dividing $I$ (empty by convention for $I = 0$), and `one_le_absNorm` records $\mathrm{N}I \ge 1$ for $I \neq 0$.
--
--   The theorem `exists_prime_liesOver` produces, for each height-one prime $v$, a rational prime $\ell$ such that $v$ lies over $\ell\mathbb{Z}$ (written `ratPrimeIdeal ℓ`); `ratBelow v` is a choice of such $\ell$, with `ratBelow_prime` and the `LiesOver` instance for it.
--
--   The remaining definitions split the prime sum. With `degOneCount K ℓ` the number of primes of $\mathcal{O}_K$ above $\ell$ with residue field of cardinality exactly $\ell$ (zero for non-prime $\ell$), `degOneSum K S₀ s` sums $\mathrm{degOneCount}(K,\ell)\,\ell^{-s}$ over $\ell \notin S_0$ and `cutSum K S₀ s` over $\ell \in S_0$; `tailSum K s` sums $(\mathrm{N}v)^{-s}$ over those $v$ whose absolute norm is not a rational prime. `tailConst` is $\sum_{\ell \text{ prime}} \ell^{-2}$. Finally `idealCount K n` is the number of ideals of absolute norm $n$, and `zetaTerm K s n` the real-valued Dirichlet coefficient $\mathrm{idealCount}(K,n)\,n^{-s}$ (set to $0$ at $n = 0$).
--
--   **Relation to Mathlib.** Mathlib supplies the absolute norm of an ideal, the height-one spectrum of a Dedekind domain and the Dedekind zeta function of a number field; the $[0,\infty]$-valued ideal, prime and partially supported sums collected here, together with the degree-one/cut/tail decomposition, are the project's own.
--
--   **Where it is used.** These sums are the analytic input for the asymptotic $\mathrm{degOneSum}(K,S_0,s) + \log(s-1) = O(1)$ as $s \downarrow 1$, i.e. the divergence of the sum over degree-one primes, which in turn yields the Frobenius-density statement used to produce Taylor–Wiles primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FrobeniusDensity_PrimeSums.lean

import Definitions.Def_FrobeniusDensity_BadPrimes
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.DedekindDomain.Factorization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Ideal NumberField Filter Topology Asymptotics IsDedekindDomain
  UniqueFactorizationMonoid
open scoped ENNReal NNReal

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

noncomputable def normRpow (s : ℝ) (I : Ideal (𝓞 K)) : ℝ≥0∞ :=
  (Ideal.absNorm I : ℝ≥0∞) ^ (-s)

noncomputable def idealSum (s : ℝ) : ℝ≥0∞ :=
  ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, normRpow K s I.1

noncomputable def primeSum (s : ℝ) : ℝ≥0∞ :=
  ∑' v : HeightOneSpectrum (𝓞 K), normRpow K s v.asIdeal

noncomputable def primeSqSum (s : ℝ) : ℝ≥0∞ :=
  ∑' v : HeightOneSpectrum (𝓞 K), normRpow K s v.asIdeal ^ 2

variable {K}

def IsFactoredBy (T : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K)) : Prop :=
  I ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I → v ∈ T

variable (K) in

noncomputable def factoredSum (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) : ℝ≥0∞ :=
  ∑' I : {I : Ideal (𝓞 K) // IsFactoredBy T I}, normRpow K s I.1

lemma one_le_absNorm {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : 1 ≤ Ideal.absNorm I :=
  Nat.one_le_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

variable (K) in

noncomputable def primeFactors (I : Ideal (𝓞 K)) : Finset (HeightOneSpectrum (𝓞 K)) :=
  if hI : I = ⊥ then ∅ else (finite_setOf_dvd hI).toFinset

variable (K)

theorem exists_prime_liesOver (v : HeightOneSpectrum (𝓞 K)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ v.asIdeal.LiesOver (ratPrimeIdeal ℓ) := by
  have hJp : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hmem : (Ideal.absNorm v.asIdeal : ℤ) ∈ v.asIdeal.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap, algebraMap_int_eq, map_natCast]
    exact Ideal.absNorm_mem v.asIdeal
  have hJne : v.asIdeal.under ℤ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot, Int.natCast_eq_zero] at hmem
    exact Nat.one_le_iff_ne_zero.mp (one_le_absNorm v.ne_bot) hmem
  refine ⟨(Submodule.IsPrincipal.generator (v.asIdeal.under ℤ)).natAbs,
    Int.prime_iff_natAbs_prime.mp
      (Submodule.IsPrincipal.prime_generator_of_isPrime _ hJne), ⟨?_⟩⟩
  rw [ratPrimeIdeal, Int.span_natAbs, Ideal.span_singleton_generator]

variable {K}

noncomputable def ratBelow (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (exists_prime_liesOver K v).choose

theorem ratBelow_prime (v : HeightOneSpectrum (𝓞 K)) : (ratBelow v).Prime :=
  (exists_prime_liesOver K v).choose_spec.1

instance liesOver_ratBelow (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.LiesOver (ratPrimeIdeal (ratBelow v)) :=
  (exists_prime_liesOver K v).choose_spec.2

variable (K)

noncomputable def degOneSum (S₀ : Finset ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ≥0∞)) * (ℓ : ℝ≥0∞) ^ (-s)

noncomputable def cutSum (S₀ : Finset ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∑' ℓ : ℕ, (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) * (ℓ : ℝ≥0∞) ^ (-s)

noncomputable def tailSum (s : ℝ) : ℝ≥0∞ :=
  ∑' v : HeightOneSpectrum (𝓞 K),
    if (Ideal.absNorm v.asIdeal).Prime then 0 else normRpow K s v.asIdeal

noncomputable def tailConst : ℝ≥0∞ :=
  ∑' ℓ : ℕ, if ℓ.Prime then ((ℓ : ℝ≥0∞) ^ 2)⁻¹ else 0

noncomputable def idealCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

noncomputable def zetaTerm (s : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else idealCount K n * (n : ℝ) ^ (-s)

end FrobeniusDensity


