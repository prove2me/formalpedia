-- Prove2me | Definitions.Def_NormIndex_AdmissibleExpOfDegree
-- name    : NormIndex_AdmissibleExpOfDegree
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/9fb302f4-e358-535e-ac78-16baeb302877
-- title:
--   Admissible exponents and admissible moduli for arbitrary degree
-- statement:
--   Throughout, $K$ is a number field and $L$ a field extension of $K$. For a natural number $n$ and a finite place $v$ of $K$ (an element of the height-one spectrum of $\mathcal O_K$), `admissibleExpOfDegree K n v` is the natural number
--   $$1 + \sum_{p \mid n} \bigl(\operatorname{ord}_p(n) + 1\bigr)\, e(v \mid p),$$
--   the sum being over the prime factors of $n$, with $\operatorname{ord}_p(n)$ the exponent of $p$ in $n$ (`Nat.factorization`) and $e(v\mid p)$ the ramification index `Ideal.ramificationIdx'` of the ideal $p\mathbb Z$ at $v$. For $n = 0$ and $n = 1$ the sum is empty and the value is $1$ at every place.
--
--   The predicate `IsAdmissibleModulusOfDegree K L n 𝔣`, for an ideal $\mathfrak f$ of $\mathcal O_K$, asserts two things: $\mathfrak f \neq 0$, and for every finite place $v$ of $K$ such that the inertia subgroup of $L \simeq_{\mathrm{alg}[K]} L$ at the chosen prime `primeAbove K L v` of $L$ above $v$ is nontrivial, the power $v^{\,\mathrm{admissibleExpOfDegree}\ K\ n\ v}$ divides $\mathfrak f$. So admissibility constrains only the places that ramify at the distinguished prime above them, and asks that the modulus be divisible there to the stated depth.
--
--   The accompanying lemmas are: admissibility of degree $n$ passes to any nonzero multiple of an admissible modulus (`IsAdmissibleModulusOfDegree.of_dvd`); a restatement of the exponent at $n = [L:K]$ (`Module.finrank K L`); for a prime $\ell$ the exponent equals $2\,e(v\mid \ell) + 1$, i.e. `PrimeNormIndex.admissibleExpAt K ℓ v`; and for $n = 24$ it equals $4\,e(v\mid 2) + 2\,e(v\mid 3) + 1$, i.e. `admissibleExp K v`. Correspondingly the degree-$\ell$ and degree-$24$ predicates agree with `PrimeNormIndex.IsAdmissibleModulusAt K L ℓ` and with `IsAdmissibleModulus K L`.
--
--   **Relation to Mathlib.** Mathlib has no notion of admissible modulus of this kind; the exponent and the predicate are the project's own, and they interpolate between the project's prime-degree notion `PrimeNormIndex.IsAdmissibleModulusAt` and its degree-$24$ notion `IsAdmissibleModulus`.
--
--   **Where it is used.** These moduli provide a sufficiently deep level at the ramified places for the class-field-theoretic development in the `LanglandsTunnell.P2.Artin` namespace (Artin symbols on ray groups, relative norms of ideles, and the two index inequalities), which supplies the Langlands–Tunnell input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NormIndex_AdmissibleExpOfDegree.lean

import Definitions.Def_PrimeNormIndex_AdmissibleExpAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open LanglandsTunnell.P2.Artin

namespace NumberField.NormIndex

variable (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]

def admissibleExpOfDegree (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  1 + ∑ p ∈ n.primeFactors,
    (n.factorization p + 1) * Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal

def IsAdmissibleModulusOfDegree (n : ℕ) (𝔣 : Ideal (𝓞 K)) : Prop :=
  𝔣 ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 K),
    (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ → v.asIdeal ^ admissibleExpOfDegree K n v ∣ 𝔣

theorem IsAdmissibleModulusOfDegree.of_dvd {n : ℕ} {𝔣 𝔣' : Ideal (𝓞 K)}
    (h : IsAdmissibleModulusOfDegree K L n 𝔣) (hd : 𝔣 ∣ 𝔣') (h0 : 𝔣' ≠ ⊥) :
    IsAdmissibleModulusOfDegree K L n 𝔣' :=
  ⟨h0, fun v hv => (h.2 v hv).trans hd⟩

omit [NumberField K] in

theorem admissibleExpOfDegree_finrank (v : HeightOneSpectrum (𝓞 K)) :
    admissibleExpOfDegree K (Module.finrank K L) v =
      (1 + ∑ p ∈ (Module.finrank K L).primeFactors,
        ((Module.finrank K L).factorization p + 1) *
          Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal : ℕ) :=
  rfl

omit [NumberField K] in

theorem admissibleExpOfDegree_eq_admissibleExpAt {ℓ : ℕ} (hℓ : ℓ.Prime)
    (v : HeightOneSpectrum (𝓞 K)) :
    admissibleExpOfDegree K ℓ v = PrimeNormIndex.admissibleExpAt K ℓ v := by
  unfold admissibleExpOfDegree PrimeNormIndex.admissibleExpAt
  rw [hℓ.primeFactors, Finset.sum_singleton, hℓ.factorization_self]
  omega

omit [NumberField K] in

theorem admissibleExpOfDegree_twentyFour (v : HeightOneSpectrum (𝓞 K)) :
    admissibleExpOfDegree K 24 v = admissibleExp K v := by
  unfold admissibleExpOfDegree admissibleExp
  have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  have hpf : (24 : ℕ).primeFactors = {2, 3} := by
    rw [h24, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.prime_three.primeFactors]
    rfl
  have hf2 : (24 : ℕ).factorization 2 = 3 := by
    rw [h24, Nat.factorization_mul (by norm_num) (by norm_num), Nat.prime_two.factorization_pow,
      Nat.prime_three.factorization]
    simp
  have hf3 : (24 : ℕ).factorization 3 = 1 := by
    rw [h24, Nat.factorization_mul (by norm_num) (by norm_num), Nat.prime_two.factorization_pow,
      Nat.prime_three.factorization]
    simp
  rw [hpf, Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3), hf2, hf3]
  push_cast
  omega

theorem isAdmissibleModulusOfDegree_iff_at {ℓ : ℕ} (hℓ : ℓ.Prime) (𝔣 : Ideal (𝓞 K)) :
    IsAdmissibleModulusOfDegree K L ℓ 𝔣 ↔ PrimeNormIndex.IsAdmissibleModulusAt K L ℓ 𝔣 := by
  unfold IsAdmissibleModulusOfDegree PrimeNormIndex.IsAdmissibleModulusAt
  simp only [admissibleExpOfDegree_eq_admissibleExpAt K hℓ]

theorem isAdmissibleModulusOfDegree_twentyFour_iff (𝔣 : Ideal (𝓞 K)) :
    IsAdmissibleModulusOfDegree K L 24 𝔣 ↔ IsAdmissibleModulus K L 𝔣 := by
  unfold IsAdmissibleModulusOfDegree IsAdmissibleModulus
  simp only [admissibleExpOfDegree_twentyFour K]

end NumberField.NormIndex

end


