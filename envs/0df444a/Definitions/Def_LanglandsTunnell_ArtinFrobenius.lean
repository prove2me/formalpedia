-- Prove2me | Definitions.Def_LanglandsTunnell_ArtinFrobenius
-- name    : LanglandsTunnell_ArtinFrobenius
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/57bf47a4-9f5d-5d1c-b3b8-bbb6eb9e64a9
-- title:
--   Chosen primes above, arithmetic Frobenius, and Artin symbol
-- statement:
--   Throughout, $K$ and $M$ are number fields with $M$ a $K$-algebra. The first group of declarations records that $\mathcal{O}_K \to \mathcal{O}_M$ is injective, and that for every $v$ in the height-one spectrum of $\mathcal{O}_K$ there exists a maximal ideal $Q$ of $\mathcal{O}_M$ with $Q \cap \mathcal{O}_K = v$ (lying over, via integrality); `primeAbove K M v` names one such $Q$, chosen once and for all. Accompanying lemmas state that this chosen ideal is maximal, lies over $v$, is nonzero (any ideal contracting to $v$ is nonzero, since $v \neq 0$), and has finite residue ring, and that $\operatorname{Gal}(M/K)$ acts as a Galois group on the extension $\mathcal{O}_K \to \mathcal{O}_M$ when $M/K$ is Galois.
--
--   For $M/K$ Galois, `artinFrob K M v` is Mathlib's arithmetic Frobenius `arithFrobAt` at the chosen prime `primeAbove K M v`, i.e. the element $\sigma \in \operatorname{Gal}(M/K)$ with $\sigma(x) \equiv x^{q}$ modulo that prime, $q$ the residue cardinality of $v$; `isArithFrobAt_artinFrob` records the defining predicate `IsArithFrobAt`.
--
--   When in addition $\operatorname{Gal}(M/K)$ is commutative, `artinSymbol K M 𝔣` is the monoid homomorphism, from the group of units of the fractional ideals of $K$ whose valuation $\operatorname{count}_w$ vanishes at every $w \mid \mathfrak{f}$, to $\operatorname{Gal}(M/K)$, given by $I \mapsto \prod_w (\mathrm{artinFrob}\ K\ M\ w)^{\operatorname{count}_w(I)}$ (a finitely supported product). Its value on the prime unit attached to $v$, for $v \nmid \mathfrak{f}$, is `artinFrob K M v`. Independence of the symbol from the choices of primes above, and reciprocity, are not asserted here.
--
--   **Relation to Mathlib.** The arithmetic Frobenius (`arithFrobAt`, `IsArithFrobAt`) and the `IsGaloisGroup` interface come from Mathlib; added here are a global choice of prime of $\mathcal{O}_M$ above each finite place of $K$ and the Artin symbol on ideals coprime to a modulus, built from the project's narrow ray class group vocabulary (`coprimeToModulus`, `raySymbolHom`, `primeUnit`).
--
--   **Where it is used.** This vocabulary belongs to the Langlands–Tunnell input of the argument, where characters of ray class groups of number fields are converted into characters of Galois groups, and Frobenius elements at places outside the modulus are needed to compare the resulting Galois representations with automorphic data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_ArtinFrobenius.lean

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Definitions.Def_NarrowRayClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.P2.Artin

open NumberField IsDedekindDomain
open Deep.NTSupply
open scoped nonZeroDivisors

section Frob

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

instance isGaloisGroup_ringOfIntegers [IsGalois K M] : IsGaloisGroup (M ≃ₐ[K] M) (𝓞 K) (𝓞 M) :=
  IsGaloisGroup.of_isFractionRing (M ≃ₐ[K] M) (𝓞 K) (𝓞 M) K M

omit [NumberField K] [NumberField M] in
theorem algebraMap_ringOfIntegers_injective : Function.Injective (algebraMap (𝓞 K) (𝓞 M)) := by
  intro x y h
  have h' : algebraMap (𝓞 K) M x = algebraMap (𝓞 K) M y := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M, IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M, h]
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K M, IsScalarTower.algebraMap_apply (𝓞 K) K M] at h'
  exact RingOfIntegers.coe_injective ((algebraMap K M).injective h')

omit [NumberField M] in
theorem exists_prime_over (v : HeightOneSpectrum (𝓞 K)) : ∃ Q : Ideal (𝓞 M), Q.IsMaximal ∧ Q.under (𝓞 K) = v.asIdeal := by
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap_ringOfIntegers_injective K M)]; exact bot_le)
  exact ⟨Q, hQ, hQv⟩

def primeAbove (v : HeightOneSpectrum (𝓞 K)) : Ideal (𝓞 M) := (exists_prime_over K M v).choose

variable (v : HeightOneSpectrum (𝓞 K))

instance primeAbove_isMaximal : (primeAbove K M v).IsMaximal := (exists_prime_over K M v).choose_spec.1

omit [NumberField M] in
theorem under_primeAbove : (primeAbove K M v).under (𝓞 K) = v.asIdeal := (exists_prime_over K M v).choose_spec.2

instance primeAbove_liesOver : (primeAbove K M v).LiesOver v.asIdeal := ⟨(under_primeAbove K M v).symm⟩

omit [NumberField K] [NumberField M] in
theorem ne_bot_of_under_eq {Q : Ideal (𝓞 M)} (hQ : Q.under (𝓞 K) = v.asIdeal) : Q ≠ ⊥ := fun h => by
  rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _ (algebraMap_ringOfIntegers_injective K M)] at hQ
  exact v.ne_bot hQ.symm

omit [NumberField M] in
theorem primeAbove_ne_bot : primeAbove K M v ≠ ⊥ := ne_bot_of_under_eq K M v (under_primeAbove K M v)

instance primeAbove_finite : Finite (𝓞 M ⧸ primeAbove K M v) := Ideal.finiteQuotientOfFreeOfNeBot _ (primeAbove_ne_bot K M v)

omit [NumberField K] in
theorem finite_quotient_of_under_eq {Q : Ideal (𝓞 M)} (hQ : Q.under (𝓞 K) = v.asIdeal) : Finite (𝓞 M ⧸ Q) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (ne_bot_of_under_eq K M v hQ)

end Frob

section Artin

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  (v : HeightOneSpectrum (𝓞 K))

def artinFrob : M ≃ₐ[K] M := arithFrobAt (𝓞 K) (M ≃ₐ[K] M) (primeAbove K M v)

theorem isArithFrobAt_artinFrob : IsArithFrobAt (𝓞 K) (artinFrob K M v) (primeAbove K M v) :=
  IsArithFrobAt.arithFrobAt (𝓞 K) (M ≃ₐ[K] M) (primeAbove K M v)

end Artin

section Symbol

open Deep.NTSupply
open scoped nonZeroDivisors

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

open scoped IsMulCommutative

def artinSymbol (𝔣 : Ideal (𝓞 K)) : ↥(coprimeToModulus K 𝔣) →* (M ≃ₐ[K] M) := raySymbolHom K 𝔣 (artinFrob K M)

theorem artinSymbol_prime {𝔣 : Ideal (𝓞 K)} {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) :
    artinSymbol K M 𝔣 ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩ = artinFrob K M v :=
  raySymbolHom_prime K 𝔣 (artinFrob K M) hv

end Symbol

#print axioms LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers
#print axioms LanglandsTunnell.P2.Artin.algebraMap_ringOfIntegers_injective
#print axioms LanglandsTunnell.P2.Artin.exists_prime_over
#print axioms LanglandsTunnell.P2.Artin.primeAbove
#print axioms LanglandsTunnell.P2.Artin.primeAbove_isMaximal
#print axioms LanglandsTunnell.P2.Artin.under_primeAbove
#print axioms LanglandsTunnell.P2.Artin.primeAbove_liesOver
#print axioms LanglandsTunnell.P2.Artin.ne_bot_of_under_eq
#print axioms LanglandsTunnell.P2.Artin.primeAbove_ne_bot
#print axioms LanglandsTunnell.P2.Artin.primeAbove_finite
#print axioms LanglandsTunnell.P2.Artin.finite_quotient_of_under_eq
#print axioms LanglandsTunnell.P2.Artin.artinFrob
#print axioms LanglandsTunnell.P2.Artin.isArithFrobAt_artinFrob
#print axioms LanglandsTunnell.P2.Artin.artinSymbol
#print axioms LanglandsTunnell.P2.Artin.artinSymbol_prime

end LanglandsTunnell.P2.Artin

end


