-- Prove2me | Definitions.Def_GaloisRep_FrobeniusPowerDense
-- name    : GaloisRep_FrobeniusPowerDense
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/760d2cff-8cea-54be-b9e2-54b55f8b9fea
-- title:
--   Frobenius-power density outside a finite set of primes
-- statement:
--   This module defines a single predicate, [`FrobeniusPowerDense`](../def/GaloisRep_FrobeniusPowerDense.html#L7), on a pair consisting of a finite set $S$ of natural numbers and a subgroup $H$ of the absolute Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, taken in the form of the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. It asserts: for every automorphism $\sigma$ there exist a natural number $\ell$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, two automorphisms $\tau$ and $g$, and a natural number $n$, such that $\ell$ is prime, $\ell \notin S$, $A$ satisfies `LiesOverPrime ℓ`, $\tau$ satisfies `IsFrobeniusAt τ ℓ` for $A$, and $g\,\tau^{n}\,g^{-1}\,\sigma^{-1} \in H$. Unfolding the two imported notions: `A.LiesOverPrime ℓ` says that the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$, i.e. lies in the maximal ideal of the valuation ring, so that $A$ is a valuation subring lying over $\ell$; and `A.IsFrobeniusAt τ ℓ` says that $\tau$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and that the resulting action of $\tau$ on the residue field of $A$ is the $\ell$-power map $x \mapsto x^{\ell}$. Thus the predicate expresses that, modulo $H$, every element of the absolute Galois group is represented by a conjugate of a power of some Frobenius element at a place above a prime outside $S$. Note that it is a statement about the cosets $g\tau^{n}g^{-1}H$ only, with no finiteness or normality requirement on $H$, and no condition tying $\ell$ to $S$ beyond $\ell \notin S$.
--
--   **Relation to Mathlib.** Mathlib supplies `ValuationSubring` together with its decomposition and inertia subgroups and the residue field of a valuation ring; the predicates [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16), [`ValuationSubring.IsFrobeniusAt`](../def/EllipticCurve_FrobeniusTrace.html#L51) and the density condition [`FrobeniusPowerDense`](../def/GaloisRep_FrobeniusPowerDense.html#L7) itself are the project's own.
--
--   **Where it is used.** The predicate packages the density input needed when two mod-$p$ Galois representations are identified from agreement of their Frobenius data outside a finite set of primes: once Frobenius powers cover all classes modulo the relevant subgroup, agreement at Frobenius elements propagates to the whole Galois group. It is verified, via Chebotarev-type density, for subgroups containing $\mathrm{Gal}(\overline{\mathbb{Q}}/F)$ for a finite Galois extension $F/\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_FrobeniusPowerDense.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

def FrobeniusPowerDense (S : Finset ℕ)
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) : Prop :=
  ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H


