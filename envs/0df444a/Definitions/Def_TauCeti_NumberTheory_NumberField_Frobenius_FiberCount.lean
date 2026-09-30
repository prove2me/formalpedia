-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Frobenius_FiberCount
-- name    : TauCeti_NumberTheory_NumberField_Frobenius_FiberCount
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:50:19.009084+00:00
-- url     : https://prove2.me/theorems/8a4cdd61-4077-4eb5-a5da-b64361ee0860
-- title:
--   How many primes carry a given Frobenius element
-- statement:
--   For a number-field extension and a chosen Frobenius automorphism, the fiber above a base prime can be represented either by prime ideals or by points of the height-one spectrum. The canonical equivalence preserves the underlying ideal. It lets finite fiber counts use either representation.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Frobenius/FiberCount.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Frobenius/FiberCount.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Unramified.Locus

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# How many primes carry a given Frobenius element

Let `L / K` be a finite Galois extension of number fields, `𝔭` an ideal of `𝓞 K` and `σ` an
element of `Gal(L/K)`. The primes of `𝓞 L` above `𝔭` at which `σ` is an arithmetic Frobenius form
the *fiber* of `σ`, and `Ideal.frobenius_fiber_card_eq_of_isConj` shows that conjugate elements
have fibers of the same size. This file computes that size, at a prime where `σ` is a Frobenius
and `L / K` is unramified:

```text
#(fiber of σ) * orderOf σ = #Centralizer_{Gal(L/K)}(σ)
```

The reason is that the fiber is a single orbit. `Gal(L/K)` acts transitively on the primes above
`𝔭`, and the Frobenius at `τ • Q` is `τ σ τ⁻¹`, so the elements carrying `Q` to another member of
the fiber are exactly those commuting with `σ`. The stabilizer of `Q` inside that centralizer is
the decomposition group `⟨σ⟩`, whose order is `orderOf σ`, and the orbit-stabilizer theorem gives
the count.

The identity is stated as a product rather than as `#Centralizer(σ) / orderOf σ` so that it says
something without a separate divisibility: `orderOf σ` divides the centralizer's order because
`⟨σ⟩` is a subgroup of it, and `ConjClasses.card_carrier_mul_orderOf_dvd` records the companion
divisibility for a whole conjugacy class.

## Main results

* `Ideal.frobenius_fiber_eq_orbit_centralizer`: the fiber of `σ` above `𝔭` is the orbit of any of
  its members under the centralizer of `σ`.
* `Ideal.frobenius_fiber_card_mul_orderOf_eq_card_centralizer`: its size, times `orderOf σ`, is
  the order of that centralizer.
* `HeightOneSpectrum.frobeniusFiberEquiv`: the height-one-prime and ideal representations of the
  fiber are equivalent.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (p. 143).
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

 section

open scoped NumberField Pointwise
open IsDedekindDomain (HeightOneSpectrum)

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

-- Source. The count is specified by the Chebotarev roadmap:
-- `TauCetiRoadmap/Chebotarev/README.md` §8.2, which displays the fibre size as
-- `#G / (#C * f) = #Centralizer_G(σ) / f` with `f = orderOf σ`. The theorems below count the
-- primes of `𝓞 L`; the roadmap's own statement counts primes of the fixed field `L ^ ⟨σ⟩`, and
-- reaches this one through the residue degree of a fixed-field prime.





end Ideal

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- The equivalence between the height-one-prime and ideal representations of a Frobenius fiber
above `p`, induced by `HeightOneSpectrum.asIdeal`. -/
noncomputable def frobeniusFiberEquiv
    (p : HeightOneSpectrum (𝓞 K)) (sigma : L ≃ₐ[K] L) :
    {Q : HeightOneSpectrum (𝓞 L) //
        Q.under (𝓞 K) = p ∧ IsArithFrobAt (𝓞 K) sigma Q.asIdeal} ≃
      {Q : Ideal (𝓞 L) // ∃ (_ : Q.IsPrime) (_ : Q.LiesOver p.asIdeal) (_ : Q ≠ ⊥),
        IsArithFrobAt (𝓞 K) sigma Q} := by
  let hdiv : ∀ Q : HeightOneSpectrum (𝓞 L),
      Q.under (𝓞 K) = p ↔
        Q.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p.asIdeal := fun Q ↦ by
    rw [← Ideal.liesOver_iff_dvd_map Q.isPrime.ne_top]
    exact ⟨fun h ↦ ⟨(congrArg HeightOneSpectrum.asIdeal h).symm⟩,
      fun h ↦ HeightOneSpectrum.ext h.over.symm⟩
  let domainEquiv :
      {Q : HeightOneSpectrum (𝓞 L) //
          Q.under (𝓞 K) = p ∧ IsArithFrobAt (𝓞 K) sigma Q.asIdeal} ≃
        {Q : {Q : HeightOneSpectrum (𝓞 L) //
            Q.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p.asIdeal} //
          IsArithFrobAt (𝓞 K) sigma Q.1.asIdeal} :=
    (Equiv.subtypeEquivRight fun Q ↦ and_congr (hdiv Q) Iff.rfl).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  let coreEquiv :
      {Q : {Q : HeightOneSpectrum (𝓞 L) //
          Q.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p.asIdeal} //
        IsArithFrobAt (𝓞 K) sigma Q.1.asIdeal} ≃
        {Q : p.asIdeal.primesOver (𝓞 L) // IsArithFrobAt (𝓞 K) sigma Q.1} :=
    (HeightOneSpectrum.equivPrimesOver (𝓞 L) p.ne_bot).subtypeEquiv fun _ ↦ Iff.rfl
  let codomainEquiv :
      {Q : p.asIdeal.primesOver (𝓞 L) // IsArithFrobAt (𝓞 K) sigma Q.1} ≃
        {Q : Ideal (𝓞 L) // ∃ (_ : Q.IsPrime) (_ : Q.LiesOver p.asIdeal) (_ : Q ≠ ⊥),
          IsArithFrobAt (𝓞 K) sigma Q} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun Q : Ideal (𝓞 L) ↦ Q ∈ p.asIdeal.primesOver (𝓞 L))
      (fun Q ↦ IsArithFrobAt (𝓞 K) sigma Q)).trans
      (Equiv.subtypeEquivRight fun Q ↦ by
        constructor
        · rintro ⟨hQ, hfrob⟩
          exact ⟨hQ.1, hQ.2, Ideal.ne_bot_of_mem_primesOver p.ne_bot hQ, hfrob⟩
        · rintro ⟨hprime, hover, -, hfrob⟩
          exact ⟨⟨hprime, hover⟩, hfrob⟩)
  exact domainEquiv.trans (coreEquiv.trans codomainEquiv)







end IsDedekindDomain.HeightOneSpectrum

end
end


