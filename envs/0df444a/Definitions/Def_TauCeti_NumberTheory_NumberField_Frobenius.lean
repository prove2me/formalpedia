-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Frobenius
-- name    : TauCeti_NumberTheory_NumberField_Frobenius
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:44:04.14817+00:00
-- url     : https://prove2.me/theorems/ecbf669a-1ec3-4b57-a9d4-11f8bfd82a41
-- title:
--   Frobenius elements of Galois number fields and their action on square roots
-- statement:
--   For a finite Galois extension $L/K$ of number fields, every nonzero prime of $\mathcal O_L$ admits an arithmetic Frobenius. At a prime unramified over $\mathcal O_K$, arithmetic Frobenius is unique. These existence and uniqueness facts support the Artin-symbol construction.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Frobenius.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Frobenius.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_RingTheory_Frobenius
import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Frobenius elements of Galois number fields and their action on square roots

For a finite Galois extension `L/K` of number fields and a nonzero prime `Q` of `𝓞 L`, an
arithmetic Frobenius at `Q` is a `σ ∈ Gal(L/K)` with
`σ x ≡ x ^ #(𝓞 K ⧸ Q ∩ 𝓞 K) (mod Q)` for all `x : 𝓞 L`. The exponent is the cardinality of the
*base* residue ring, not the absolute norm of `Q`. This file provides the following number-field
services on top of Mathlib's `RingTheory/Frobenius.lean`:

* **relative existence** — a Frobenius exists at every nonzero prime of `𝓞 L`
  (`IsArithFrobAt.exists_of_isInvariant` with the number-field instances discharged: the
  residue field of a nonzero prime is finite, and the Galois action on `𝓞 L` has invariants
  `𝓞 K`);
* **rational-prime existence** — for a Galois number field `K/ℚ`, a Frobenius relative to the
  base ring `ℤ` exists at every prime over `(p)`, with exponent `p`. This is distinct from the
  relative theorem at `K = ℚ`, whose base-ring carrier is `𝓞 ℚ`, not `ℤ`;
* **uniqueness** — for a finite Galois extension `L/K` of number fields, two Frobenius elements
  of `Gal(L/K)` at an unramified prime `Q` of `𝓞 L` are equal, by combining Mathlib's
  integral-ring uniqueness theorem with the faithfulness of the Galois action; and
* **the square-root action** — for a number field `K`, `p` odd, and `x ∈ K` with
  `x² = d ∈ ℤ`, `p ∤ d`, a
  Frobenius at any ideal `Q` over `p` satisfies `σ x = legendreSym p d • x`, transporting the
  `𝓞 K`-level computation `AlgHom.IsArithFrobAt.apply_sqrt` along the Galois action
  on the ring of integers (via `NumberField.algebraMap_smul_eq_apply`), with the `σ x = x`
  characterization read off from it.

`TauCeti.NumberTheory.Multiquadratic.Frobenius` combines existence with the square-root action
to describe the Frobenius of a multiquadratic field on all its generators at once (Layer 1 of the
multiquadratic roadmap).

## Main results

* `NumberField.exists_isArithFrobAt`: a relative Frobenius exists at every nonzero prime of
  `𝓞 L` in a finite Galois extension `L/K` of number fields.
* `NumberField.exists_isArithFrobAt_int_of_liesOver`: a `ℤ`-carrier Frobenius exists at every
  prime over a rational prime.
* `AlgEquiv.isArithFrobAt_autCongr`: an isomorphism of extensions transports the Frobenius
  condition.
* `NumberField.isArithFrobAt_eq_of_isUnramifiedAt`: for a finite Galois extension `L/K` of
  number fields, two Frobenius elements of `Gal(L/K)` at an unramified prime `Q` of `𝓞 L` are
  equal.
* `NumberField.subsingleton_isArithFrobAt`: for such an extension and prime, the type of
  Frobenius elements is a subsingleton.
* `NumberField.isArithFrobAt_apply_sqrt`: a Frobenius at `Q ∣ p` sends a square root
  of `d` to `legendreSym p d` times it.
* `NumberField.isArithFrobAt_apply_sqrt_eq_self_iff`: it fixes `√d` iff `d` is a
  quadratic residue mod `p`.
* `TauCeti.isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight` and
  `TauCeti.isArithFrobAt_apply_sqrt_two`: for `d ≡ 1 (mod 4)`, Frobenius at `2` fixes
  `√d` exactly when `d ≡ 1 (mod 8)` and negates it otherwise.
-/

 section

open Ideal

open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

 theorem exists_isArithFrobAt_aux {L : Type*} [Field L] [NumberField L]
    (R : Type*) [CommRing R] [Algebra R (𝓞 L)] (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G (𝓞 L)] [SMulCommClass G R (𝓞 L)]
    [Algebra.IsInvariant R (𝓞 L) G] (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    ∃ σ : G, IsArithFrobAt R σ Q := by
  let _ : Finite (𝓞 L ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient hQ
  exact IsArithFrobAt.exists_of_isInvariant R G Q

variable (K) in
/-- **Relative Frobenius elements exist.** For a finite Galois extension `L/K` of number fields
and a nonzero prime `Q` of `𝓞 L`, some `σ ∈ Gal(L/K)` is an arithmetic Frobenius at `Q`. -/
theorem exists_isArithFrobAt {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    ∃ σ : L ≃ₐ[K] L, IsArithFrobAt (𝓞 K) σ Q :=
  exists_isArithFrobAt_aux (𝓞 K) (L ≃ₐ[K] L) Q hQ



end NumberField

namespace AlgEquiv

variable {K L L' : Type*} [Field K] [Field L] [Algebra K L] [Field L'] [Algebra K L']



end AlgEquiv

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

/-! ### Uniqueness at unramified primes

Mathlib proves uniqueness for algebra homomorphisms of the integral rings.  The Galois-group
form below first applies that theorem to the action on `𝓞 L`, then uses the faithful Galois
action to recover equality of the automorphisms themselves.  In the number-field setting the
complement of every prime consists of non-zero-divisors, which discharges the remaining
hypothesis of the generic theorem.
-/

/-- **Frobenius elements are unique at an unramified prime.** If `Q` is a prime of the
ring of integers of a finite Galois extension `L/K`, then two arithmetic Frobenius elements at
`Q` coincide whenever `L/K` is unramified at `Q`.

This is a conditional uniqueness statement and makes no existence assertion, so `Q` need not be
nonzero.

This is the Galois-group form of `IsArithFrobAt.eq_of_isUnramifiedAt`. -/
theorem isArithFrobAt_eq_of_isUnramifiedAt {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    {σ τ : L ≃ₐ[K] L} {Q : Ideal (𝓞 L)} [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (hσ : IsArithFrobAt (𝓞 K) σ Q)
    (hτ : IsArithFrobAt (𝓞 K) τ Q) : σ = τ := by
  let _ : FaithfulSMul (L ≃ₐ[K] L) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
  exact _root_.IsArithFrobAt.eq_of_isUnramifiedAt
    (Ideal.primeCompl_le_nonZeroDivisors Q) hσ hτ

/-- The Frobenius elements at an unramified prime form a subsingleton. -/
instance subsingleton_isArithFrobAt {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    {Q : Ideal (𝓞 L)} [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    Subsingleton {σ : L ≃ₐ[K] L // IsArithFrobAt (𝓞 K) σ Q} where
  allEq σ τ := Subtype.ext (isArithFrobAt_eq_of_isUnramifiedAt σ.property τ.property)





end NumberField

/-! ### Frobenius on square roots at 2

For `d ≡ 1 (mod 4)`, an arithmetic Frobenius at a prime above `2` fixes a square root of
`d` exactly when `d ≡ 1 (mod 8)`, and negates it when `d ≡ 5 (mod 8)`. The ambient field
need not be quadratic, so the result applies to each generator of a multiquadratic field.

The two roots have identical reductions in characteristic two. Instead one uses the algebraic
integer `(1 + √d) / 2`, whose conjugate is `1 - (1 + √d) / 2`; their difference has odd square
and hence is nonzero modulo the prime. This is the dyadic counterpart of the Legendre-symbol
formula for Frobenius at odd primes, and supplies its missing local input at an odd discriminant.

The classical quadratic splitting criterion is described in D. A. Cox,
*Primes of the Form x² + ny²*, §5.A.
-/

open NumberField

namespace TauCeti





end TauCeti

end
end


