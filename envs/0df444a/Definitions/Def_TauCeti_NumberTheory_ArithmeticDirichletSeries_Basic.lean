-- Prove2me | Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
-- name    : TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:37:45.72055+00:00
-- url     : https://prove2.me/theorems/b828c3e9-ceda-4335-a6e1-6c1a580e7e40
-- title:
--   Arithmetic functions on nonzero ideals
-- statement:
--   For a number field $K$, an ideal arithmetic function is a complex-valued function on the nonzero integral ideals of $\mathcal O_K$. Such a function is multiplicative if
--
--   $$
--   f(\mathcal O_K)=1,\qquad f(IJ)=f(I)f(J)\quad\text{when }I+J=\mathcal O_K.
--   $$
--
--   This is the coefficient space for ideal Dirichlet series.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Arithmetic functions on nonzero ideals

For the intended number-field applications, an ideal-indexed Dirichlet series should not assign an
arithmetic coefficient to the zero ideal. Excluding it ensures that ideal convolution never
considers factorizations through the zero ideal. This file introduces the carrier used throughout
the arithmetic-Dirichlet-series roadmap, parameterized over an arbitrary field:

* `TauCeti.IdealArithmeticFunction K` is a complex-valued function on the nonzero ideals of
  `𝓞 K`;
* `TauCeti.IdealArithmeticFunction.zeroExtend` is its canonical extension to all integral ideals,
  with value zero at the zero ideal;
* `TauCeti.IdealArithmeticFunction.restrict` restricts a function on all ideals to the nonzero
  ideals;
* `TauCeti.IdealArithmeticFunction.map` and `TauCeti.IdealArithmeticFunction.mapEquiv`:
  functoriality under an isomorphism `K ≃+* L` of the ambient fields.

It also carries the multiplicativity predicate
`TauCeti.IdealArithmeticFunction.IsMultiplicative` — value `1` at the unit ideal, multiplicative on
relatively prime nonzero ideals — together with its two factorization consequences:
`IsMultiplicative.map_prod` for a pairwise relatively prime finite product, and, over a number
field, `IsMultiplicative.map_prod_pow` for a prime-power factorization of a nonzero ideal, the
factorizations themselves being supplied by `Ideal.exists_eq_prod_pow`.

The two operations are inverse precisely on functions vanishing at the zero ideal. The resulting
existence-and-uniqueness API is recorded without exposing the implementation of `zeroExtend`:
`TauCeti.IdealArithmeticFunction.existsUnique_zeroExtend_eq` characterizes its image, while
`TauCeti.IdealArithmeticFunction.zeroExtend_injective` says that no information is lost.

The extension respects the pointwise additive, scalar, and multiplicative operations. It does not
preserve the pointwise unit: the constant-one function on all ideals takes value one at the zero
ideal, and therefore cannot be a zero extension. The theorem
`TauCeti.IdealArithmeticFunction.not_exists_zeroExtend_eq_one` is the zero-ideal rejection test
required by Layer 0 of the roadmap.

## Roadmap role

This is Layer **0.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, and is the common
carrier on which its norm regrouping, ideal convolution, Euler products, and summatory functions
are built. Later Layer 0 files add completely multiplicative and unitary subtypes; those are
special coefficient systems on this general carrier, not replacements for it.

## References

* `TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, whose Layer 0.1 nonzero-ideal
  carrier and zero-extension design are adapted here.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open NumberField nonZeroDivisors

variable (K : Type*) [Field K]

/-- An **ideal arithmetic function** over a field `K`: a complex-valued function on the nonzero
ideals of `𝓞 K`.

The domain is `(Ideal (𝓞 K))⁰`, Mathlib's non-zero-divisor submonoid. Since the ring of integers is
a domain, its elements are exactly the ideals different from `⊥`. For number fields, keeping `⊥`
out of the carrier ensures that later divisor sums use only the nonzero-ideal factorization
theory. -/
abbrev IdealArithmeticFunction := (Ideal (𝓞 K))⁰ → ℂ

namespace IdealArithmeticFunction

variable {K}

/-- An ideal arithmetic function is multiplicative when it takes the unit ideal to `1` and
respects products of relatively prime nonzero ideals. This is weaker than the complete
multiplicativity carried by `MultiplicativeIdealWeight`. -/
structure IsMultiplicative (f : IdealArithmeticFunction K) : Prop where
  /-- A multiplicative ideal arithmetic function takes the unit ideal to `1`. -/
  map_one : f 1 = 1
  /-- A multiplicative ideal arithmetic function respects products of relatively prime ideals. -/
  map_mul_of_isRelPrime {I J : (Ideal (𝓞 K))⁰}
    (hIJ : IsRelPrime (I : Ideal (𝓞 K)) (J : Ideal (𝓞 K))) : f (I * J) = f I * f J



/-- Pointwise products of multiplicative ideal arithmetic functions are multiplicative. -/
theorem IsMultiplicative.mul {f g : IdealArithmeticFunction K}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) : (f * g).IsMultiplicative := by
  refine ⟨by simp [hf.map_one, hg.map_one], fun hIJ ↦ ?_⟩
  rw [Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, hf.map_mul_of_isRelPrime hIJ,
    hg.map_mul_of_isRelPrime hIJ]
  ring

/-- Complex conjugation preserves multiplicativity of ideal arithmetic functions. -/
theorem IsMultiplicative.star {f : IdealArithmeticFunction K} (hf : f.IsMultiplicative) :
    (star f).IsMultiplicative := by
  refine ⟨by simp [hf.map_one], fun hIJ ↦ ?_⟩
  simp only [Pi.star_apply, hf.map_mul_of_isRelPrime hIJ, star_mul']

section Factorization

open IsDedekindDomain (HeightOneSpectrum)

variable {f : IdealArithmeticFunction K}



variable [NumberField K]



end Factorization































/-! ## Compatibility with pointwise operations -/

















/-!
### Functoriality under an isomorphism of fields
-/

section Transport

variable {L M : Type*} [Field L] [Field M]

















/-! Transport preserves the pointwise structure inherited from `Pi`. -/















end Transport

end IdealArithmeticFunction

end TauCeti

end
end


