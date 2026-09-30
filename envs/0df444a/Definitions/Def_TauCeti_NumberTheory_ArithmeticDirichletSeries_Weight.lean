-- Prove2me | Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
-- name    : TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:43:13.958985+00:00
-- url     : https://prove2.me/theorems/8df28216-66c5-4b7d-b18e-c8630dff8b25
-- title:
--   Completely multiplicative ideal weights
-- statement:
--   A multiplicative ideal weight on a number field $K$ is a function $\chi$ from integral ideals to $\mathbb C$ with
--
--   $$
--   \chi(0)=0,\quad\chi(\mathcal O_K)=1,\quad\chi(IJ)=\chi(I)\chi(J),
--   $$
--
--   and only finitely many prime ideals $P$ satisfying $\chi(P)=0$. These are its bad primes. A unitary weight additionally has modulus one at every good prime. This is the coefficient data for degree-one Euler products.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Weight.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Weight.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Completely multiplicative ideal weights

The completely multiplicative specializations of `TauCeti.IdealArithmeticFunction`: the two
carriers on which every Euler product, Hecke character and character-family argument of this
development is stated.

A `TauCeti.MultiplicativeIdealWeight K` is a monoid-with-zero homomorphism
`Ideal (𝓞 K) →*₀ ℂ` killing only finitely many height-one primes, and
`TauCeti.UnitaryIdealWeight K` is the subtype of those whose values have modulus `1` away from
that finite bad set. Using Mathlib's `→*₀` vocabulary is what pins the zero-ideal law
`χ ⊥ = 0`; the finiteness condition is what bounds the bad local factors of the Euler product.

Both carriers are *degree one*: the value at `𝔭 ^ n` is forced to be `χ 𝔭 ^ n`. They are
therefore deliberately too narrow for the ideal Möbius function or for coefficient systems
whose prime-power values are independent local data; those get separate carriers.

The organising notion is `Ideal.IsPrimeTo`, an ideal of a Dedekind domain being nonzero and
divisible by no prime of a given set; it is stated for a general Dedekind domain because
nothing in it is specific to a number field. The good ideals of a weight are the ideals
prime to its bad primes, and `Ideal.IsPrimeTo.induction_on` factors such an ideal into
good primes; this is the engine behind both
`TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood` and
`TauCeti.UnitaryIdealWeight.norm_eq_one`.

## Main declarations

* `Ideal.IsPrimeTo`: an ideal is nonzero and no prime of `S` divides it, with its
  multiplicativity (`Ideal.isPrimeTo_mul_iff`) and its induction principle
  (`Ideal.IsPrimeTo.induction_on`);
* `TauCeti.MultiplicativeIdealWeight`: the general completely multiplicative carrier, its
  `TauCeti.MultiplicativeIdealWeight.badPrimes` and its good ideals
  (`TauCeti.MultiplicativeIdealWeight.IsGood`);
* `TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood`: a weight is nonzero exactly on
  the good ideals;
* `TauCeti.MultiplicativeIdealWeight.ext_heightOneSpectrum`: a weight is determined by its
  values at the height-one primes;
* `TauCeti.MultiplicativeIdealWeight.ofBadPrimes`, the pointwise `CommMonoid` structure (whose
  unit is the trivial weight), `TauCeti.MultiplicativeIdealWeight.restrict`,
  `TauCeti.MultiplicativeIdealWeight.conj` and
  `TauCeti.MultiplicativeIdealWeight.normTwist`: the constructors and operations;
* `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood` and
  `TauCeti.MultiplicativeIdealWeight.IsTrivialOnGood`: the weights agreeing with a purely
  imaginary norm twist, respectively with the trivial weight, on their good ideals, with the
  structure theorem `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.eq_normTwist`, its
  converse `TauCeti.MultiplicativeIdealWeight.isNormTwistOnGood_normTwist_ofBadPrimes`, and the
  behaviour of the parameter under conjugation, the pointwise product and a further twist;
* `TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction`: passage to the general
  carrier, inverted by `TauCeti.IdealArithmeticFunction.zeroExtend`;
* `TauCeti.UnitaryIdealWeight`: the unitary subtype, with
  `TauCeti.UnitaryIdealWeight.norm_eq_one` on all good ideals,
  `TauCeti.UnitaryIdealWeight.norm_normTwist` for the modulus of an arbitrary norm twist,
  `TauCeti.UnitaryIdealWeight.ofPowEqOne` for finite-order weights, and the operations
  `TauCeti.UnitaryIdealWeight.conj`, `TauCeti.UnitaryIdealWeight.restrict` and
  `TauCeti.UnitaryIdealWeight.normTwist` (the last for the imaginary norm twists only), and
  `TauCeti.UnitaryIdealWeight.toIdealArithmeticFunction` for its passage to the general carrier;
* `TauCeti.MultiplicativeIdealWeight.map` and `TauCeti.UnitaryIdealWeight.map`, with their
  equivalences `mapEquiv`: functoriality under an isomorphism `K ≃+* L` of the ambient fields,
  together with the identity and composition laws, the preservation of the pointwise product
  (`map_one` and `map_mul` on both carriers), the naturality of restriction, conjugation and norm
  twists, and the compatibilities
  `TauCeti.MultiplicativeIdealWeight.badPrimes_map` and
  `TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_map`.

## Rejection tests

The two worked negative examples of this layer are proved here.
`TauCeti.MultiplicativeIdealWeight.coe_ne_const_one` says the everywhere-one function on *all*
integral ideals underlies no weight, because `→*₀` forces the value `0` at `⊥` — the
everywhere-one function on the *nonzero* ideals is the trivial weight instead
(`TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one`).
`TauCeti.UnitaryIdealWeight.norm_normTwist_apply_ne_one` says that a norm twist with
`Re z ≠ 0` changes the modulus at every good ideal of absolute norm greater than one, so such
twists live only in the general carrier.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* `TauCetiRoadmap/ArithmeticDirichletSeries/README.md` and its `Suggested.lean` target
  signatures: this file implements the Layer 0 export contract stated there, and follows its
  naming and organization for the two weight carriers.
-/

 section

namespace TauCeti

open NumberField IsDedekindDomain nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]



/-!
### The general carrier of completely multiplicative ideal weights
-/

/-- A **multiplicative ideal weight** on a number field `K`: a completely multiplicative
complex-valued function on *all* integral ideals of `𝓞 K`, packaged as a monoid-with-zero
homomorphism `Ideal (𝓞 K) →*₀ ℂ`, which kills only finitely many height-one primes.

Being a `→*₀` forces the value `0` at the zero ideal `⊥` and the value `1` at `⊤`; the
finiteness condition is what makes the associated Euler product have finitely many bad local
factors. This carrier is *degree one*: its value at a prime power `𝔭 ^ n` is forced to be
`χ 𝔭 ^ n`, so it excludes the ideal Möbius function and any coefficient system whose
prime-power values are independent local data. -/
structure MultiplicativeIdealWeight (K : Type*) [Field K] [NumberField K] where
  /-- The underlying completely multiplicative map on all integral ideals. -/
  toMonoidWithZeroHom : Ideal (𝓞 K) →*₀ ℂ
  /-- Only finitely many height-one primes are killed. -/
  finite_setOf_apply_eq_zero :
    {𝔭 : HeightOneSpectrum (𝓞 K) | toMonoidWithZeroHom 𝔭.asIdeal = 0}.Finite

namespace MultiplicativeIdealWeight

instance : FunLike (MultiplicativeIdealWeight K) (Ideal (𝓞 K)) ℂ where
  coe χ := χ.toMonoidWithZeroHom
  coe_injective χ ψ h := by
    cases χ; cases ψ
    congr 1
    exact DFunLike.coe_injective h

instance : MonoidWithZeroHomClass (MultiplicativeIdealWeight K) (Ideal (𝓞 K)) ℂ where
  map_zero χ := χ.toMonoidWithZeroHom.map_zero
  map_one χ := χ.toMonoidWithZeroHom.map_one
  map_mul χ := χ.toMonoidWithZeroHom.map_mul



@[ext]
theorem ext {χ ψ : MultiplicativeIdealWeight K} (h : ∀ I, χ I = ψ I) : χ = ψ :=
  DFunLike.ext _ _ h

/-- **The zero-ideal law.** Every multiplicative ideal weight kills the zero ideal, so no
weight is the everywhere-one function on all ideals. -/
@[simp]
theorem apply_bot (χ : MultiplicativeIdealWeight K) : χ ⊥ = 0 := map_zero χ

@[simp]
theorem apply_top (χ : MultiplicativeIdealWeight K) : χ ⊤ = 1 := by
  simpa using map_one χ



/-- The **bad primes** of an ideal weight: the height-one primes it kills. This is a derived,
canonically determined accessor, not extra data. -/
def badPrimes (χ : MultiplicativeIdealWeight K) : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | χ 𝔭.asIdeal = 0}

@[simp]
theorem mem_badPrimes {χ : MultiplicativeIdealWeight K} {𝔭 : HeightOneSpectrum (𝓞 K)} :
    𝔭 ∈ χ.badPrimes ↔ χ 𝔭.asIdeal = 0 := Iff.rfl

theorem finite_badPrimes (χ : MultiplicativeIdealWeight K) : χ.badPrimes.Finite :=
  χ.finite_setOf_apply_eq_zero

variable {χ : MultiplicativeIdealWeight K}

/-- An ideal is **good** for `χ` when it is prime to the bad primes of `χ`. In particular a
good ideal is nonzero, even when `χ` has no bad primes at all. -/
abbrev IsGood (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) : Prop :=
  Ideal.IsPrimeTo I χ.badPrimes





/-!
### Constructors and operations
-/

section Operations

variable {S : Set (HeightOneSpectrum (𝓞 K))}

open scoped Classical in
/-- The **indicator weight** of a finite set `S` of height-one primes: the value is `1` on the
ideals prime to `S` and `0` elsewhere. Its bad primes are exactly `S`, and `ofBadPrimes ∅` is
the trivial weight `1`. -/
noncomputable def ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    MultiplicativeIdealWeight K where
  toMonoidWithZeroHom :=
    { toFun I := if Ideal.IsPrimeTo I S then 1 else 0
      map_zero' := by simp
      map_one' := by simp [Ideal.one_eq_top]
      map_mul' I J := by
        by_cases h : Ideal.IsPrimeTo (I * J) S
        · simp [h, (Ideal.isPrimeTo_mul_iff.mp h).1, (Ideal.isPrimeTo_mul_iff.mp h).2]
        · rcases not_and_or.mp (fun hc ↦ h (Ideal.isPrimeTo_mul_iff.mpr hc)) with h' | h' <;>
            simp [h, h'] }
  finite_setOf_apply_eq_zero := by
    convert hS using 1
    ext 𝔭
    simp

open scoped Classical in
/-- Defining equation of `TauCeti.MultiplicativeIdealWeight.ofBadPrimes`; its body is not
exposed. -/
@[simp]
theorem ofBadPrimes_apply (hS : S.Finite) (I : Ideal (𝓞 K)) :
    ofBadPrimes S hS I = if Ideal.IsPrimeTo I S then 1 else 0 := (rfl)

@[simp]
theorem badPrimes_ofBadPrimes (hS : S.Finite) : (ofBadPrimes S hS).badPrimes = S := by
  classical
  ext 𝔭
  simp [badPrimes, ofBadPrimes_apply]



/-- The pointwise product of two multiplicative ideal weights. -/
noncomputable instance : Mul (MultiplicativeIdealWeight K) where
  mul χ ψ :=
    { toMonoidWithZeroHom := χ.toMonoidWithZeroHom * ψ.toMonoidWithZeroHom
      finite_setOf_apply_eq_zero := by
        refine (χ.finite_badPrimes.union ψ.finite_badPrimes).subset fun 𝔭 h𝔭 ↦ ?_
        -- the product of two `→*₀` is built from the product of the underlying `→*`, so the
        -- value of the product is computed by `MonoidHom.mul_apply`
        have hzero : χ 𝔭.asIdeal * ψ 𝔭.asIdeal = 0 :=
          (MonoidHom.mul_apply χ.toMonoidWithZeroHom.toMonoidHom
            ψ.toMonoidWithZeroHom.toMonoidHom 𝔭.asIdeal).symm.trans h𝔭
        exact mul_eq_zero.mp hzero }

@[simp]
theorem mul_apply (χ ψ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    (χ * ψ) I = χ I * ψ I := (rfl)

/-- The trivial multiplicative ideal weight. -/
noncomputable instance : One (MultiplicativeIdealWeight K) where
  one :=
    { toMonoidWithZeroHom := 1
      finite_setOf_apply_eq_zero := by
        refine Set.finite_empty.subset fun 𝔭 h𝔭 ↦ ?_
        exact 𝔭.ne_bot (MonoidWithZeroHom.one_apply_eq_zero_iff.mp h𝔭) }

/-- The trivial weight is the indicator of the nonzero ideals. -/
@[simp]
theorem one_apply (I : Ideal (𝓞 K)) :
    (1 : MultiplicativeIdealWeight K) I = if I = ⊥ then 0 else 1 := by
  split_ifs with hI
  · subst I
    simp
  · exact MonoidWithZeroHom.one_apply_of_ne_zero hI



@[simp]
theorem badPrimes_mul (χ ψ : MultiplicativeIdealWeight K) :
    (χ * ψ).badPrimes = χ.badPrimes ∪ ψ.badPrimes := by
  ext 𝔭
  simp [badPrimes, mul_eq_zero]

/-- The pointwise product of multiplicative ideal weights, with the trivial weight as unit.
Ideal convolution (roadmap Layer 2) will instead be an operation on
`TauCeti.IdealArithmeticFunction`. -/
noncomputable instance : CommMonoid (MultiplicativeIdealWeight K) where
  mul_assoc χ ψ ω := by ext I; simp [mul_assoc]
  one_mul χ := by
    ext I
    rcases eq_or_ne I ⊥ with rfl | hI
    · simp
    · simp [one_apply, hI]
  mul_one χ := by
    ext I
    rcases eq_or_ne I ⊥ with rfl | hI
    · simp
    · simp [one_apply, hI]
  mul_comm χ ψ := by ext I; simp [mul_comm]





/-- **Restriction away from a finite set of primes**: `χ` is left unchanged on the ideals prime
to `S` and set to `0` on the others. -/
noncomputable def restrict (χ : MultiplicativeIdealWeight K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) : MultiplicativeIdealWeight K :=
  χ * ofBadPrimes S hS

open scoped Classical in
@[simp]
theorem restrict_apply (χ : MultiplicativeIdealWeight K) (hS : S.Finite) (I : Ideal (𝓞 K)) :
    χ.restrict S hS I = if Ideal.IsPrimeTo I S then χ I else 0 := by
  by_cases h : Ideal.IsPrimeTo I S <;> simp [restrict, ofBadPrimes_apply, h]

@[simp]
theorem badPrimes_restrict (χ : MultiplicativeIdealWeight K) (hS : S.Finite) :
    (χ.restrict S hS).badPrimes = χ.badPrimes ∪ S := by
  simp [restrict]

























/-!
### Weights that are norm twists on their good locus
-/



/-- A weight **is trivial on its good ideals** when it takes the value `1` at every ideal prime
to its bad primes; equivalently it is a norm twist on its good ideals with parameter `0`
(`TauCeti.MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff`). -/
def IsTrivialOnGood (χ : MultiplicativeIdealWeight K) : Prop :=
  ∀ I : Ideal (𝓞 K), χ.IsGood I → χ I = 1





















end Operations

/-!
### Passage to the general carrier, and the zero-ideal rejection test
-/

/-- The ideal arithmetic function underlying an ideal weight: its restriction to the nonzero
ideals. -/
def toIdealArithmeticFunction (χ : MultiplicativeIdealWeight K) : IdealArithmeticFunction K :=
  fun I ↦ χ I

@[simp]
theorem toIdealArithmeticFunction_apply (χ : MultiplicativeIdealWeight K) (I : (Ideal (𝓞 K))⁰) :
    χ.toIdealArithmeticFunction I = χ I := (rfl)



/-- The ideal arithmetic function underlying a completely multiplicative ideal weight is
multiplicative on relatively prime ideals. -/
theorem isMultiplicative_toIdealArithmeticFunction (χ : MultiplicativeIdealWeight K) :
    χ.toIdealArithmeticFunction.IsMultiplicative := by
  constructor <;> simp











/-!
### Functoriality under an isomorphism of fields
-/

section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]





















/-! Transport preserves the pointwise `CommMonoid` structure. -/













end Transport

end MultiplicativeIdealWeight

/-!
### The unitary subtype
-/

/-- A **unitary ideal weight**: a multiplicative ideal weight whose values have modulus `1`
away from its bad primes. Finite-order Hecke characters land here
(`TauCeti.UnitaryIdealWeight.ofPowEqOne`), and so do the purely imaginary norm twists
(`TauCeti.UnitaryIdealWeight.normTwist`); a norm twist with `Re z ≠ 0` does not
(`TauCeti.UnitaryIdealWeight.norm_normTwist_apply_ne_one`). -/
abbrev UnitaryIdealWeight (K : Type*) [Field K] [NumberField K] : Type _ :=
  {χ : MultiplicativeIdealWeight K //
    ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ χ.badPrimes → ‖χ 𝔭.asIdeal‖ = 1}

namespace UnitaryIdealWeight



-- Source. The statement and its proof follow `DirichletCharacter.norm_le_one` in Mathlib's
-- `Mathlib/NumberTheory/DirichletCharacter/Bounds.lean`, transposed from a Dirichlet character on
-- `ZMod n` to a unitary ideal weight: the case split there is on `IsUnit a` and closes with
-- `map_nonunit`, here it is on `MultiplicativeIdealWeight.IsGood` and closes with
-- `apply_eq_zero_iff_not_isGood`.



/-- The trivial weight is unitary. -/
noncomputable instance : One (UnitaryIdealWeight K) :=
  ⟨1, fun 𝔭 _ ↦ by simp [MultiplicativeIdealWeight.one_apply, 𝔭.ne_bot]⟩

@[simp]
theorem val_one : (1 : UnitaryIdealWeight K).1 = 1 := rfl

/-- The pointwise product of unitary weights is unitary. -/
noncomputable instance : Mul (UnitaryIdealWeight K) where
  mul χ ψ :=
    ⟨χ.1 * ψ.1, fun 𝔭 h𝔭 ↦ by
      rw [MultiplicativeIdealWeight.badPrimes_mul, Set.mem_union, not_or] at h𝔭
      rw [MultiplicativeIdealWeight.mul_apply, norm_mul, χ.2 𝔭 h𝔭.1, ψ.2 𝔭 h𝔭.2,
        one_mul]⟩

@[simp]
theorem val_mul (χ ψ : UnitaryIdealWeight K) : (χ * ψ).1 = χ.1 * ψ.1 := rfl

/-- Pointwise multiplication makes the unitary weights a commutative monoid. -/
noncomputable instance : CommMonoid (UnitaryIdealWeight K) where
  mul_assoc χ ψ ω := Subtype.ext (by simp only [val_mul]; exact mul_assoc _ _ _)
  one_mul χ := Subtype.ext (by simp only [val_mul, val_one]; exact one_mul _)
  mul_one χ := Subtype.ext (by simp only [val_mul, val_one]; exact mul_one _)
  mul_comm χ ψ := Subtype.ext (by simp only [val_mul]; exact mul_comm _ _)



/-- **Finite-order weights are unitary.** If a positive power of `χ` takes the value `1` at
every good prime — as for a finite-order Hecke character — then `χ` is unitary. -/
def ofPowEqOne (χ : MultiplicativeIdealWeight K) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ χ.badPrimes → χ 𝔭.asIdeal ^ n = 1) :
    UnitaryIdealWeight K :=
  ⟨χ, fun 𝔭 h𝔭 ↦ by
    refine (pow_left_inj₀ (norm_nonneg _) zero_le_one hn).mp ?_
    rw [← norm_pow, h 𝔭 h𝔭, norm_one, one_pow]⟩



















/-- Restricting a unitary weight away from a finite set of primes keeps it unitary: the
restricted weight is unchanged at the primes that are good for it. -/
noncomputable def restrict (χ : UnitaryIdealWeight K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) : UnitaryIdealWeight K :=
  ⟨χ.1.restrict S hS, fun 𝔭 h𝔭 ↦ by
    rw [MultiplicativeIdealWeight.badPrimes_restrict, Set.mem_union, not_or] at h𝔭
    rw [MultiplicativeIdealWeight.restrict_apply]
    simp [h𝔭.2, χ.2 𝔭 h𝔭.1]⟩





section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]















/-! Transport preserves the pointwise `CommMonoid` structure of the unitary carrier too. -/











end Transport

/-- The ideal arithmetic function underlying a unitary weight: the restriction of the
underlying multiplicative weight to the nonzero ideals. -/
def toIdealArithmeticFunction (χ : UnitaryIdealWeight K) : IdealArithmeticFunction K :=
  χ.1.toIdealArithmeticFunction















end UnitaryIdealWeight

end TauCeti

end
end


