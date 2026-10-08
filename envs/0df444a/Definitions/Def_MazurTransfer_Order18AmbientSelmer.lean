-- Prove2me | Definitions.Def_MazurTransfer_Order18AmbientSelmer
-- name    : MazurTransfer_Order18AmbientSelmer
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T18:46:38.482231+00:00
-- url     : https://prove2.me/theorems/70f46ae8-6284-4fc0-820d-0d29aa304675
-- title:
--   Order-18 exact supported Selmer space and valuation-certificate type
-- statement:
--   The original degree-nine field carries its relative integral closure, unit and field square-class quotients, dyadic supported square classes, relative norm homomorphism, and explicit candidate representative family. The DyadicValuationCertificate declaration is a structure type: it requires an enumeration of two dyadic places, support membership and the prescribed valuation-parity matrix. This file does not assert that the structure is inhabited, that any candidate lies in the norm kernel, or that the candidates exhaust or independently generate that kernel. Its six nonzero constructor witnesses are direct projections of the separately Proved public representative theorem. Remaining proof fields are generic quotient/instance construction laws or projections from a supplied certificate. Named downstream consumer: MazurTorsion.XOneEighteenDyadicValuationCertificate.dyadicValuationCertificate.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Original complete Lean AST commands selected by resolved source references and kernel dependencies. Original mathematical data and certificate type retained; only six proof values replaced by direct projections of the separately Proved public nonzero theorem. Apache-2.0 source headers and authors retained. No Selmer cardinality, actual certificate witness, norm-kernel membership or torsion exclusion is exported.

import Mathlib
import Definitions.Def_MazurTransfer_Order18CompositumField
import Theorems.Thm_MazurTransfer_order18_selmer_representatives_nonzero

noncomputable section
namespace MazurTorsion.XOneEighteenCoefficientFieldArithmetic
end MazurTorsion.XOneEighteenCoefficientFieldArithmetic
namespace MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
end MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
namespace EllipticCurves.X18SelmerCardinality
end EllipticCurves.X18SelmerCardinality
namespace MazurTorsion.XOneEighteenTwoDivisionExactSignature
end MazurTorsion.XOneEighteenTwoDivisionExactSignature
namespace MazurTorsion.XOneEighteenDescentAlgebraEquiv
end MazurTorsion.XOneEighteenDescentAlgebraEquiv
namespace MazurTorsion.XOneEighteenCoefficientDyadicSelmer
end MazurTorsion.XOneEighteenCoefficientDyadicSelmer
namespace MazurTorsion.XOneEighteenSelmerSieve
end MazurTorsion.XOneEighteenSelmerSieve
namespace MazurTorsion.XOneEighteenMinimalTwoDescentModel
end MazurTorsion.XOneEighteenMinimalTwoDescentModel
namespace MazurTorsion.XOneEighteenQuotientTwoDescentModel
end MazurTorsion.XOneEighteenQuotientTwoDescentModel
namespace MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
end MazurTorsion.XOneEighteenTwoDivisionSmallPrimes


/- Source module: EllipticCurves.Mathlib.Basic. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# Material for Mathlib

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in `PORTING.md`.

This file collects the general-purpose results developed for `EllipticCurves.WeakMordellWeil`
that have nothing to do with elliptic curves and look like candidates for Mathlib.

* `MonoidHom.ofMapMulMulEqOne`: build a `MonoidHom` from `f 1 = 1` and
  `a * b * c = 1 → f a * f b * f c = 1`.
* `Valuation.map_eval_eq_of_one_lt` and `Valuation.le_one_of_root_monic`: dominance of the
  leading term of a monic polynomial with integral coefficients, and integrality of its roots.
  `Valuation.eq_one_of_mul_eq_one`: a factor of a unit is a unit, provided both factors are
  integral.
* `IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one`,
  `.below` (the prime lying below a prime of an integral extension), `.primesAbove` and its
  finiteness `.primesAbove_finite`,
  `IsDedekindDomain.selmerGroupAbove`, `.valuationOfNeZero_eq_iff`,
  `.dvd_toAdd_valuationOfNeZero` and
  `.valuationOfNeZeroMod_mk_eq_one_iff`, which turns the Selmer condition into a
  divisibility of valuations; `Set.integer_mono` and `Set.unit_mono`, monotonicity of the
  `S`-integers and `S`-units in `S`. (`Mathlib.RingTheory.DedekindDomain.SelmerGroup` has a
  `TODO` about the `Multiplicative`/`Additive` defeq abuse in `valuationOfNeZeroMod`
  and provides no API for it.)
* `Units.modPow`, the group of `n`-th power classes of units, which
  `Mathlib.RingTheory.DedekindDomain.SelmerGroup` has only as a local notation, together
  with `map`, `congr` and `piEquiv`.
* Division with remainder by a monic polynomial: `Polynomial.Monic.divByMonic_mul_add`,
  `.modByMonic_mul_add`, `modByMonic_mem_degreeLT`, `divByMonic_mem_degreeLT`.
* `isIntegralClosure_int_integralClosure`, `NumberField.finite_classGroup_integralClosure` and
  `NumberField.fg_units_integralClosure`: the class number theorem and the finite generation of
  the unit group for the integral closure of `𝓞 K` in a finite extension of a number field `K`;
  `NumberField.subsingleton_classGroup_integralClosure` and
  `NumberField.finrank_additive_units_integralClosure` transport triviality of the class
  group and the unit rank from `𝓞 L`.
* `AdjoinRoot.discr_powerBasis_eq_discr`, `NumberField.exists_eq_discr_mul_sq`,
  `RingOfIntegers.isPrincipalIdealRing_of_finrank_eq_three_of_abs_discr_le` and
  `RingOfIntegers.finrank_additive_units_of_discr_neg`/`_pos`: the discriminant of the power
  basis of `K[X]/(f)` is `f.discr`; the field discriminant is any integral power-basis
  discriminant divided by a square; a cubic field with `|discr| ≤ 49` has trivial class group
  (Minkowski bound), and the sign of its discriminant determines the unit rank (Dirichlet).
* `AdjoinRoot.norm_mk_eq_resultant`: for monic `g`, the norm of `AdjoinRoot.mk g p` is the
  resultant of `g` and `p`. This links `Polynomial.resultant` to `Algebra.norm`.
* `AdjoinRoot.equivPiFactors`: for nonzero squarefree `f`, `K[X]/(f)` is the product of the
  fields `K[X]/(p)` over the monic irreducible factors `p` of `f`, and the induced
  `AdjoinRoot.modPowEquivPiFactors` on `n`-th power classes of units.
* `Polynomial.discr_X_sub_C_mul`: splitting off a linear factor multiplies the discriminant
  by the square of the evaluation, `((X - C x) * g).discr = g.discr * g.eval x ^ 2`.
* `Matrix.det_blockDiagonal'`, `LinearMap.det_pi'`, `Algebra.norm_prod`, `Algebra.norm_pi`:
  determinants and norms on (dependent) products decompose as products; together with
  `AdjoinRoot.norm_eq_prod_norm_projFactor`, the norm on `K[X]/(f)` as the product of the
  norms on the field factors.
* General helpers extracted from the rank example: `Squarefree.map` (transport along a
  `MulEquiv`), `Polynomial.Monic.irreducible_map_fraction_map_of_irreducible_map`
  (irreducibility over the fraction field via reduction modulo a prime),
  `Polynomial.Factors.coe_eq`, `AdjoinRoot.isIntegralElem_root_of_map`,
  `AdjoinRoot.finrank_eq_natDegree`, and the `IsPrincipalIdealRing (𝓞 ℚ)` instance.
-/

section

section Group

variable {G H : Type*} [Group G] [Group H]









end Group

section Units

variable {α : Type*} [Monoid α]





end Units

section modPow



/-- The group of `n`-th power classes of units of `α`. This is the group underlying the
Selmer groups of `Mathlib.RingTheory.DedekindDomain.SelmerGroup`, where it only exists
as a local notation. -/
abbrev Units.modPow (α : Type*) [CommMonoid α] (n : ℕ) : Type _ :=
  αˣ ⧸ (powMonoidHom n : αˣ →* αˣ).range

/-- A multiplicative equivalence of commutative groups induces one on the quotients by the
subgroups of `n`-th powers. -/
def QuotientGroup.congrRangePowMonoidHom {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr _ _ e <| by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨e u, by simp⟩
    · rintro ⟨u, rfl⟩
      exact ⟨e.symm u ^ n, ⟨_, rfl⟩, by simp⟩

namespace Units.modPow

variable {α β : Type*} [CommMonoid α] [CommMonoid β] {a b c : α}

open QuotientGroup

















/-- A monoid homomorphism `α →* β` induces a homomorphism on `n`-th power classes of units. -/
def map (φ : α →* β) (n : ℕ) : Units.modPow α n →* Units.modPow β n :=
  QuotientGroup.map _ _ (Units.map φ) <| by
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map φ u, by simp [powMonoidHom]⟩









/-- A multiplicative equivalence `α ≃* β` induces one on `n`-th power classes of units. -/
def congr (e : α ≃* β) (n : ℕ) : Units.modPow α n ≃* Units.modPow β n :=
  congrRangePowMonoidHom (Units.mapEquiv e) n









end Units.modPow

end modPow

section Ideal



end Ideal

section LinearAlgebra







end LinearAlgebra

section Valuation

open Polynomial

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (ν : Valuation L Γ)
  {t a b : L}









end Valuation

section DedekindDomain

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]























variable (R) (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra R B]

/-- The primes of `B` lying above a set `S` of primes of `R`. -/
def IsDedekindDomain.HeightOneSpectrum.primesAbove (S : Set (HeightOneSpectrum R)) :
    Set (HeightOneSpectrum B) :=
  {w | ∃ v ∈ S, v.asIdeal = w.asIdeal.under R}

-- The `IsDedekindDomain` instances are needed to *state* this (they are parameters of
-- `HeightOneSpectrum`), but are erased from the proof term (`nolint unusedArguments`),
-- which makes the linter fire spuriously.


-- as for `primesAbove_mono`, the `IsDedekindDomain` instances are needed for the statement
















-- as for `mem_selmerGroupAbove_iff`, the instances are needed for the statement only


namespace IsDiscreteValuationRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]



variable {A}



end IsDiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]



-- the `IsDedekindDomain` instances are needed to state this, but the proof (`rfl`) erases them


variable {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
  [Field N] [Algebra C N] [IsFractionRing C N]







end IsDedekindDomain.HeightOneSpectrum

end DedekindDomain

namespace Polynomial

variable {R : Type*} [CommRing R] {g : R[X]}



















section

variable [Nontrivial R] {q : R[X]} {n : ℕ}















end

section Sylvester

open Module LinearMap LinearEquiv

variable [Nontrivial R] {p : R[X]} {n : ℕ}

/-!
### The norm on `AdjoinRoot g` is the resultant

Write `m = g.natDegree` and `n = p.natDegree`. The Sylvester map
`S : R[X]_m × R[X]_n →ₗ R[X]_(m+n)`, `(u, v) ↦ g * v + p * u`, has the Sylvester matrix as its
matrix, so `det S = resultant g p m n`.

Taking `p = 1` gives a map `Ψ : (u, v) ↦ g * v + u`, which is a linear *equivalence* when `g` is
monic (its inverse is `q ↦ (q %ₘ g, q /ₘ g)`), and `det Ψ = resultant g 1 m n = 1`.

Now `S = Ψ ∘ₗ B` where `B := Ψ⁻¹ ∘ₗ S` is the endomorphism
`(u, v) ↦ ((p * u) %ₘ g, v + (p * u) /ₘ g)` of `R[X]_m × R[X]_n`, by `modByMonic_add_div`.
In the block decomposition the matrix of `B` is lower triangular with diagonal blocks
`mulModByMonic hg p` and `1`, so `det B = det (mulModByMonic hg p)`.

Finally `mk g : R[X]_m ≃ₗ AdjoinRoot g` conjugates `mulModByMonic hg p` into multiplication by
`mk g p`, whose determinant is by definition `Algebra.norm R (mk g p)`.

No signs appear anywhere: `B` is an endomorphism, so the two blocks are never reordered.
-/



















end Sylvester



end Polynomial

open Polynomial LinearMap LinearEquiv

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {g : R[X]} {n : ℕ}



















section Map

variable {S : Type*} [CommRing S] (σ : R →+* S)



end Map

end AdjoinRoot



/-! ### The norm on a product algebra -/





section EtaleDecomposition

/-!
### Decomposition of `K[X]/(f)` into a product of fields

For a nonzero squarefree `f` over a field `K`, the étale algebra `AdjoinRoot f` is the product
of the fields `AdjoinRoot p`, where `p` runs over the distinct irreducible factors of `f`.
This is what lets one talk about the primes, and hence the Selmer group, of `AdjoinRoot f`:
they are those of the factors.

If moreover `f` is separable, each factor is separable, so each `AdjoinRoot p` is a finite
separable extension of `K` and its integral closure over a Dedekind domain is again Dedekind.
-/

open Polynomial UniqueFactorizationMonoid

namespace Polynomial

variable {K : Type*} [Field K] {f : K[X]}



namespace Factors





































end Factors

end Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K] {f : K[X]}



































end AdjoinRoot

end EtaleDecomposition

/-!
### Rings of integers in finite extensions of number fields

The integral closure of `𝓞 K` in a finite extension `L` of a number field `K` is (isomorphic to)
the ring of integers of `L`; consequently the class number theorem and (the finite-generation
part of) Dirichlet's unit theorem apply to it.
-/

section NumberField

open NumberField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]





variable [NumberField K] [FiniteDimensional K L]









end NumberField

/-!
### Discriminants, class numbers, and unit ranks of cubic fields

The discriminant of a number field is the discriminant of any power basis with integral
generator divided by a square; consequently a cubic field whose power-basis discriminant is
at most `49` in absolute value has trivial class group (by the Minkowski bound), and the sign
of the power-basis discriminant determines the signature and hence, by Dirichlet's unit
theorem, the unit rank (`1` if negative, `2` if positive).
-/

section Discriminant

open NumberField Module

variable {K : Type*} [Field K] [NumberField K]









end Discriminant

end

end


/- Source module: EllipticCurves.X18SelmerCardinality. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Cardinality bookkeeping for the `X₁(18)` two-descent

This file supplies the finite-group bookkeeping which turns checked global
square-class data into the cardinalities used by the `X₁(18)` descent.  It
uses the valuation map already attached to a Dedekind Selmer group and the
unit--Selmer--class-group exact sequence from
`MazurTorsion.NumberTheory.SelmerClassGroup`.

There is deliberately no arithmetic oracle here.  The concrete theorem at
the end consumes three independently checkable certificates:

* the cardinality of integral-unit square classes;
* surjectivity of the supported valuation map;
* a splitting of the norm on square classes.

It then proves, rather than assumes, finiteness of every group involved and
the numerical conclusions `256` and `16`.
-/

open IsDedekindDomain

namespace EllipticCurves.X18SelmerCardinality

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## Explicit unit-parity certificates -/



























section Support

variable (S : Set (HeightOneSpectrum R)) (n : ℕ)



abbrev SupportedSelmer :=
  selmerGroup (R := R) (K := K) (S := S) (n := n)

abbrev supportValuation :
    SupportedSelmer (R := R) (K := K) S n →*
      S → Multiplicative (ZMod n) :=
  selmerGroup.valuation

/-- The nontrivial element of the multiplicative copy of `ZMod 2`. -/
def parityOne : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1













end Support

section SplitNorm

variable {G : Type v} [Group G] {H : Type w} [Group H]





end SplitNorm

section Concrete

variable (S : Set (HeightOneSpectrum R))



end Concrete

end

end EllipticCurves.X18SelmerCardinality

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenCoefficientDyadicSelmer. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The dyadic supported squareclasses of the `X₁(18)` coefficient field

The rational prime `2` is inert in the real cubic coefficient field.  Thus
there is one dyadic place, the class of `2` supplies its nonzero valuation
parity, and the supported squareclass group has cardinality
`8 * 2 = 16`.
-/

open IsDedekindDomain NumberField Ideal RingOfIntegers
  UniqueFactorizationMonoid

namespace MazurTorsion.XOneEighteenCoefficientDyadicSelmer

noncomputable section

open EllipticCurves.X18SelmerCardinality
open MazurTorsion.XOneEighteenCoefficientFieldArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K

/-- The even places of the real cubic coefficient field. -/
def coefficientDyadicSupport : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | v.valuation K 2 ≠ 1}



private instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

















































end

end MazurTorsion.XOneEighteenCoefficientDyadicSelmer

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenGlobalSelmerBridge. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Global Selmer bookkeeping for the `X₁(18)` two-descent

This module connects the arithmetic of the explicit degree-nine
two-division field to the generic supported-Selmer cardinality package.
The remaining prime and local-image calculations enter through narrow
certificate hypotheses: the theorem below does not assume a Selmer or
Mordell--Weil conclusion.
-/

open IsDedekindDomain NumberField Polynomial

namespace MazurTorsion.XOneEighteenGlobalSelmerBridge

noncomputable section

open EllipticCurves.X18SelmerCardinality
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionExactSignature
open MazurTorsion.XOneEighteenDescentAlgebraEquiv
open MazurTorsion.XOneEighteenCoefficientDyadicSelmer
open MazurTorsion.XOneEighteenSelmerSieve
open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K

/-- The integral closure occurring in the unique irreducible field factor
of the generic descent algebra. -/
abbrev RelativeIntegers := integralClosure (𝓞 K) M

instance relativeIntegersIsDedekindDomain :
    IsDedekindDomain RelativeIntegers :=
  IsIntegralClosure.isDedekindDomain (𝓞 K) K M _

instance relativeIntegersIsFractionRing :
    IsFractionRing RelativeIntegers M :=
  IsIntegralClosure.isFractionRing_of_finite_extension (𝓞 K) K M _

/-- The relative integral closure is canonically the absolute ring of
integers of the same degree-nine field. -/
def relativeIntegersEquiv : RelativeIntegers ≃+* 𝓞 M :=
  (IsIntegralClosure.equiv (𝓞 K) RelativeIntegers M (𝓞 M)).toRingEquiv

/-- The induced equivalence on integral-unit square classes. -/
def relativeUnitSquareclassEquiv :
    Units.modPow RelativeIntegers 2 ≃* Units.modPow (𝓞 M) 2 :=
  Units.modPow.congr relativeIntegersEquiv.toMulEquiv 2



/-! ## The exact dyadic support -/

/-- The primes in the degree-nine field lying above the even places of the
coefficient field.  This is the support used by the explicit descent. -/
def compositumDyadicSupport : Set (HeightOneSpectrum RelativeIntegers) :=
  HeightOneSpectrum.primesAbove (𝓞 K) RelativeIntegers
    coefficientDyadicSupport

/-- Square classes in the degree-nine field supported at the dyadic
primes. -/
abbrev DyadicSelmerM :=
  selmerGroup (R := RelativeIntegers) (K := M)
    (S := compositumDyadicSupport) (n := 2)

/-! ## The minimal model has genuinely dyadic bad support -/



















/-! ## Relative norm and its four checked kernel generators -/

/-- The relative norm from the degree-nine field to the real cubic field,
on square classes. -/
def relativeNormSquareclasses :
    Units.modPow M 2 →* Units.modPow K 2 :=
  Units.modPow.map (Algebra.norm K) 2





/-- The squareclass of a nonzero field element. -/
def fieldSquareclass (x : M) (hx : x ≠ 0) : Units.modPow M 2 :=
  QuotientGroup.mk (Units.mk0 x hx)

private theorem h1_ne_zero : h1 ≠ 0 := by
  exact MazurTransfer.order18_selmer_representatives_nonzero.2.2.1


private theorem h2_ne_zero : h2 ≠ 0 := by
  exact MazurTransfer.order18_selmer_representatives_nonzero.2.2.2.1


private theorem h3_ne_zero : h3 ≠ 0 := by
  exact MazurTransfer.order18_selmer_representatives_nonzero.2.2.2.2.1




private theorem h4_ne_zero : h4 ≠ 0 := by
  exact MazurTransfer.order18_selmer_representatives_nonzero.2.2.2.2.2


private theorem alpha_ne_zero : alpha ≠ 0 := by
  exact MazurTransfer.order18_selmer_representatives_nonzero.1


private theorem beta_ne_zero : beta ≠ 0 := by
  exact MazurTransfer.order18_selmer_representatives_nonzero.2.1


/-- The actual squareclass of the first dyadic generator `alpha`. -/
def alphaSquareclass : Units.modPow M 2 :=
  fieldSquareclass alpha alpha_ne_zero

/-- The actual squareclass of the second dyadic generator `beta`. -/
def betaSquareclass : Units.modPow M 2 :=
  fieldSquareclass beta beta_ne_zero

/-- The four explicit squareclasses with square relative norm. -/
def kernelGenerator : Fin 4 → Units.modPow M 2
  | 0 => fieldSquareclass h1 h1_ne_zero
  | 1 => fieldSquareclass h2 h2_ne_zero
  | 2 => fieldSquareclass h3 h3_ne_zero
  | 3 => fieldSquareclass h4 h4_ne_zero





/-- The product selected by the four low bits of a mask. -/
def kernelRepresentative (mask : Fin 16) : Units.modPow M 2 :=
  (if mask.val.testBit 0 then kernelGenerator 0 else 1) *
  (if mask.val.testBit 1 then kernelGenerator 1 else 1) *
  (if mask.val.testBit 2 then kernelGenerator 2 else 1) *
  (if mask.val.testBit 3 then kernelGenerator 3 else 1)





/-! ## Cardinality from genuine arithmetic certificates -/

/-- A two-prime valuation certificate records the two actual dyadic
places and the valuation-parity matrix of the classes of `alpha` and
`beta`.  Surjectivity is derived from the matrix, not stored in the
certificate. -/
structure DyadicValuationCertificate where
  places : Fin 2 ≃ compositumDyadicSupport
  alpha_mem : alphaSquareclass ∈ DyadicSelmerM
  beta_mem : betaSquareclass ∈ DyadicSelmerM
  alpha_at_zero :
    supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 ⟨alphaSquareclass, alpha_mem⟩ (places 0) = parityOne
  alpha_at_one :
    supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 ⟨alphaSquareclass, alpha_mem⟩ (places 1) = 1
  beta_at_zero :
    supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 ⟨betaSquareclass, beta_mem⟩ (places 0) = 1
  beta_at_one :
    supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 ⟨betaSquareclass, beta_mem⟩ (places 1) = parityOne





/-! ## The actual ambient relative norm -/

/-- The dyadically supported source mapped by relative norm to the full
coefficient-field squareclass group.  No unsupported claim that relative
norm preserves dyadic support is needed. -/
def fullDyadicRelativeNorm :
    DyadicSelmerM →* Units.modPow K 2 :=
  relativeNormSquareclasses.comp DyadicSelmerM.subtype























/-! ## The global subgroup consumed by the Selmer sieve -/





/-! ## The unique generic descent factor -/











/-! ## Integral-closure transport for the unique factor -/































end

end MazurTorsion.XOneEighteenGlobalSelmerBridge

end

#print axioms MazurTorsion.XOneEighteenGlobalSelmerBridge.RelativeIntegers
#print axioms MazurTorsion.XOneEighteenGlobalSelmerBridge.relativeIntegersEquiv
#print axioms MazurTorsion.XOneEighteenGlobalSelmerBridge.relativeUnitSquareclassEquiv
#print axioms MazurTorsion.XOneEighteenGlobalSelmerBridge.compositumDyadicSupport
#print axioms MazurTorsion.XOneEighteenGlobalSelmerBridge.DyadicSelmerM
#print axioms MazurTorsion.XOneEighteenGlobalSelmerBridge.fieldSquareclass
#print axioms MazurTorsion.XOneEighteenGlobalSelmerBridge.relativeNormSquareclasses
#print axioms MazurTorsion.XOneEighteenGlobalSelmerBridge.fullDyadicRelativeNorm
#print axioms MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelGenerator
#print axioms MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelRepresentative
#print axioms MazurTorsion.XOneEighteenGlobalSelmerBridge.DyadicValuationCertificate
end


