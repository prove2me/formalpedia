-- Prove2me | Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimeCounting_VonMangoldt
-- name    : TauCeti_NumberTheory_Chebotarev_PrimeCounting_VonMangoldt
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:00:28.402553+00:00
-- url     : https://prove2.me/theorems/cd47a225-3540-4950-9a3e-ddf59c1868d2
-- title:
--   Frobenius von Mangoldt coefficients
-- statement:
--   For a finite Galois extension $L/K$ and a conjugacy class $C$, define the Frobenius prime-power count by
--
--   $$
--   \psi_C(x)=\sum_{\substack{P\text{ unramified},\ j\geq1\\(\operatorname{Art}(P))^j=C,\ \mathrm N(P^j)\leq x}}\log\mathrm N P.
--   $$
--
--   The corresponding prime-only weight gives $\vartheta_C$, and the unweighted prime count gives $\pi_C$. Extending the weight by zero to other ideals and grouping by norm supplies the Dirichlet coefficients used in the analytic argument.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/VonMangoldt.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/VonMangoldt.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Group_Conj
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_FrobeniusPrimeSet
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Frobenius von Mangoldt coefficients

For a conjugacy class `C` in the Galois group of a finite Galois extension `L / K`, this file
defines the von Mangoldt coefficient and summatory functions restricted to `C`. A prime power
`𝔭 ^ j` belongs to the `C`-fibre when the `j`-th power of the Artin class of `𝔭` is `C`.
Consequently a prime whose Artin class is not `C` can still contribute through a higher power.

The definitions retain only unramified primes: the Artin symbol is never evaluated at a ramified
prime. The exponent-one terms form `frobeniusTheta`; all higher prime powers are dominated by the
unrestricted higher-prime-power weight from the arithmetic Dirichlet-series development, hence
their contribution is `o(x)`.

## Main definitions

* `NumberField.Chebotarev.frobeniusPrimePowerSet`: prime powers selected by the powered Artin
  class.
* `NumberField.Chebotarev.frobeniusVonMangoldtCoeff`: the corresponding nonnegative arithmetic
  function, regrouped by absolute norm.
* `NumberField.Chebotarev.frobeniusPsi` and `NumberField.Chebotarev.frobeniusTheta`: the weighted
  prime-power and prime summatory functions.
* `NumberField.Chebotarev.frobeniusPrimeCount`: the number of primes of norm at most `x`
  whose arithmetic Frobenius class is `C`, with `NumberField.Chebotarev.natCast_frobeniusPrimeCount`
  identifying it with the generic count of `frobeniusPrimeSet`.

## Main results

* `NumberField.Chebotarev.frobeniusVonMangoldtCoeff_rat_natGenerator_pow`: over `ℚ`, the
  coefficient at `p ^ (k + 1)` is the powered Frobenius weight of `𝔭 ^ (k + 1)`, the only ideal
  of that norm.
* `NumberField.Chebotarev.frobeniusPsi_eq_sum_range`: `frobeniusPsi` is the inclusive partial sum
  of `frobeniusVonMangoldtCoeff`.
* `NumberField.Chebotarev.frobeniusPsi_eq_sum_Icc`: the same sum indexed from `1`.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_eq_primePowerSummatory`: their
  difference is exactly the contribution from exponents at least two.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_le`: that difference is bounded by
  the unrestricted higher-prime-power tail.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_isLittleO`: this difference is `o(x)`.

The coefficient convention follows Neukirch, *Algebraic Number Theory*, Chapter VII. The
construction reuses Tau Ceti's generic prime-power counting and removal estimates.
-/

 section

namespace NumberField.Chebotarev

open Filter TauCeti
open scoped Asymptotics nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

-- The powered-class convention follows `TauCetiRoadmap/Chebotarev/Suggested.lean`.
variable (K L) in
/-- The prime powers whose powered Artin class is `C`. A prime power `𝔭 ^ j` is included when
`𝔭` is unramified in `L` and `(artinSymbol 𝔭) ^ j = C`. -/
def frobeniusPrimePowerSet (C : ConjClasses (L ≃ₐ[K] L)) : Set (IdealPrimePower K) :=
  {A | ∃ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q,
    artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C}





-- Not `@[simp]`: `mem_frobeniusPrimePowerSet_iff` together with `primePowerBase_ofPrime`,
-- `primePowerExponent_ofPrime` and `ConjClasses.pow_one` already rewrites the left-hand side.


variable (K L) in
/-- The logarithmic weight on prime powers selected by their powered Artin class. -/
noncomputable def frobeniusPrimePowerWeight (C : ConjClasses (L ≃ₐ[K] L))
    (A : IdealPrimePower K) : ℝ :=
  (frobeniusPrimePowerSet K L C).indicator primePowerWeight A













variable (K L) in
/-- Chebyshev's `ψ` restricted by powered Frobenius class: the inclusive sum of `log N(𝔭)` over
`𝔭 ^ j` of norm at most `x` for which `(artinSymbol 𝔭) ^ j = C`. -/
noncomputable def frobeniusPsi (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) : ℝ :=
  primePowerSummatory K (frobeniusPrimePowerWeight K L C) x

variable (K L) in
/-- Chebyshev's `ϑ` restricted to the primes whose unpowered Artin class is `C`. -/
noncomputable def frobeniusTheta (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) : ℝ :=
  primeTheta K (frobeniusPrimeSet K L C) x

variable (K L) in
open Classical in
/-- The number of primes of `K` of norm at most `x` whose arithmetic Frobenius in `L/K`
belongs to `C`. Only primes unramified in `L` are counted. -/
noncomputable def frobeniusPrimeCount (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) : ℕ :=
  ((primesLE K x).filter (· ∈ frobeniusPrimeSet K L C)).card



















variable (K L) in
/-- The powered Frobenius weight on nonzero ideals, extended by zero away from prime powers. -/
noncomputable def frobeniusVonMangoldtWeight (C : ConjClasses (L ≃ₐ[K] L))
    (I : (Ideal (𝓞 K))⁰) : ℝ := by
  classical
  exact if hI : IsPrimePow (I : Ideal (𝓞 K)) then
      frobeniusPrimePowerWeight K L C ⟨I, hI⟩ else 0







variable (K L) in
/-- The Frobenius von Mangoldt coefficient at `n`: the sum of `log N(𝔭)` over prime powers
`𝔭 ^ j` of absolute norm `n` whose `j`-th powered Artin class is `C`. -/
noncomputable def frobeniusVonMangoldtCoeff (C : ConjClasses (L ≃ₐ[K] L)) :
    ArithmeticFunction ℝ where
  toFun n := ∑ I ∈ normFiber K n, frobeniusVonMangoldtWeight K L C I
  map_zero' := by rw [normFiber_zero, Finset.sum_empty]





-- The powered filter is exercised here: this is the term a definition filtering on
-- `artinSymbol 𝔭 = C` alone would lose. The order-four configuration is not vacuous —
-- `ConjClasses.mk_ne_mk_of_orderOf_ne` separates the two classes for *every* element of order
-- four, its square having order two, and the cyclic group of order four realises such an element
-- concretely.




















end NumberField.Chebotarev

end
end


