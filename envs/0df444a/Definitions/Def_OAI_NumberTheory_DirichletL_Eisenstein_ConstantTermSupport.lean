-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConstantTermSupport
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_ConstantTermSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:54:00.529523+00:00
-- url     : https://prove2.me/theorems/9ef99518-3e86-43c7-8be3-52aebfb220a4
-- title:
--   Constant Term Support
-- statement:
--   Definitions and structural lemmas for Constant Term Support, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/ConstantTermSupport.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FixedProfiles
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
namespace CubicEisenstein
open MeasureTheory Set Filter
open scoped BigOperators Classical
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid
end
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
end
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
end CubicEisenstein
open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
def idealZeroMask (D : Ideal O) (z : O) : ℂ :=
  if ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P then 0 else 1
def gcdMaskPrimes (D : Ideal O) : Finset (Ideal O) :=
  {Ideal.span {lambda}, Ideal.span {(2 : O)}} ∪
    (UniqueFactorizationMonoid.normalizedFactors D).toFinset
instance gcdMaskPrimes_maximal (D : Ideal O) (P : gcdMaskPrimes D) : P.val.IsMaximal := by
  rcases Finset.mem_union.mp P.property with hp | hp
  · rcases Finset.mem_insert.mp hp with hp | hp
    · rw [hp]
      exact lambdaIdeal_maximal
    · rw [Finset.mem_singleton.mp hp]
      exact twoIdeal_maximal
  · have h := UniqueFactorizationMonoid.prime_of_normalized_factor P.val (Multiset.mem_toFinset.mp hp)
    exact (Ideal.isPrime_of_prime h).isMaximal h.ne_zero
end
section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport QuadraticUnitInvariance PrimaryIdealUnitReindex
end
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex
end CanonicalQuadraticSieve
end
end OAI


