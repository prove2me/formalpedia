-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T05:59:12.986204+00:00
-- url     : https://prove2.me/theorems/073cc9c8-7ea6-46d8-9541-d098950e424b
-- title:
--   Annular Lifting
-- statement:
--   Definitions and structural lemmas for Annular Lifting, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularLifting.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Theorems.Thm_OAI_CanonicalQuadraticSieve_admissible_idealQuotient
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealQuotient_norm_le
import Theorems.Thm_OAI_CanonicalQuadraticSieve_liftingPrime_norm
import Theorems.Thm_OAI_CanonicalQuadraticSieve_liftingPrime_prime

set_option autoImplicit false
namespace OAI
noncomputable section
namespace CanonicalQuadraticSieve
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
section
open scoped BigOperators Classical
section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss QuadraticSquarefreeKernel
def squarefreeHighRange (M K : ℝ) : Finset (Ideal O) :=
  (idealRange M).filter (fun I => K<(Ideal.absNorm I:ℝ))
def annularLift (M K : ℝ) (I : squarefreeHighRange M K) : Ideal O :=
  liftedRow M I.val (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1.1
    (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).2
end
section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open FiniteSieveRestriction
def liftingDivisibleColumns (N : ℝ) : Finset (idealRange N) :=
  Finset.univ.filter (fun J => liftingPrime∣J.val)
def liftingQuotientColumn (N : ℝ) (J : liftingDivisibleColumns N) : idealRange N :=
  ⟨idealQuotient liftingPrime J.val.val, by
    have hd := (Finset.mem_filter.mp J.property).2
    have hj := mem_idealRange.mp J.val.property
    refine mem_idealRange.mpr ⟨admissible_idealQuotient hj.1 hd,?_⟩
    have hn := idealQuotient_norm_le liftingPrime_prime.ne_zero hd N hj.2
    rw [liftingPrime_norm] at hn
    have hN : 0≤N := (Nat.cast_nonneg _).trans hj.2
    exact hn.trans (by norm_num; linarith)⟩
def liftingFreeCoefficient (N : ℝ) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  fun J => if liftingPrime∣J.val then 0 else a J
def liftingDividedCoefficient (N : ℝ) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  extendByZero Finset.univ (liftingQuotientColumn N) (fun J : liftingDivisibleColumns N => a J.val)
end
section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss FiniteSieveOperator
def ballQuadraticEnergy (M N : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑I : idealRange M, ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2
end
open ActualEisensteinCubic CompletedGauss
end
section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open IdealCoprimeSieveOperator DivisorBlockCauchy
end
section
def cutoffRescaleCoefficient (C η r q : ℝ) : ℝ := C*r*q^2/(r/q)^η
end
open scoped BigOperators Classical
def largeGcdThreshold (α N : ℝ) : ℝ := N^(1-1/α)
end CanonicalQuadraticSieve
end
end OAI


