-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:10:40.27521+00:00
-- url     : https://prove2.me/theorems/f898284c-a1e6-4cfa-ae90-35b145709793
-- title:
--   Cross Factorization
-- statement:
--   Definitions and structural lemmas for Cross Factorization, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/CrossFactorization.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Theorems.Thm_OAI_SquarefreeDivisorBound_prime_support_subsets_bound

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
open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss)
def threeBlockExponent {ι : Type*} [DecidableEq ι] (N P : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (i : ι) : ℕ :=
  if i ∈ N then 5 else if i ∈ P then 1
  else (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val
end FirstPassCubeLabels
namespace QuadraticGaussRay
open EisensteinEPrimaryPhase ActualEisensteinCoordinates ActualEisensteinCubic
end QuadraticGaussRay
namespace QuadraticMainBoundaryFibers
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum QuadraticMainBoundary
def productIdeal (x : Ideal O × Ideal O × Ideal O) : Ideal O := x.1 * x.2.1 * x.2.2
def boundaryCoefficient (K : ℝ) (s : Finset (Ideal O × Ideal O × Ideal O))
    (B : Ideal O) : ℂ :=
  ∑ x ∈ s.filter (fun x => productIdeal x = B),
    (UniqueFactorizationMonoid.moebius x.2.2 : ℂ) * (cutoffDifference K x.1 x.2.1 : ℝ)
end QuadraticMainBoundaryFibers
namespace CoprimeSieveOperator
open FiniteSieveOperator CoprimeMobiusExtension
end CoprimeSieveOperator
namespace IdealCoprimeSieveOperator
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum CoprimeSieveOperator FiniteSieveOperator
open UniqueFactorizationMonoid
def supportConstant (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (SquarefreeDivisorBound.prime_support_subsets_bound ε hε).choose
open ConcretePrimeRowBridge
end IdealCoprimeSieveOperator
open scoped BigOperators Classical
namespace QuadraticMainOperatorBound
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum QuadraticMainBoundary IdealCoprimeSieveOperator FiniteSieveOperator
def mainWeight (K : ℝ) (H D E : Ideal O) : ℂ :=
  (cutoffDifference K H D : ℂ) / (Real.sqrt (Ideal.absNorm (H * D * E) : ℝ) : ℂ)
open ConcretePrimeRowBridge ActualEisensteinCubic
end QuadraticMainOperatorBound
end
end OAI


