-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T03:56:58.570042+00:00
-- url     : https://prove2.me/theorems/13a8eccb-3987-4d56-a93c-c40e94b9b9cc
-- title:
--   Poisson Comparison
-- statement:
--   Definitions and structural lemmas for Poisson Comparison, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
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
namespace CanonicalQuadraticSieve
section
def bootstrapExponent (n : ℕ) : ℝ := 1+1/((n:ℝ)+1)
section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
def divisorTwist {n : Type} (cols : n → Ideal O) (a : n → ℂ) (q : Ideal O) : n → ℂ :=
  fun j => a j*quadraticRow (cols j) (idealGenerator q)
def centeredRetainedDual {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) (q : Ideal O) : ℂ :=
  (6:ℂ)*retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
    (fun I : squarefreeIdealRange K => I.val) cols (divisorTwist cols a q) M (Ideal.absNorm q:ℝ) -
  paperRadialFourier (quadraticTransformedSquareProfile W) 0 *
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
      (divisorTwist cols a q) (divisorTwist cols a q) (M/(Ideal.absNorm q:ℝ))
def centeredMaskedSource {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedPrincipalSourceSum G (quadraticSquareProfile W)
    (fun I : coprimeSquarefreeRange G K => I.val) cols a M -
  paperRadialFourier (quadraticSquareProfile W) 0 *
    maskedSourceDensity G (fun I : coprimeSquarefreeRange G K => I.val) cols a M
def maskedPoissonDifference {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedDualFamily G cols a W M - (6:ℂ)⁻¹ *
    maskedPrincipalSourceSum G (quadraticSquareProfile W)
      (fun I : coprimeSquarefreeRange G K => I.val) cols a M
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator
end
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator
def poissonComparisonMajorant {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
    retainedDualMajorant sD CD l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) +
  6*(256*M*(idealDivisors G).card*
    ((CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
        (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A))*∑j, ‖a j‖^2) +
  (columnDyadicLength K+1:ℕ)*
    sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε G (2*K) N M T a (quadraticSquareProfile W) +
  ‖paperRadialFourier (quadraticSquareProfile W) 0‖ *
    (((idealDivisors G).card:ℝ)^2*(supportConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
      (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑j, ‖a j‖^2)
end
section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open DivisorBlockCauchy
end
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy
end CanonicalQuadraticSieve
open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def globalSecondOuterWeight (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℂ :=
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let b0 := b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)
  (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    (secondNormalizedExpansionWeight p hp hcop hg Ψ (m*b0) c d z X Y x.source *
      (secondExpansionScale p X r (expansionSupportData x.common x.firstDivisor x.source) : ℂ)⁻¹)
def globalPooledOuterBound (z : SecondRayIndex) (ell Y : ℝ) (j : GlobalLogIndex) : ℝ :=
  (Y*(Real.exp 1)^6*globalLogRep j 2*globalLogRep j 3*(globalLogRep j 0)^2*(globalLogRep j 1)^2/ell^2)*
    ‖secondRayCoefficient z‖
end SecondPassArithmetic
end
end OAI


