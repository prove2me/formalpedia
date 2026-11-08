-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrimePools
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_PrimePools
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:22:35.615195+00:00
-- url     : https://prove2.me/theorems/bfb01beb-0657-4294-9403-b396874b69eb
-- title:
--   Prime Pools
-- statement:
--   Definitions and structural lemmas for Prime Pools, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/PrimePools.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GcdReduction
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowMajorants
import Theorems.Thm_OAI_CompletedGauss_primaryPrime_ne_zero

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
open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
instance canonicalPoolMaximal (F : Finset (Ideal O)) (i : primePool F) : i.val.IsMaximal := by
  obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
theorem poolGood (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    lambda ∉ i.val := by
  obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
  exact ((hF I hIF).2.2 i.val hi).1
def poolPrimary (F : Finset (Ideal O)) (i : primePool F) : O := primaryPrime i.val
theorem poolPrimary_ne_zero (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (i : primePool F) : poolPrimary F i ≠ 0 := primaryPrime_ne_zero i.val (poolGood F hF i)
theorem poolPrimary_span (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (i : primePool F) : Ideal.span {poolPrimary F i} = i.val :=
  (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.1
theorem poolPrimary_good (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    lambda ∉ Ideal.span {poolPrimary F i} := by rw [poolPrimary_span F hF i]; exact poolGood F hF i
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
end
section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport
end
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
end CanonicalQuadraticSieve
open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog primeProductNorm normalizedColumn)
open EisensteinSchwartzPoisson (paperRadialFourier)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def radialPairKernel (e k : O) (W : 𝓢(ℝ, ℂ))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) (S T : Finset ι) : ℂ :=
  star (normalizedColumn p (fun U => V₁ (columnLog p X₁ U)) S) *
    normalizedColumn p (fun U => V₂ (columnLog p X₂ U)) T *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p S * primeProductNorm p T))
end SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
def elementNorm (a : O) : ℝ := ‖eisEmbedding a‖ ^ 2
def conjugateProfile (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap g
end SecondPassIntegration
open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
def secondPairRadialMode (S T : Finset ι) (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  let n := ∏ i : activeSupport T S, p i.val
  ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
    activeGaussRowFactor p hp hinj hg T S e k
def residualSecondMode (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
    if Disjoint S T then
      star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
      secondPairRadialMode p hp hg hinj S T e k W Y
    else 0
end
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open FirstPassCubeLabels (primeProductNorm)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
def secondFrequencyKernel (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    ((Y : ℂ) / (‖eisEmbedding (∏ i ∈ S ∪ T, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p (S ∪ T))) *
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ S T
  else 0
def secondOverlapBlock (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset, if Disjoint S T then
    overlapPairWeight p hg Ψ m c d H G S T * maskedSecondDual p hg hp hinj G S T W Y
  else 0
end SecondPassArithmetic
end
end OAI


