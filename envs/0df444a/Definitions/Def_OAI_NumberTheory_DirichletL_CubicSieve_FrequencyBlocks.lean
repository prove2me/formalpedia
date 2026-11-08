-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FrequencyBlocks
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_FrequencyBlocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:28:42.901115+00:00
-- url     : https://prove2.me/theorems/908bf210-bfea-4516-945d-39b19d527951
-- title:
--   Frequency Blocks
-- statement:
--   Definitions and structural lemmas for Frequency Blocks, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/FrequencyBlocks.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrimePools
import Theorems.Thm_OAI_SecondPassIntegration_tupleSource_uniform_transfer

set_option autoImplicit false
namespace OAI
noncomputable section
namespace SecondPassArithmetic
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
open scoped BigOperators Classical SchwartzMap
section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
end
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportConjugateSum supportMobius)
open RayFourExpansion (RayCharacter)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
end
def nonzeroRowMajorantSum (P : O → ℂ) (Y : ℝ) : ℂ :=
  ∑' z : O, if z = 0 then 0 else
    rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
end
section
open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
end
section
open scoped BigOperators Classical
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct cubeRadical aLabel jLabel j2Label squarefreeLabel b0Label
  bit retained parity b0Exponent)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
def actualSecondTuple (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (k : O) : SecondPassFiber.OldTuple where
  core := ![Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂},
    ∏ i ∈ C, Ideal.span {p i}, ∏ i ∈ E, Ideal.span {p i},
    Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)},
    Ideal.span {primeProduct p B v₁}, Ideal.span {aLabel p B ε₁},
    Ideal.span {aLabel p B ε₂}, ∏ i ∈ D, Ideal.span {p i}]
  v := ∏ i ∈ V, Ideal.span {p i}
  j2 := Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}
  b2 := Ideal.span {primeProduct p B v₂}
  row := k
def actualSecondLabel (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Ideal O :=
  Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂} *
    (∏ i ∈ C, Ideal.span {p i}) * (∏ i ∈ E, Ideal.span {p i}) * (∏ i ∈ V, Ideal.span {p i})
def actualSecondRow (D E : Finset ι) (k : O) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) D *
    primeSubsetGenerator (fun i => Ideal.span {p i}) E * k
end
open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel b0Label primeProductNorm)
@[ext] structure SecondSupportData (ι : Type*) where
  common : Finset ι
  firstDivisor : Finset ι
  secondDivisor : Finset ι
  overlap : Finset ι
  frequency : O
  deriving DecidableEq
instance {ι : Type*} : Inhabited (SecondSupportData ι) := ⟨⟨∅, ∅, ∅, ∅, 0⟩⟩
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
def secondSupportTuple (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondSupportData ι) : SecondPassFiber.OldTuple :=
  actualSecondTuple p B x.common x.firstDivisor x.secondDivisor x.overlap v₁ v₂ ε₁ ε₂ x.frequency
def secondSupportLabel (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondSupportData ι) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
    jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂ *
    primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor * (∏ i ∈ x.overlap, p i)
def secondSupportNewLabel (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondSupportData ι) : Ideal O :=
  actualSecondLabel p B x.common x.secondDivisor x.overlap v₁ v₂ ε₁ ε₂
def secondSupportRow (x : SecondSupportData ι) : O :=
  actualSecondRow p x.firstDivisor x.secondDivisor x.frequency
def secondSectorZ (X X₀ : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap * X₀ / X)
def secondSectorUd (D : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (‖ConcreteTraceCRT.eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)‖ ^ 2 / D)
def secondSectorUe (E : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (‖ConcreteTraceCRT.eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)‖ ^ 2 / E)
def secondSectorUv (V₀ : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap / V₀)
def secondSectorKap (K : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (‖ConcreteTraceCRT.eisEmbedding (secondSupportRow p x)‖ ^ 2 / K)
end
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open SecondPassIntegration (tupleSourceSum tupleSource_uniform_transfer childGeometricMean)
open JointLogSeparation
open FirstPassCubeLabels (b0Label)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def actualSecondSectorSource
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ)
    (D₀ E₀ V₀ X X₀ K Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m
    (secondSupportLabel p B v₁ v₂ ε₁ ε₂ x) (secondSupportRow p x) (-secondSupportRow p x)
    A₁ A₂ W windows (secondSectorZ p X X₀ x) (secondSectorUd p D₀ x)
    (secondSectorUe p E₀ x) (secondSectorUv p V₀ x) (secondSectorKap p K x)
    X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2))
end SecondPassArithmetic
end
end OAI


