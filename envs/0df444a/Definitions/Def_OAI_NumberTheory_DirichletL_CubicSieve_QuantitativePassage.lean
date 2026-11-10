-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_QuantitativePassage
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_QuantitativePassage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:54:25.662917+00:00
-- url     : https://prove2.me/theorems/659042e5-da60-4e36-beba-3efc0237718b
-- title:
--   Quantitative Passage
-- statement:
--   Definitions and structural lemmas for Quantitative Passage, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/QuantitativePassage.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
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
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
end
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def canonicalCubeFirstBlock (pool : Finset ι) (b : GlobalCubeBlock ι)
    (s : Finset (Ideal O × O)) (a : Ideal O × O → ℂ)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ W V₁ V₂ : 𝓢(ℝ,ℂ)) (K ell : ℝ) : ℂ :=
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) b.common
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor
  let X₁ := globalCubeColumnScale p ell true b
  let X₂ := globalCubeColumnScale p ell false b
  (primeProductNorm p b.firstDivisor : ℂ)⁻¹ * ∑ x∈s,a x*actualFirstKernel p hp hcop hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit true
      (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit false
      (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    W V₁ V₂ X₁ X₂ K d x.2
end
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
end SecondPassArithmetic
open scoped BigOperators Classical
namespace CompletedGauss
section
open ActualEisensteinCubic IdealMobiusDivisorSum UniqueFactorizationMonoid
end
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum
end CompletedGauss
open scoped BigOperators
namespace CompletedDyadic
def kernelTerm (t s A : ℝ) (n : ℕ) : ℝ := ((2:ℝ)^n)^s/(1+t*(2:ℝ)^n)^A
end CompletedDyadic
end
end OAI


