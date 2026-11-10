-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
-- name    : OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T08:50:26.17551+00:00
-- url     : https://prove2.me/theorems/79e9662c-a19d-482c-9057-365a8e6c61a4
-- title:
--   Powerful Parts
-- statement:
--   Definitions and structural lemmas for Powerful Parts, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/PowerfulParts.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SquarefreeTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
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
namespace CompletedGauss
section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel UniqueFactorizationMonoid
def rowPowerfulPart (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => 2≤(normalizedFactors I).count P)).prod
def rowSimplePart (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => ¬2≤(normalizedFactors I).count P)).prod
end
open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid
def squarefreeMaskPart (I R : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P∣R)).prod
def squarefreeResidualPart (I R : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => ¬P∣R)).prod
def rowMaskPart (I R : Ideal O) : Ideal O := squarefreeMaskPart (rowSimplePart I) R
def rowResidualPart (I R : Ideal O) : Ideal O := squarefreeResidualPart (rowSimplePart I) R
end CompletedGauss
namespace SecondPassArithmetic
section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff gCoeff)
def firstCoreUniformWeight (r : FirstCoreIndex) : ℝ := ‖crossCoeff r.1 r.2.1‖*‖gCoeff r.2.2‖
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def GlobalCubeAdmissible (b : GlobalCubeBlock ι) : Prop :=
  b.cube.Admissible ∧ Disjoint b.common b.cube.support ∧ b.firstDivisor⊆b.common∪b.cube.support
end
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def globalFirstFamilyBudget (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
    (w : GlobalCubeBlock ι → ℝ) (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ))
    (windows : Fin 7 → ℝ → ℂ) (C Ct Γ ε K ell B F M H : ℝ) (A J N : ℕ) (side : Bool) : ℝ :=
  let family := globalFirstFamilySet pool blocks
  let source := globalFirstSupportedPool p pool family
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
  ∑ a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑ r : FirstCoreIndex,
    let Ψmode := firstCoreTwist side (if side then a.1 else a.2) Ψ r
    let weight := fun d => globalFirstFamilyWeight p hg w Ψ m side r d*globalFirstCoefficient p K ell B F side d
    (∫ t : ℝ,firstLogDensity 0 t)*
      (globalFirstDiagonalCost p hg pool family (fun d => weight d) Ψmode m
          (firstCoreBaseProfile g V side) rowMajorant ell side (globalFirstPooledRow p K ell B F side) +
        globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*firstCoreUniformWeight r*C) ε 0 0 K ell B F M H A J side +
        Ct*globalFirstTailCost p family (fun d => weight d) K ell B F M H N side)
end
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
def globalCubeFirstBlock (pool : Finset ι) (b : GlobalCubeBlock ι)
    (s : Finset (Ideal O × O)) (a : Ideal O × O → ℂ)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ W V₁ V₂ : 𝓢(ℝ,ℂ)) (K ell : ℝ) : ℂ :=
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) b.common
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor
  let X₁ := globalCubeColumnScale p ell true b
  let X₂ := globalCubeColumnScale p ell false b
  ∑ x∈s,a x*actualFirstKernel p hp hcop hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit true
      (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit false
      (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    W V₁ V₂ X₁ X₂ (K/primeProductNorm p b.firstDivisor) d x.2
end
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
end SecondPassArithmetic
end
end OAI


