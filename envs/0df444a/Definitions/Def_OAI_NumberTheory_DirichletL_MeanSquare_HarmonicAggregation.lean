-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HarmonicAggregation
-- name    : OAI_NumberTheory_DirichletL_MeanSquare_HarmonicAggregation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:18:14.899916+00:00
-- url     : https://prove2.me/theorems/63a87972-ffa3-42e3-aafb-9591e2c206da
-- title:
--   Harmonic Aggregation
-- statement:
--   Definitions and structural lemmas for Harmonic Aggregation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/HarmonicAggregation.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RadialWindows
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
def initialRayMass : ℝ := ∑ ray : SecondRayIndex,‖secondRayCoefficient ray‖
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
end InitialMeanSquare
open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
section
open ActualEisensteinCubic FirstPassCubeLabels
open ConcretePrimeRowBridge (idealGenerator)
variable {ι:Type*} [DecidableEq ι]
  (p:ι→OAI.SecondPassArithmetic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})
def sourceGlobalBlock (b:CubeCoordinates ι) (C D:Finset ι) : GlobalCubeBlock ι :=
  ⟨b.swap,C,D⟩
def commonProductUnit (C:Finset ι) : Oˣ :=
  Classical.choose (exists_label_unit (∏i∈C,p i) (∏i∈C,Ideal.span {p i})
    (FiniteGaussPhase.span_finset_prod C p))
def commonCubePhase (b:CubeCoordinates ι) (C:Finset ι) : ℂ :=
  blockRow p hg (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
    (fun i=>(conductorExponent (parity (b.leftExponent i+b.rightExponent i)) (b.leftBit i) (b.rightBit i)).val)
    ((commonProductUnit p C:O)^2)
end
section
open ActualEisensteinCubic FirstPassCubeLabels
open ConcretePrimeRowBridge (idealGenerator)
open ConcreteTraceCRT (eisEmbedding)
variable {ι:Type*} [DecidableEq ι]
  (p:ι→OAI.SecondPassArithmetic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})
def rawCanonicalBlock (pool:Finset ι) (b:GlobalCubeBlock ι)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (K ell:ℝ) : ℂ :=
  let q:=b.cube.swap
  ∑x∈s,a x*((UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)/
    (primeProductNorm p b.firstDivisor:ℂ))*
    actualFirstKernel p hp hcop hg (pool\(q.support∪b.common)) q.support
      (fun i=>q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit
      (canonicalCubeResidual p hg q b.common true Ψ₁ m₁ (idealGenerator x.1)
        (fun U=>g₁ (columnLog p ell U)))
      (canonicalCubeResidual p hg q b.common false Ψ₂ m₂ (idealGenerator x.1)
        (fun U=>g₂ (columnLog p ell U)))
      W (fun _=>1) (fun _=>1) 1 1 K
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) b.firstDivisor) x.2
def sourceFrequencyEquiv (C:Finset ι) : (Ideal O×O)≃(Ideal O×O) :=
  Equiv.prodCongr (Equiv.refl _) (unitSquareRowEquiv (commonProductUnit p C))
def sourceRotatedCoefficient (b:GlobalCubeBlock ι) (a:Ideal O×O→ℂ) (x:Ideal O×O) : ℂ :=
  (UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)*
    commonCubePhase p hg b.cube.swap b.common*a ((sourceFrequencyEquiv p b.common).symm x)
end
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)
end SecondPassArithmetic
end
end OAI


