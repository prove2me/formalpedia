-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T07:21:07.956338+00:00
-- url     : https://prove2.me/theorems/51b73373-c5ec-4d8d-b285-cd70573cb934
-- title:
--   Pooled Rows
-- statement:
--   Definitions and structural lemmas for Pooled Rows, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/PooledRows.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
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
open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
def GlobalFirstAdmissible (b : GlobalFirstData ι) : Prop :=
  b.cube.Admissible ∧ Disjoint b.common b.cube.support ∧ b.firstDivisor ⊆ b.common∪b.cube.support
variable (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
def globalFirstIndex (side : Bool) (b : GlobalFirstData ι) : GlobalLogIndex :=
  globalScaleIndex p side (b.append ⟨∅,∅,∅,1⟩)
def globalFirstPooledRow (K ell B F : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  globalPooledRowScale K ell B F (globalFirstIndex p side b)
def globalFirstCoefficient (K ell B F : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  globalBinFirstCoefficient K ell B F (globalFirstIndex p side b)
def globalFirstConcreteCutoff (K ell B F M H : ℝ) (side : Bool) (b : GlobalFirstData ι) :
    Finset ι → Finset ι → Finset O :=
  firstCoreSecondCutoff p b.firstCommon (globalFirstBlockColumnScale p ell side b)
    (globalFirstPooledRow p K ell B F side b) M H
def globalFirstSupportedPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) : Finset (GlobalSecondData ι) :=
  (globalFirstExpansionPool pool s cutoff).filter (fun x =>
    SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
end
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
end
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (densityChildEnergy)
open JointLogSeparation (frequencyTwist)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def globalChildBudget (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε θ₁ θ₂ K ell B F M H : ℝ) (A J : ℕ) (side : Bool) : ℝ :=
  ∑ j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
    ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p source side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q *
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
        (globalPooledColumnScale ell j*globalPooledLabelScale j))
end
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
end SecondPassArithmetic
open scoped BigOperators Classical
namespace InitialMeanSquare
section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O
structure Datum where
  divisor : Ideal O
  shared : Ideal O
  frequency : O
  deriving DecidableEq
def newRow (x : Datum) : O := idealGenerator x.divisor*x.frequency
def newLabel (x : Datum) : Ideal O := x.divisor*x.shared
def oldCommon (b : Ideal O) (x : Datum) : Ideal O := b*x.divisor
def observation (x : Datum) : O × Ideal O := (newRow x,newLabel x)
end
def columnScale (Z B F : ℝ) : ℝ := Z/(B*F)
def rowScale (Z H B : ℝ) : ℝ := Z^2/(H*B^2)
end InitialMeanSquare
end
end OAI


