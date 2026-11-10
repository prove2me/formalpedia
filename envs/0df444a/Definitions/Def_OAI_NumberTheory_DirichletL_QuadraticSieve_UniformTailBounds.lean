-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_UniformTailBounds
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_UniformTailBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T08:21:42.390804+00:00
-- url     : https://prove2.me/theorems/bfc3e0ad-15ad-4210-9fa5-af67997870eb
-- title:
--   Uniform Tail Bounds
-- statement:
--   Definitions and structural lemmas for Uniform Tail Bounds, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/UniformTailBounds.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply


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
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
end CanonicalQuadraticSieve
open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)
end SecondPassArithmetic
open scoped BigOperators Classical
namespace InitialMeanSquare
open IdealMobiusDivisorSum
structure ElementDatum where
  divisor : Ideal O
  shared : O
  frequency : O
  deriving DecidableEq
def elementRow (gen : Ideal O→O) (x : ElementDatum) : O := gen x.divisor*x.frequency
def elementLabel (gen : Ideal O→O) (x : ElementDatum) : O := gen x.divisor*x.shared
def elementObservation (gen : Ideal O→O) (x : ElementDatum) : O×O := (elementRow gen x,elementLabel gen x)
end InitialMeanSquare
open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn)
open EisensteinSchwartzPoisson (paperRadialFourier)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def globalFirstDiagonalCost (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℝ :=
  ∑ b∈s,‖w b‖*(primeProductNorm p b.firstCommon)⁻¹*
    (|Y b| *‖paperRadialFourier W 0‖*
      ∑ G∈(globalFirstRawPool pool b).powerset,
        ‖secondInputCoefficient p hg Ψ (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
          (globalFirstBlockTest p g ell side b) G‖^2)
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
def globalFirstTailCost (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (K ell B F M H : ℝ) (N : ℕ) (side : Bool) : ℝ :=
  ∑ b∈s,
    let lengthScale := 1+globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon*Real.exp M
    let Y := globalFirstPooledRow p K ell B F side b
    ‖w b‖*(primeProductNorm p b.firstCommon)⁻¹*lengthScale^4*Y*(1+lengthScale^3/Y)^2/(1+H)^N
end
end SecondPassArithmetic
end
end OAI


