-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RankMargins
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_RankMargins
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T11:47:37.388695+00:00
-- url     : https://prove2.me/theorems/83618cfb-5e23-4caf-8d52-40e75910f422
-- title:
--   Rank Margins
-- statement:
--   Definitions and structural lemmas for Rank Margins, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/RankMargins.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_PolynomialHeight
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DensityBudgets
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
namespace SecondPassArithmetic
def canonicalPadding (ε C : ℝ) : ℝ :=
  min ((1:ℝ)/120040) (ε/6002)/(1+C)
end SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
end CanonicalRowCompletion
namespace CompletedHeight
section
open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open FourierBridge JointLogSeparation
def fixedLogReturnCLM (a b : ℝ) (ha : 0 < a) : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (positiveCutoff a b ha)).comp
    (SchwartzMap.compCLM ℝ
      (patchedLog_temperate (a/2) (max a b+a/2) (by linarith))
      (patchedLog_proper (a/2) (max a b+a/2) (by linarith)))
def uniformTwistedSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  fixedLogReturnCLM a b ha (frequencyTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) t)
end
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open CompletedGauss
def HasUniformPolynomialKernel {κ : Type*} (P : κ→ℝ→ℝ→ℂ) : Prop :=
  (∀w t,ContDiffOn ℝ ∞ (CubicReflectionKernel.paperKernel (Vstar (P w t))) (Set.Ioi 0)) ∧
  ∀ A K : ℕ,∃n : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀t : ℝ,∀i≤K,∀x : ℝ,0<x →
    (1+x)^A*‖LocalLogFourier.eulerDeriv (CubicReflectionKernel.paperKernel (Vstar (P w t))) i x‖≤
      C*(1+‖t‖)^n
abbrev SupportedSmoothSource (a b : ℝ) :=
  {W : ℝ→ℂ // Function.support W⊆Set.Icc a b ∧ ContDiff ℝ ∞ W}
end CompletedHeight
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedHeight
open CompletedGauss hiding O
open ActualEisensteinCubic
open CanonicalQuadraticSieve hiding O
end CompletedHeight
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedHeight
open CompletedGauss hiding O
open ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve hiding O
end CompletedHeight
end
end OAI


