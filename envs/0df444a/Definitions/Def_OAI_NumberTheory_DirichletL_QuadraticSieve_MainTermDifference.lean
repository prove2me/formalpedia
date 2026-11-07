-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MainTermDifference
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_MainTermDifference
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:34:55.453586+00:00
-- url     : https://prove2.me/theorems/1470aacd-e4ef-4ada-a13a-b0f909705bbd
-- title:
--   Main Term Difference
-- statement:
--   Definitions and structural lemmas for Main Term Difference, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/MainTermDifference.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeLabels
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
namespace QuadraticMainTermDifference
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic QuadraticDivisorCancellation QuadraticMainBoundary
def normCutoff {κ : Type*} (q : κ → O) (K : ℝ) (A : Finset κ) : ℂ :=
  if (Ideal.absNorm (∏ i ∈ A, Ideal.span {q i}) : ℝ) ≤ K then 1 else 0
def partialSquarefreeSum {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) (K : ℝ) (V : Finset κ) : ℂ :=
  ∑ A ∈ V.powerset, normalizedRow P hg S (∏ i ∈ A, q i) * normCutoff q K A
def divisorSum {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) (G : Finset κ) : ℂ :=
  ∑ E ∈ G.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
    normalizedRow P hg S (∏ i ∈ E, q i)
end QuadraticMainTermDifference
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel
def realBeta (a b : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, x ^ (a - 1) * (1 - x) ^ (b - 1)
end CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel
def mellinLogFamily (V : ℝ → ℂ) (σ u : ℝ) : ℂ :=
  Real.exp (-σ * u) • V (Real.exp (-u))
end CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel
def mellinData (V : ℝ → ℂ) (s : ℂ) : ℂ := mellin V (-s) * gammaMultiplier s
def mellinEulerData (V : ℝ → ℂ) (j : ℕ) (s : ℂ) : ℂ := (-s) ^ j * mellinData V s
end CubicReflectionKernel
end
end OAI


