-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:28:08.591198+00:00
-- url     : https://prove2.me/theorems/9bc19381-dbd3-4505-9ad3-d6f876a71fe3
-- title:
--   Initial Bound
-- statement:
--   Definitions and structural lemmas for Initial Bound, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/InitialBound.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
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
open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
def quadraticRow {α : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) : ℂ :=
  (finiteSquarefreeRow P hg S z) ^ 3
def supportNorm {α : Type*} (P : α → Ideal O) (S : Finset α) : ℝ :=
  Ideal.absNorm (∏ i ∈ S, P i)
def diagonalControl (W : 𝓢(ℝ, ℂ)) : ℝ :=
  16 * (1 + Real.pi) ^ 2 *
    (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
def sieveBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num
def sieveCutoff : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (fun t : ℝ => (sieveBump t : ℂ)) :=
    sieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (sieveBump t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp sieveBump.contDiff
  exact hc.toSchwartzMap hs
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge
def initialSieveConstant : ℝ :=
  diagonalControl sieveCutoff + 128 * pvControl sieveCutoff + 1
end QuadraticInitialBound
open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory
namespace CubicReflectionKernel
def gammaMultiplier (s : ℂ) : ℂ :=
  Complex.Gamma ((7 / 6 : ℂ) + s) * Complex.Gamma ((5 / 6 : ℂ) + s) /
    (Complex.Gamma ((7 / 6 : ℂ) - s) * Complex.Gamma ((5 / 6 : ℂ) - s))
def axisMultiplier (u : ℝ) : ℂ := gammaMultiplier ((2 * Real.pi * u : ℝ) * Complex.I)
def spectralProfile (logSource : SchwartzMap ℝ ℂ) (u : ℝ) : ℂ := axisMultiplier u * (𝓕 logSource) u
def reflectedLogProfile (logSource : SchwartzMap ℝ ℂ) : ℝ → ℂ := 𝓕 (spectralProfile logSource)
end CubicReflectionKernel
end
end OAI


