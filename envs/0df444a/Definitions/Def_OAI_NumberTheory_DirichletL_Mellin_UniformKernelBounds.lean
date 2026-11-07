-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
-- name    : OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:07:54.740062+00:00
-- url     : https://prove2.me/theorems/70dd8a0e-d2f1-4a3c-a637-9e7e0c6e0f69
-- title:
--   Uniform Kernel Bounds
-- statement:
--   Definitions and structural lemmas for Uniform Kernel Bounds, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/UniformKernelBounds.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_InverseContour
import Theorems.Thm_OAI_FiniteGaussPhase_canonicalProductGauss_cross_factors

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
namespace CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
def negativeLogPullbackCLM (a b : ℝ) : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv).comp (logPullbackCLM a b)
def logWeight (a b σ u : ℝ) : ℂ := (Real.exp (-σ * u) * logCutoff a b (-u) : ℝ)
end CubicReflectionKernel
open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss canonicalProductGauss_cross_factors)
open MixedGaussConversion (localGauss)
def gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) : ℂ :=
  ∏ i ∈ S, (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) *
    localGauss (p i) (hp i) (hg i) (e i)
def blockCross {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (e : ι → ℕ) : ℂ :=
  ∏ i ∈ S, ∏ k ∈ T,
    crossSymbol p hg i k ^ e i * crossSymbol p hg k i ^ e k
def cubeActiveSupport {ι : Type*} (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0)
def blockCubeExponent {ι : Type*} [DecidableEq ι] (U : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) (i : ι) : ℕ :=
  if i ∈ U then (if side then 5 else 1)
  else (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val
end FirstPassCubeLabels
end
end OAI


