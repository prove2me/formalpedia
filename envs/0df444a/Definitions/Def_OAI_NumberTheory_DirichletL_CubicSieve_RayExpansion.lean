-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayExpansion
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_RayExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:16:39.901683+00:00
-- url     : https://prove2.me/theorems/2ef1d72e-b6a2-4789-b442-c7172af60b71
-- title:
--   Ray Expansion
-- statement:
--   Definitions and structural lemmas for Ray Expansion, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/RayExpansion.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Theorems.Thm_OAI_FourierBridge_logPhase_continuous_left
import Theorems.Thm_OAI_FourierBridge_logPhase_norm

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
namespace FirstPassCubeLabels
section
open ActualEisensteinCubic
open MixedCrossSeparation (quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport firstPassColumnMinus firstPassColumnPlus)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)
def fixedRayExpansion {ι : Type*} (p : ι → O) (F S : Finset ι) : ℂ :=
  ∑ χ : RayCharacter, ∑ η : RayCharacter,
    crossCoeff χ η * supportRay p χ S * supportRay p η F
def cubeMinusCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  star (fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
    firstPassColumnMinus p hp hcop hg C (d * crtLabel p B v ε₁ ε₂ true) S
def cubePlusCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S *
    firstPassColumnPlus p hp hcop hg C (d * crtLabel p B v ε₁ ε₂ false) S
def idealPairReindex {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (R : Finset ι)
    (C₁ C₂ : Finset ι → ℂ) (h : O) : ℂ :=
  let P := fun i => Ideal.span {p i}
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ R.powerset,
      (supportMobius P D * rowCoprimeMask P D h * supportRay p r.1 D * supportRay p r.2 D) *
      star (conjugateIdealRowSum (supportIdealFamily P (R \ D))
        (supportIdealFamily_pos P (R \ D)) (supportIdealFamily_good P hg (R \ D))
        (fun I => star (supportRay p r.1 (recoveredSupport P (R \ D) I)) *
          C₁ (D ∪ recoveredSupport P (R \ D) I)) h) *
      conjugateIdealRowSum (supportIdealFamily P (R \ D))
        (supportIdealFamily_pos P (R \ D)) (supportIdealFamily_good P hg (R \ D))
        (fun I => supportRay p r.2 (recoveredSupport P (R \ D) I) *
          C₂ (D ∪ recoveredSupport P (R \ D) I)) h
end
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
section
open ActualEisensteinCubic
open FourierBridge (logPhase logPhase_norm logPhase_continuous_left)
open EisensteinSchwartzPoisson (paperRadialFourier)
def logTwistMinus {ι : Type*} (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * star (V (y S) * logPhase t (-(y S)))
def logTwistPlus {ι : Type*} (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * (V (y S) * logPhase t (-(y S)))
end
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
def primeProductNorm {ι : Type*} (p : ι → O) (S : Finset ι) : ℝ :=
  ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2
def columnLog {ι : Type*} (p : ι → O) (X : ℝ) (S : Finset ι) : ℝ :=
  Real.log (primeProductNorm p S / X)
def firstDualScale {ι : Type*} (p : ι → O) (C : Finset ι)
    (lengthScale X₁ X₂ : ℝ) (d h : O) : ℝ :=
  lengthScale * ‖eisEmbedding h‖ ^ 2 /
    (‖eisEmbedding d‖ ^ 2 * primeProductNorm p C * X₁ * X₂)
def normalizedColumn {ι : Type*} (p : ι → O) (C : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  C S / (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)
end FirstPassCubeLabels
open scoped BigOperators Classical
namespace QuadraticDivisorSplit
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum
end QuadraticDivisorSplit
end
end OAI


