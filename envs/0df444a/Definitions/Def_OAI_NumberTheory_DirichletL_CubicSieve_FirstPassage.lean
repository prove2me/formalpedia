-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstPassage
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_FirstPassage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T05:15:24.005027+00:00
-- url     : https://prove2.me/theorems/df527874-8b9a-4ad6-8cf4-78aae750f2a1
-- title:
--   First Passage
-- statement:
--   Definitions and structural lemmas for First Passage, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/FirstPassage.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
import Theorems.Thm_OAI_ConcretePrimeRowBridge_conjugateIdealRowSum_smoothed_poisson
import Theorems.Thm_OAI_ConcretePrimeRowBridge_conjugateIdealRowSum_smoothed_summable
import Theorems.Thm_OAI_FirstPassCubeLabels_mask_mul
import Theorems.Thm_OAI_FirstPassCubeLabels_mask_union
import Theorems.Thm_OAI_FirstPassCubeLabels_row_union
import Theorems.Thm_OAI_MixedCrossSeparation_columnCoefficient_cancel_false
import Theorems.Thm_OAI_MixedCrossSeparation_columnCoefficient_cancel_true
import Theorems.Thm_OAI_PoissonChildCRT_mask_mul

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
namespace FirstPassCubeLabels
section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)
open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)
def firstOutputEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) : ℝ :=
  ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖crossCoeff r.1 r.2‖ * ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
      ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
        (if negative then r.1 else r.2) (normalizedColumn p C) V (columnLog p X) c d t z‖ ^ 2
end
open ActualEisensteinCubic
open ConcretePrimeRowBridge (conjugateIdealRowSum mobiusIdealColumn idealPairPoissonKernel
  primePool mem_primePool_iff conjugateIdealRowSum_smoothed_summable
  conjugateIdealRowSum_smoothed_poisson)
open FirstCauchyArithmetic (supportIdealFamily supportIdealFamily_pos supportIdealFamily_good
  recoveredSupport supportRay)
open RayFourExpansion (RayCharacter)
open ConcreteTraceCRT (eisEmbedding)
def dilatedIdealCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool) (χ : RayCharacter)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (I : Ideal O) : ℂ :=
  let U := recoveredSupport (fun i => Ideal.span {p i}) (F \ D) I
  (if negative then star (supportRay p χ U) else supportRay p χ U) *
    cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t (D ∪ U) *
    afterDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ c d U
end FirstPassCubeLabels
namespace SecondPassArithmetic
section
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient columnG convertedColumnBlock quadraticCrossPhase
  columnPrimeCoprime columnCoefficient_cancel_false columnCoefficient_cancel_true)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
def secondColumnMinus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (e k : O) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * star (columnG p hp hcop hg S) * C S *
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k
def secondColumnPlus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (e k : O) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
    star (columnG p hp hcop hg S) * C S *
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k
end
section
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels (row_union mask_union mask_mul)
section Masks
variable {ι : Type*} (P : ι → Ideal OAI.SecondPassArithmetic.O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
end Masks
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def secondPreColumn (Ψ : O →* ℂ) (m c d e k : O)
    (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏ i ∈ S, p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d *
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k * H S
def secondChildColumn (Ψ : O →* ℂ) (m f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏ i ∈ S, p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S y * H S
end
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def secondSeparatedPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset,
    if Disjoint S T then
      star (secondPreColumn p hp hcop hg Ψ₁ (m * (e * r)) c d e k₁ H₁ S) *
        secondPreColumn p hp hcop hg Ψ₂ (m * (e * r)) c d e k₂ H₂ T
    else 0
def secondCommonWeight (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O) (V : Finset ι) : ℂ :=
  supportMobius (fun i => Ideal.span {p i}) V *
    star (secondPreColumn p hp hcop hg Ψ₁ (m * (e * r)) c d e k₁ (fun _ => 1) V) *
      secondPreColumn p hp hcop hg Ψ₂ (m * (e * r)) c d e k₂ (fun _ => 1) V
def secondChildSum (F V : Finset ι) (Ψ : O →* ℂ)
    (m r c d e k : O) (H : Finset ι → ℂ) : ℂ :=
  ∑ N ∈ (F \ V).powerset,
    secondChildColumn p hp hcop hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
      (fun U => H (V ∪ U)) N
def secondChildEnergy (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (H : Finset ι → ℂ) (negative : Bool) : ℝ :=
  ∑ V ∈ F.powerset, ‖secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V‖ *
    ‖secondChildSum p hp hcop hg F V (if negative then Ψ₁ else Ψ₂)
      m r c d e (if negative then k₁ else k₂) H‖ ^ 2
end SecondPassArithmetic
end
end OAI


