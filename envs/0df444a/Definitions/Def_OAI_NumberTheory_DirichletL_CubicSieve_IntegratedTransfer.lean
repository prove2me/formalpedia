-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_IntegratedTransfer
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_IntegratedTransfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:56:55.365736+00:00
-- url     : https://prove2.me/theorems/221a381d-3ce2-4418-9696-ad3632a64743
-- title:
--   Integrated Transfer
-- statement:
--   Definitions and structural lemmas for Integrated Transfer, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/IntegratedTransfer.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ChildTransfer
import Theorems.Thm_OAI_PrimaryIdealUnitReindex_finite_units

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
namespace SecondPassArithmetic
section
open scoped BigOperators Classical
open MeasureTheory
section
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeOddSupport coreRayCoefficient coreRayTwist dilatedCoreRow
  b0Label jLabel firstLogDensity columnLog normalizedColumn firstOutputEnergy)
open FirstCauchyArithmetic (supportMobius supportConjugateSum)
open RayFourExpansion (RayCharacter crossCoeff)
open FourierBridge (logPhase)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def firstCoreInputRow (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (z : O) : ℂ :=
  inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
    (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (firstCoreTest H V y negative t D) (if negative then -z else z)
end
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeOddSupport coreRayCoefficient dilatedCoreRow b0Label jLabel
  firstLogDensity columnLog normalizedColumn firstOutputEnergy)
open RayFourExpansion (RayCharacter crossCoeff)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def firstInputFamilyEnergy (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) : ℝ :=
  ∑ a : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖crossCoeff a.1 a.2‖ * ∑ r : FirstCoreIndex,
      ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
        ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
          ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative
            (if negative then a.1 else a.2) Ψ m (normalizedColumn p H)
            V (columnLog p X) c d r t z‖ ^ 2
end
open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label jLabel)
open RayFourExpansion (RayCharacter)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
end SecondPassArithmetic
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace JointLogSeparation
abbrev Frequency := ℝ × ℝ × ℝ
def tripleCoefficient (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (t : Frequency) : ℂ :=
  b₁ t.1 * (b₂ t.2.1 * b₃ t.2.2)
end JointLogSeparation
namespace SecondPassIntegration
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open FirstPassCubeLabels (columnLog)
local instance _p2m_local_instance_da3c5b0272_513 : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassIntegration.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def rowMagnitude (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X : ℝ)
    (negative : Bool) : ℝ :=
  ∑ N ∈ F.powerset,
    ‖secondChildColumn p hp hcop hg Ψ m f y (fixedSecondTest p V X 0 0 negative) N‖
def childEnergy (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) : ℝ :=
  ∑ u : Oˣ, ∑ z ∈ T,
    ‖idealChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b testNegative) rowNegative u z‖ ^ 2
def energyMagnitude (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) : ℝ :=
  ∑ u : Oˣ, ∑ z ∈ T,
    (rowMagnitude p hp hcop hg F Ψ m ((u : O) * ConcretePrimeRowBridge.idealGenerator z.1)
      (if rowNegative then -z.2 else z.2) V X testNegative) ^ 2
end SecondPassIntegration
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance _p2m_local_instance_da3c5b0272_611 : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassIntegration.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def integratedSecondMode (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (s : Finset OldTuple) (w : Frequency → OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) *
    fixedSecondMode p hp hcop hg s (w (t₁,t₂,t₃)) label F Ψ₁ Ψ₂ m
      (fixedSecondTest p V₁ X₁ t₁ t₃ true) (fixedSecondTest p V₂ X₂ t₂ t₃ false)
def childGeometricMean (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (q : Frequency) : ℝ :=
  Real.sqrt (childEnergy p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2) *
    Real.sqrt (childEnergy p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2)
end SecondPassIntegration
end
end OAI


