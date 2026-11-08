-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_FrequencyTwists
-- name    : OAI_NumberTheory_DirichletL_Fourier_FrequencyTwists
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:19:07.814452+00:00
-- url     : https://prove2.me/theorems/d6dd2953-2dce-4b4a-b2d9-c6abbb087333
-- title:
--   Frequency Twists
-- statement:
--   Definitions and structural lemmas for Frequency Twists, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Fourier/FrequencyTwists.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SecondPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_PrincipalTruncation
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
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
namespace JointLogSeparation
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge
def frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (logPhase t) g
def phaseDerivative (t : ℝ) : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
def derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (SchwartzMap.seminorm ℝ k i) g
def twistSourceBound (g : 𝓢(ℝ, ℂ)) (K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (K + 1),
    ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i))
end JointLogSeparation
section
open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
namespace JointLogSeparation
open FourierBridge
end JointLogSeparation
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog firstLogDensity)
open JointLogSeparation (outerWindow fixedColumnTest)
open FourierBridge (logPhase)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def postCommonSmoothPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ R : ℝ) : ℂ :=
  ∑ N ∈ F.powerset, ∑ M ∈ F.powerset,
    star (secondChildColumn p hp hcop hg Ψ₁ m f y₁ (fun _ => 1) N) *
      secondChildColumn p hp hcop hg Ψ₂ m f y₂ (fun _ => 1) M *
      (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
        A₁ (z + columnLog p X₁ N) * A₂ (z + columnLog p X₂ M) *
        EisensteinSchwartzPoisson.paperRadialFourier W
          (R * Real.exp (kap - ud - 2 * ue - 2 * uv - columnLog p X₁ N - columnLog p X₂ M)))
def fixedSecondTest (V : ℝ → ℂ) (X t s : ℝ) (negative : Bool) (N : Finset ι) : ℂ :=
  if negative then star (fixedColumnTest V (t-s) (columnLog p X N))
  else fixedColumnTest V (t-s) (columnLog p X N)
def separatedPostCommon (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ b : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ : ℝ) : ℂ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
    (outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
      logPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
    star (fixedChildRow p hp hcop hg F Ψ₁ m
      (fixedSecondTest p (V 5) X₁ t₁ t₃ true) f y₁) *
    fixedChildRow p hp hcop hg F Ψ₂ m
      (fixedSecondTest p (V 6) X₂ t₂ t₃ false) f y₂
end SecondPassArithmetic
end
open scoped BigOperators Classical
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance _p2m_local_instance_8ea36ba204_523 : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
end
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
open RayFourExpansion (RayCharacter gCoeff crossCoeff)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
end
end SecondPassArithmetic
end
end OAI


