-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ChildTransfer
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_ChildTransfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:21:37.513862+00:00
-- url     : https://prove2.me/theorems/ab8173e7-2c5d-4176-9904-dd65b65c7641
-- title:
--   Child Transfer
-- statement:
--   Definitions and structural lemmas for Child Transfer, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/ChildTransfer.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_FrequencyTwists
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
import Theorems.Thm_OAI_PrimaryIdealUnitReindex_finite_units

set_option autoImplicit false
namespace OAI
noncomputable section
namespace SecondPassArithmetic
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
section
open scoped BigOperators Classical
section
open ActualEisensteinCubic
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance _p2m_local_instance_bf590f06ec_82 : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def fixedSecondMode (s : Finset OldTuple) (w : OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ x ∈ s, w x *
    star (fixedChildRow p hp hcop hg F Ψ₁ m H₁ (label x) (newRow x)) *
      fixedChildRow p hp hcop hg F Ψ₂ m H₂ (label x) (-newRow x)
end
section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportConjugateSum)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def inputConjugateRow (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (z : O) : ℂ :=
  supportConjugateSum (fun i => Ideal.span {p i}) hg F
    (secondInputCoefficient p hg Ψ m c d H) z
end
section
open ActualEisensteinCubic
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg
end
section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg
omit hg in

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem poisson_mask_generator_dvd (E G : Finset ι) (hEG : E ⊆ G) :
    primeSubsetGenerator (fun i => Ideal.span {p i}) E ∣ ∏ i ∈ G, p i := by
  have hs : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) E} =
      Ideal.span {∏ i ∈ E, p i} := by
    rw [primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator,
      FiniteGaussPhase.span_finset_prod]
  have ha := Ideal.span_singleton_eq_span_singleton.mp hs
  exact (dvd_dvd_iff_associated.mpr ha).1.trans (Finset.prod_dvd_prod_of_subset E G p hEG)
omit hg in
def secondMaskQuotient (E G : Finset ι) (hEG : E ⊆ G) : O :=
  Classical.choose (poisson_mask_generator_dvd p E G hEG)
end
open ActualEisensteinCubic
end
section
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)
open EisensteinSchwartzPoisson (paperRadialFourier)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def maskedSecondSource (G U V : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) G z *
    (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z) * W (‖eisEmbedding z‖ ^ 2 / Y)
def overlapPairWeight (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (G U V : Finset ι) : ℂ :=
  (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
    star (supportMobius (fun i => Ideal.span {p i}) U *
      secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) U) *
    (supportMobius (fun i => Ideal.span {p i}) V *
      secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) V)
def maskedSecondDual (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (G U V : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  let n := ∏ i : activeSupport V U, p i.val
  ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ G.powerset,
      let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
        (‖eisEmbedding e‖ ^ 2 : ℝ)) *
        ∑' k : O, paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
          (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
          FirstCauchyArithmetic.activeGaussRowFactor p hp hinj hg V U e k
end
open scoped BigOperators Classical
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeCoreCoefficient cubeOddSupport coreRayCoefficient coreRayTwist
  coreRayCharacter dilatedCoreRow dilatedRayColumn afterDilationLabel b0Label jLabel)
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)
open FourierBridge (logPhase)
abbrev FirstCoreIndex := RayCharacter × (RayCharacter × RayCharacter)
def sideRayMonoid (negative : Bool) (χ : RayCharacter) : O →* ℂ :=
  if negative then conjugateRayMonoid χ else rayMonoid χ
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def multiplicativeCoreColumn (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏ i ∈ S, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) S m * H S
def firstCoreTest (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (t : ℝ) (D U : Finset ι) : ℂ :=
  H (D ∪ U) *
    (if negative then star (V (y (D ∪ U)) * logPhase t (-(y (D ∪ U))))
      else V (y (D ∪ U)) * logPhase t (-(y (D ∪ U))))
def firstCoreOuter (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (D : Finset ι) (r : FirstCoreIndex) : ℂ :=
  coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2 *
    (Ψ * coreRayTwist negative r.1 r.2.2) (∏ i ∈ D, p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) D m *
    (if negative then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg D (-1)) else 1)
def firstCoreTwist (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ)
    (r : FirstCoreIndex) : O →* ℂ :=
  sideRayMonoid negative χ * (Ψ * coreRayTwist negative r.1 r.2.2)
end SecondPassArithmetic
end
end OAI


