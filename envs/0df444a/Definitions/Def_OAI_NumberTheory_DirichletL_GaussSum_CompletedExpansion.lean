-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
-- name    : OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:19:16.085469+00:00
-- url     : https://prove2.me/theorems/9131de3b-a72d-4979-9298-56af18951763
-- title:
--   Completed Expansion
-- statement:
--   Definitions and structural lemmas for Completed Expansion, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CompletedExpansion.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span

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
namespace CompletedGauss
open ActualEisensteinCubic
def expandedTerm (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I H J : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) *
    (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm H : ℝ) ^ 3 *
        (Ideal.absNorm J : ℝ) ^ 3 / X))
open ActualEisensteinCubic ConcreteTraceCRT
theorem normalizedFactors_product {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] :
    UniqueFactorizationMonoid.normalizedFactors (Ideal.span {∏ i, p i}) =
      Finset.univ.val.map (fun i => Ideal.span {p i}) := by
  have hp (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have h := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    (m := Finset.univ.val.map (fun i => Ideal.span {p i})) (by
      intro P hP
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hP
      exact hp i)
  rw [FiniteGaussPhase.span_finset_prod]
  exact h
def productPrimeIndexEquiv {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) :
    ι ≃ PrimeIndex (Ideal.span {∏ i, p i}) := by
  have hinj : Function.Injective (fun i => (Ideal.span {p i} : Ideal O)) := by
    intro i j hij
    by_contra hne
    have ht := (hcop hne).sup_eq
    rw [hij, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
  have hmem (i : ι) : (Ideal.span {p i} : Ideal O) ∈ primeSupport (Ideal.span {∏ i, p i}) := by
    rw [primeSupport, normalizedFactors_product]
    exact Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let f : ι → PrimeIndex (Ideal.span {∏ i, p i}) := fun i => ⟨Ideal.span {p i}, hmem i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    exact hinj (congrArg Subtype.val hij)
  · intro P
    have hm := Multiset.mem_toFinset.mp P.property
    rw [normalizedFactors_product] at hm
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hm
    exact ⟨i, Subtype.ext hi⟩
end CompletedGauss
namespace FiniteRayExpansion
variable {R : Type*} [CommRing R] [Fintype R]
noncomputable local instance _p2m_local_instance_47d1e46724_359 : Fintype (MulChar R ℂ) := Fintype.ofFinite _
def unitFourierCoeff (f : Rˣ → ℂ) (χ : MulChar R ℂ) : ℂ :=
  (∑ u : Rˣ, f u * star (χ (u : R))) / (Fintype.card Rˣ : ℂ)
def zeroExtendUnits (f : Rˣ → ℂ) (r : R) : ℂ :=
  if hr : IsUnit r then f hr.unit else 0
def unitTensorCoeff (f : Rˣ → Rˣ → ℂ) (χ η : MulChar R ℂ) : ℂ :=
  unitFourierCoeff (fun u => unitFourierCoeff (f u) η) χ
def zeroExtendUnitPair (f : Rˣ → Rˣ → ℂ) (r s : R) : ℂ :=
  zeroExtendUnits (fun u => zeroExtendUnits (f u) s) r
end FiniteRayExpansion
open scoped BigOperators Classical
namespace RayFourExpansion
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion
abbrev RayRing := O ⧸ Ideal.span {(4 : O)}
noncomputable instance rayRingFintype : Fintype RayRing := by
  letI : Finite RayRing := finite_quotient_span (by norm_num : (4 : O) ≠ 0)
  exact Fintype.ofFinite _
abbrev RayCharacter := MulChar RayRing ℂ
noncomputable instance rayCharacterFintype : Fintype RayCharacter := Fintype.ofFinite _
def rayCharacter (χ : RayCharacter) (a : O) : ℂ :=
  χ (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)
def rayMask (a : O) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) then 1 else 0
def phaseCoeff (f : RayRing → ℂ) (χ : RayCharacter) : ℂ :=
  unitFourierCoeff (fun u : RayRingˣ => f (u : RayRing)) χ
def pairCoeff (f : RayRing → RayRing → ℂ) (χ η : RayCharacter) : ℂ :=
  unitTensorCoeff (fun u v : RayRingˣ => f (u : RayRing) (v : RayRing)) χ η
def gCoeff : RayCharacter → ℂ := phaseCoeff fixedGQuotientValue
def crossQuotientPhase (r s : RayRing) : ℂ :=
  MixedCrossSeparation.quadraticRayPair (residueQuotientFour r) (residueQuotientFour s)
def crossCoeff : RayCharacter → RayCharacter → ℂ := pairCoeff crossQuotientPhase
end RayFourExpansion
end
end OAI


