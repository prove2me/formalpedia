-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0100
-- name    : PNT_ZeroFree_433_0100
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:41:27.076025+00:00
-- url     : https://prove2.me/theorems/68be9066-ddd7-4b22-9401-3fdec40bd95b
-- title:
--   Zero-free region foundations: CubicSieve.TwistedProfiles [0100]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.TwistedProfiles
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/TwistedProfiles.lean#L87-L732

import Definitions.Def_PNT_ZeroFree_433_0099

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/TwistedProfiles.lean#L87-L732
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.TwistedProfiles
section
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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open JointLogSeparation
open FirstPassCubeLabels (jLabel)
open SecondPassIntegration (exists_fixed_twisted_normalized_child_tests elementNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem actualSecondRawVariableSector_twisted_profiles
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j t, windows j t ≠ 0 → |t| ≤ A+H+1) ∧
      ∀ (θ₁ θ₂ D E V₀ X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X₀ → 0 < K →
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O) (X : SecondSupportData ι → ℝ),
        (∀ x ∈ s, 0 < X x) →
        (∀ x ∈ s, x.frequency ≠ 0) →
        (∀ x ∈ s, |secondSectorZ p (X x) X₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D x| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E x| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K x| ≤ H) →
        actualSecondRawVariableSector p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W X Y =
          actualSecondVariableSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s
            (fun x => w x * (X x : ℂ)⁻¹) F Ψ₁ Ψ₂ (m*r)
            (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows D E V₀ X X₀ K Y := by
  obtain ⟨A₁, A₂, windows, hwc, hws, hwb, hid⟩ :=
    exists_fixed_twisted_normalized_child_tests p hp hcop hg g₁ g₂ W A H hA hH hg₁ hg₂
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro θ₁ θ₂ D E V₀ X₀ K Y hD hE hV₀ hX₀ hK B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r X hX hk hz hud hue huv hkap
  simp only [actualSecondRawVariableSector, actualSecondVariableSectorSource]
  apply Finset.sum_congr rfl
  intro x hx
  have heq := hid θ₁ θ₂ D E V₀ (X x) X₀ K Y hD hE hV₀ (hX x hx) hX₀ hK F x.overlap Ψ₁ Ψ₂ m r
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor) x.frequency
    (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _) (hk x hx)
    (hz x hx) (hud x hx) (hue x hx) (huv x hx) (hkap x hx)
  rw [heq]
  simp only [secondSupportLabel, secondSupportRow, actualSecondRow,
    secondSectorZ, secondSectorUd, secondSectorUe, secondSectorUv, secondSectorKap,
    elementNorm, mul_neg]
  ring

end
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label firstLogDensity)
open SecondPassIntegration (childGeometricMean)
open JointLogSeparation

theorem actual_raw_twisted_sector_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      (∀ z ud ue uv kap : ℝ, ‖outerWindow windows z ud ue uv kap‖ ≤ Cw) ∧
      ∀ D E V₀ X₀ K Y : ℝ, 0 < D → 0 < E → 0 < V₀ → 0 < X₀ → 0 < K → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ t₁ t₂ t₃ : ℝ,
        (1+Y*K/(D*E^2*V₀^2*X₀^2))^decayOrder * ‖(𝓕 (frequencyTwist A₁ (-θ₁))) t₁*(𝓕 (frequencyTwist A₂ θ₂)) t₂*b t₃‖ ≤
          Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*firstLogDensity J t₁*firstLogDensity J t₂*firstLogDensity J t₃) ∧
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (T : Finset (Ideal O × O))
        (w : SecondSupportData ι → ℂ) (Bnd lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O) (X : SecondSupportData ι → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) →
        (∀ x ∈ s, Disjoint x.common B) →
        (∀ x ∈ s, x.firstDivisor ⊆ x.common ∪ B) →
        (∀ x ∈ s, 0 < X x) → (∀ x ∈ s, x.frequency ≠ 0) →
        (∀ x ∈ s, |secondSectorZ p (X x) X₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D x| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E x| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K x| ≤ H) →
        0 ≤ Bnd → 0 ≤ lengthScale →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x, secondSupportRow p x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x * (X x : ℂ)⁻¹‖ * ‖outerWindow windows
          (secondSectorZ p (X x) X₀ x) (secondSectorUd p D x) (secondSectorUe p E x)
          (secondSectorUv p V₀ x) (secondSectorKap p K x)‖ ≤ Bnd) →
        ‖actualSecondRawVariableSector p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W X Y‖ ≤
          (Bnd*Cₐ*(lengthScale*Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
          (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
            ‖tripleCoefficient (𝓕 (frequencyTwist A₁ (-θ₁))) (𝓕 (frequencyTwist A₂ θ₂)) b (t₁,t₂,t₃)‖ *
              childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ (m*r) T (windows 5) (windows 6)
                X₀ X₀ (t₁,t₂,t₃)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ :=
    actualSecondRawVariableSector_twisted_profiles p hp hcop hg g₁ g₂ W A H hA hH hg₁ hg₂
  obtain ⟨Cw,hCw,hwglobal⟩ := outerWindow_global_bound windows hwc (fun j => (hws j).continuous)
  have hM : ∀ j : Fin 7, 0 ≤ (fun _ : Fin 7 => A+H+1) j := by intro j; dsimp; linarith
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ :=
    actual_second_variable_sector_twisted_transfer p hp hcop hg hinj ε hε A₁ A₂ W windows
      (fun _ => A+H+1) hM hwb decayOrder J
  refine ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hwglobal,?_⟩
  intro D E V₀ X₀ K Y hD hE hV₀ hX₀ hK hY
  obtain ⟨b,hb⟩ := htrans D E V₀ X₀ K Y hD hE hV₀ hX₀ hK hY
  refine ⟨b,?_⟩
  intro θ₁ θ₂
  obtain ⟨hpoint,hbound⟩ := hb (-θ₁) θ₂
  refine ⟨?_,?_⟩
  · simpa only [norm_neg] using hpoint
  intro B v₁ v₂ ε₁ ε₂ s T w Bnd lengthScale F Ψ₁ Ψ₂ m r X hv hCB hdiv hX hk hz hud hue huv hkap
    hBnd hL hmap hT hnorm hw
  rw [hid θ₁ θ₂ D E V₀ X₀ K Y hD hE hV₀ hX₀ hK B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r X
    hX hk hz hud hue huv hkap]
  exact hbound B v₁ v₂ ε₁ ε₂ s T (fun x => w x*(X x : ℂ)⁻¹) Bnd lengthScale F Ψ₁ Ψ₂ (m*r) X
    hv hCB hdiv hBnd hL hmap hT hnorm hw

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)
open FourierBridge (logPhase)
open SecondPassIntegration (conjugateProfile)

def firstCoreBaseProfile (g V : 𝓢(ℝ, ℂ)) (negative : Bool) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (if negative then conjugateProfile V else V) g

def firstCoreModeHeight (negative : Bool) (t : ℝ) : ℝ := if negative then t else -t

def firstCoreModeProfile (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  frequencyTwist (firstCoreBaseProfile g V negative) (firstCoreModeHeight negative t)

theorem firstCoreBaseProfile_apply (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (s : ℝ) :
    firstCoreBaseProfile g V negative s = g s * (if negative then star (V s) else V s) := by
  cases negative <;>
    simp only [firstCoreBaseProfile, Bool.false_eq_true, ite_false, ite_true,
      SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.hasTemperateGrowth _),
      smul_eq_mul, SecondPassIntegration.conjugateProfile_apply] <;> ring

lemma logPhase_neg_argument (t s : ℝ) : logPhase t (-s) = logPhase (-t) s := by
  unfold logPhase
  congr 1
  push_cast
  ring

theorem firstCoreModeProfile_apply (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t s : ℝ) :
    firstCoreModeProfile g V negative t s = g s *
      (if negative then star (V s * logPhase t (-s)) else V s * logPhase t (-s)) := by
  cases negative <;>
    simp only [firstCoreModeProfile, frequencyTwist_apply, firstCoreModeHeight,
      firstCoreBaseProfile_apply, Bool.false_eq_true, ite_false, ite_true,
      star_mul, logPhase_neg_argument, SecondPassIntegration.logPhase_conjugate, neg_neg] <;> ring

theorem firstCoreModeProfile_norm (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t s : ℝ) :
    ‖firstCoreModeProfile g V negative t s‖ = ‖g s‖ * ‖V s‖ := by
  rw [firstCoreModeProfile_apply]
  cases negative <;> simp [FourierBridge.logPhase_norm]

theorem firstCoreModeProfile_support (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t s : ℝ)
    (h : firstCoreModeProfile g V negative t s ≠ 0) : g s ≠ 0 ∧ V s ≠ 0 := by
  have hn : ‖g s‖ * ‖V s‖ ≠ 0 := by
    rw [← firstCoreModeProfile_norm g V negative t s]
    exact norm_ne_zero_iff.mpr h
  exact ⟨norm_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1,
    norm_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).2⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hp

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem firstCoreTest_eq_normalized_mode (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t : ℝ)
    (D S : Finset ι) (hDS : Disjoint D S) (X : ℝ) (hX : 0 < X) :
    firstCoreTest (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X)
        negative t D S =
      (‖eisEmbedding (∏ i ∈ D, p i)‖ : ℂ)⁻¹ *
        normalizedColumn p (fun A => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) A)) S := by
  simp only [firstCoreTest, normalizedColumn,
    SecondPassIntegration.columnLog_extract_common p hp D S hDS X hX,
    Finset.prod_union hDS, map_mul, norm_mul, Complex.ofReal_mul,
    firstCoreModeProfile_apply]
  ring

theorem firstCoreInputRow_eq_mode_row
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (z : O) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
      (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z =
      (‖eisEmbedding (∏ i ∈ D, p i)‖ : ℂ)⁻¹ *
      inputConjugateRow p hg (F\D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (normalizedColumn p (fun A => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) A))) (if negative then -z else z) := by
  unfold firstCoreInputRow inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hDS : Disjoint D S := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hS) disjoint_sdiff_self_right
  simp only [secondInputCoefficient, firstCoreTest_eq_normalized_mode p hp g V negative t D S hDS X hX]
  ring

theorem firstCoreInputRow_mode_norm_sq
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (z : O) :
    ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
      (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2 =
      (primeProductNorm p D)⁻¹ *
      ‖inputConjugateRow p hg (F\D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (normalizedColumn p (fun A => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) A))) (if negative then -z else z)‖ ^ 2 := by
  rw [firstCoreInputRow_eq_mode_row p hp hg F D B v ε₁ ε₂ negative χ Ψ m g V X hX c d r t z]
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), mul_pow, inv_pow, primeProductNorm]

end SecondPassArithmetic

namespace CubicEisenstein
open Filter
open scoped BigOperators Classical MatrixGroups Matrix Topology

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

abbrev UpperCoordinates := {p : ℂ × ℝ // 0 < p.2}

def coordinateSection (w : UpperCoordinates) : SL(2,ℂ) :=
  upperSection w.1.1 w.1.2 w.2

lemma continuous_coordinate_inverse_operator :
    Continuous (fun w : UpperCoordinates => rowOperator (coordinateSection w)⁻¹) := by
  have hroot : Continuous (fun w : UpperCoordinates => (Real.sqrt w.1.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_snd.comp continuous_subtype_val))
  have hne : ∀ w : UpperCoordinates, (Real.sqrt w.1.2 : ℂ) ≠ 0 := fun w =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr w.2).ne'
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_pi
  intro i
  change Continuous (fun w : UpperCoordinates =>
    Matrix.vecMul u (Matrix.adjugate (coordinateSection w : Matrix (Fin 2) (Fin 2) ℂ)) i)
  simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,coordinateSection,upperSection,
    Matrix.SpecialLinearGroup.coe_mk,Matrix.adjugate_fin_two]
  fin_cases i
  · change Continuous (fun w : UpperCoordinates =>
      u 0 * (Real.sqrt w.1.2 : ℂ)⁻¹ + u 1 * (-0))
    exact (continuous_const.mul (hroot.inv₀ hne)).add
      (continuous_const.mul continuous_const)
  · change Continuous (fun w : UpperCoordinates =>
      u 0 * (-(w.1.1 / (Real.sqrt w.1.2 : ℂ))) + u 1 * (Real.sqrt w.1.2 : ℂ))
    exact (continuous_const.mul ((continuous_fst.comp continuous_subtype_val).div hroot hne).neg).add
      (continuous_const.mul hroot)

lemma continuous_coordinate_rowBound :
    Continuous (fun w : UpperCoordinates => rowBound (coordinateSection w)) :=
  continuous_const.mul (continuous_const.add continuous_coordinate_inverse_operator.norm)

lemma continuous_coordinate_summand (x : CuspCosets) :
    Continuous (fun p : UpperCoordinates × ℂ => summand (coordinateSection p.1) p.2 x) := by
  have hv : Continuous (fun p : UpperCoordinates × ℂ => p.1.1.2) :=
    (continuous_snd.comp continuous_subtype_val).comp continuous_fst
  have hz : Continuous (fun p : UpperCoordinates × ℂ => p.1.1.1) :=
    (continuous_fst.comp continuous_subtype_val).comp continuous_fst
  simp only [coordinateSection,summand_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    apply hv.div
    · unfold heightDenominator
      exact ((continuous_const.mul hz).add continuous_const).norm.pow 2 |>.add
        (continuous_const.mul (hv.pow 2))
    · intro p
      exact (heightDenominator_pos _ _ p.1.2 _ (embeddedRow_ne_zero x)).ne'
  · exact continuous_snd
  · intro p
    exact Complex.ofReal_mem_slitPlane.mpr (div_pos p.1.2
      (heightDenominator_pos _ _ p.1.2 _ (embeddedRow_ne_zero x)))

lemma coordinate_summable_majorant (C a b : ℝ) (hC : 0 < C)
    (ha : 2 < a) (hb : 2 < b) :
    ∃ M : CuspCosets → ℝ, Summable M ∧ (∀ x,0 ≤ M x) ∧
      ∀ p : UpperCoordinates × ℂ,
        rowBound (coordinateSection p.1) ≤ C → a ≤ p.2.re → p.2.re ≤ b →
        ∀ x, ‖summand (coordinateSection p.1) p.2 x‖ ≤ M x := by
  let weight (t : ℝ) (x : CuspCosets) :=
    C^(2*t)*‖rowCoordinates (cosetRow x)‖^(-(2*t))
  have hsum (t : ℝ) (ht : 2<t) : Summable (weight t) := by
    have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
      rowCoordinates_injective.comp cosetRow_injective
    exact ((summable_integer_four_rpow (2*t) (by linarith)).comp_injective hinj).mul_left _
  refine ⟨fun x => weight a x + weight b x,(hsum a ha).add (hsum b hb),?_,?_⟩
  · intro x
    dsimp [weight]
    positivity
  · intro p hbound hpa hpb x
    apply (norm_summand_strip (coordinateSection p.1) a b p.2 hpa hpb x).trans
    apply add_le_add
    · apply (norm_summand_bound (coordinateSection p.1) (a:ℂ) (by simpa using lt_trans (by norm_num) ha) x).trans
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (rowBound_pos _).le hbound (by simpa only [Complex.ofReal_re] using (show 0 ≤ 2*a by linarith))) (by positivity)
    · apply (norm_summand_bound (coordinateSection p.1) (b:ℂ) (by simpa using lt_trans (by norm_num) hb) x).trans
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (rowBound_pos _).le hbound (by simpa only [Complex.ofReal_re] using (show 0 ≤ 2*b by linarith))) (by positivity)

theorem coordinate_eisenstein_continuousAt (p : UpperCoordinates × ℂ) (hp : 2 < p.2.re) :
    ContinuousAt (fun q : UpperCoordinates × ℂ => eisenstein (coordinateSection q.1) q.2) p := by
  let a : ℝ := (2+p.2.re)/2
  let b : ℝ := p.2.re+1
  let C : ℝ := rowBound (coordinateSection p.1)+1
  let region : Set (UpperCoordinates × ℂ) := {q |
    rowBound (coordinateSection q.1) < C ∧ a < q.2.re ∧ q.2.re < b}
  have ha : 2<a := by dsimp [a]; linarith
  have hb : 2<b := by dsimp [b]; linarith
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection p.1)]
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C a b hC ha hb
  have hopen : IsOpen region := by
    exact (isOpen_lt (continuous_coordinate_rowBound.comp continuous_fst) continuous_const).inter
      ((isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd)).inter
        (isOpen_lt (Complex.continuous_re.comp continuous_snd) continuous_const))
  have hmem : p ∈ region := by
    dsimp [region,a,b,C]
    constructor
    · linarith
    · constructor <;> linarith
  have hcont : ContinuousOn (fun q : UpperCoordinates × ℂ =>
      ∑' x : CuspCosets, summand (coordinateSection q.1) q.2 x) region := by
    apply continuousOn_tsum (fun x => (continuous_coordinate_summand x).continuousOn) hM
    intro x q hq
    exact hbound q hq.1.le hq.2.1.le hq.2.2.le x
  exact (hcont p hmem).continuousAt (hopen.mem_nhds hmem)

theorem coordinate_eisenstein_tendstoUniformlyOn (C a b : ℝ) (hC : 0<C)
    (ha : 2<a) (hb : 2<b) :
    TendstoUniformlyOn
      (fun f : Finset CuspCosets => fun p : UpperCoordinates × ℂ =>
        ∑ x ∈ f, summand (coordinateSection p.1) p.2 x)
      (fun p => eisenstein (coordinateSection p.1) p.2) atTop
      {p | rowBound (coordinateSection p.1) ≤ C ∧ a ≤ p.2.re ∧ p.2.re ≤ b} := by
  obtain ⟨M,hM,_,hbound⟩ := coordinate_summable_majorant C a b hC ha hb
  exact tendstoUniformlyOn_tsum hM (fun x p hp => hbound p hp.1 hp.2.1 hp.2.2 x)

theorem coordinate_eisenstein_continuousOn :
    ContinuousOn (fun p : UpperCoordinates × ℂ =>
      eisenstein (coordinateSection p.1) p.2) {p | 2 < p.2.re} :=
  fun p hp => (coordinate_eisenstein_continuousAt p hp).continuousWithinAt

theorem upperEisenstein_joint_continuousAt (p : UpperCoordinates × ℂ)
    (hp : 2 < p.2.re) :
    ContinuousAt (fun q : UpperCoordinates × ℂ =>
      upperEisenstein q.1.1.1 q.1.1.2 q.1.2 q.2) p :=
  coordinate_eisenstein_continuousAt p hp

end CubicEisenstein

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

def logRatioPower (s : ℂ) (v q : ℝ) : ℂ :=
  Complex.exp (s * ((Real.log v - Real.log q : ℝ) : ℂ))

lemma logRatioPower_eq_cpow (s : ℂ) {v q : ℝ} (hv : 0<v) (hq : 0<q) :
    logRatioPower s v q = ((v/q : ℝ):ℂ)^s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hv hq).ne'),
    ← Complex.ofReal_log (div_pos hv hq).le, Real.log_div hv.ne' hq.ne']
  unfold logRatioPower
  congr 1
  ring

lemma hasDerivAt_logRatioPower (s : ℂ) {f g : ℝ → ℝ} {x f' g' : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) :
    HasDerivAt (fun t => logRatioPower s (f t) (g t))
      (logRatioPower s (f x) (g x) * s * ((f'/f x-g'/g x : ℝ):ℂ)) x := by
  convert! (((hf.log hf0).sub (hg.log hg0)).ofReal_comp.const_mul s).cexp using 1 <;>
    dsimp [logRatioPower] ; ring

lemma hasDerivAt_deriv_logRatioPower (s : ℂ) (f g df dg : ℝ → ℝ) (x ddf ddg : ℝ)
    (hf : ∀t, HasDerivAt f (df t) t) (hg : ∀t, HasDerivAt g (dg t) t)
    (hdf : HasDerivAt df ddf x) (hdg : HasDerivAt dg ddg x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) :
    HasDerivAt (deriv (fun t => logRatioPower s (f t) (g t)))
      (logRatioPower s (f x) (g x) *
        (s^2 * ((df x/f x-dg x/g x : ℝ):ℂ)^2 +
         s * (((ddf*f x-df x*df x)/(f x)^2 -
           (ddg*g x-dg x*dg x)/(g x)^2 : ℝ):ℂ))) x := by
  have hnear : ∀ᶠ t in 𝓝 x, f t ≠ 0 ∧ g t ≠ 0 :=
    ((hf x).continuousAt.eventually_ne hf0).and ((hg x).continuousAt.eventually_ne hg0)
  have heq : (deriv (fun t => logRatioPower s (f t) (g t))) =ᶠ[𝓝 x]
      (fun t => logRatioPower s (f t) (g t) * s * ((df t/f t-dg t/g t : ℝ):ℂ)) := by
    filter_upwards [hnear] with t ht
    exact (hasDerivAt_logRatioPower s (hf t) (hg t) ht.1 ht.2).deriv
  have hfirst := hasDerivAt_logRatioPower s (hf x) (hg x) hf0 hg0
  have hsecond := ((hdf.div (hf x) hf0).sub (hdg.div (hg x) hg0)).ofReal_comp
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert! (hfirst.mul_const s).mul hsecond using 1 ;
    simp only [Pi.sub_apply,Pi.div_apply] ; ring

def quadraticHeightDenominator (A B C D x y v : ℝ) : ℝ :=
  A*(x^2+y^2+v^2)+2*(B*x+C*y)+D

lemma quadraticHeightDenominator_hasDerivAt_x (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D t y v)
      (2*(A*x+B)) x := by
  convert! (((((hasDerivAt_id x).pow 2).add_const (y^2)).add_const (v^2)).const_mul A).add
    ((((hasDerivAt_id x).const_mul B).add_const (C*y)).const_mul 2) |>.add_const D using 1 <;>
    dsimp [quadraticHeightDenominator] ; ring

lemma quadraticHeightDenominator_hasDerivAt_y (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D x t v)
      (2*(A*y+C)) y := by
  convert! (((((hasDerivAt_id y).pow 2).const_add (x^2)).add_const (v^2)).const_mul A).add
    ((((hasDerivAt_id y).const_mul C).const_add (B*x)).const_mul 2) |>.add_const D using 1 <;>
    dsimp [quadraticHeightDenominator] ; ring

lemma quadraticHeightDenominator_hasDerivAt_v (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D x y t)
      (2*A*v) v := by
  convert! ((((hasDerivAt_id v).pow 2).const_add (x^2+y^2)).const_mul A).add_const
    (2*(B*x+C*y)+D) using 1 <;> dsimp [quadraticHeightDenominator] <;> ring_nf

def spatialHeightPower (s : ℂ) (A B C D x y v : ℝ) : ℂ :=
  logRatioPower s v (quadraticHeightDenominator A B C D x y v)

def heightLogDx (A B C D x y v : ℝ) : ℝ :=
  -(2*(A*x+B)/quadraticHeightDenominator A B C D x y v)
def heightLogDy (A B C D x y v : ℝ) : ℝ :=
  -(2*(A*y+C)/quadraticHeightDenominator A B C D x y v)
def heightLogDv (A B C D x y v : ℝ) : ℝ :=
  1/v - 2*A*v/quadraticHeightDenominator A B C D x y v

def heightLogDxx (A B C D x y v : ℝ) : ℝ :=
  -((2*A*quadraticHeightDenominator A B C D x y v -
    (2*(A*x+B))*(2*(A*x+B)))/(quadraticHeightDenominator A B C D x y v)^2)
def heightLogDyy (A B C D x y v : ℝ) : ℝ :=
  -((2*A*quadraticHeightDenominator A B C D x y v -
    (2*(A*y+C))*(2*(A*y+C)))/(quadraticHeightDenominator A B C D x y v)^2)
def heightLogDvv (A B C D x y v : ℝ) : ℝ :=
  -(1/v^2) - ((2*A*quadraticHeightDenominator A B C D x y v -
    (2*A*v)*(2*A*v))/(quadraticHeightDenominator A B C D x y v)^2)

lemma deriv_spatialHeightPower_v (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (spatialHeightPower s A B C D x y) v =
      spatialHeightPower s A B C D x y v * s * (heightLogDv A B C D x y v : ℂ) := by
  exact (hasDerivAt_logRatioPower s (hasDerivAt_id v)
    (quadraticHeightDenominator_hasDerivAt_v A B C D x y v) hv hq).deriv

lemma deriv2_spatialHeightPower_x (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (deriv (fun t => spatialHeightPower s A B C D t y v)) x =
      spatialHeightPower s A B C D x y v *
        (s^2*(heightLogDx A B C D x y v : ℂ)^2 +
          s*(heightLogDxx A B C D x y v : ℂ)) := by
  have h := hasDerivAt_deriv_logRatioPower s (fun _ => v)
    (fun t => quadraticHeightDenominator A B C D t y v) (fun _ => 0)
    (fun t => 2*(A*t+B)) x 0 (2*A)
    (fun t => hasDerivAt_const t v)
    (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t y v)
    (hasDerivAt_const x 0) (by simpa only [id_eq,mul_one] using ((hasDerivAt_id x).const_mul A |>.add_const B).const_mul 2)
    hv hq
  simpa only [spatialHeightPower,heightLogDx,heightLogDxx,zero_div,zero_sub,zero_mul,sub_zero] using h.deriv

lemma deriv2_spatialHeightPower_y (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (deriv (fun t => spatialHeightPower s A B C D x t v)) y =
      spatialHeightPower s A B C D x y v *
        (s^2*(heightLogDy A B C D x y v : ℂ)^2 +
          s*(heightLogDyy A B C D x y v : ℂ)) := by
  have h := hasDerivAt_deriv_logRatioPower s (fun _ => v)
    (fun t => quadraticHeightDenominator A B C D x t v) (fun _ => 0)
    (fun t => 2*(A*t+C)) y 0 (2*A)
    (fun t => hasDerivAt_const t v)
    (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D x t v)
    (hasDerivAt_const y 0) (by simpa only [id_eq,mul_one] using ((hasDerivAt_id y).const_mul A |>.add_const C).const_mul 2)
    hv hq
  simpa only [spatialHeightPower,heightLogDy,heightLogDyy,zero_div,zero_sub,zero_mul,sub_zero] using h.deriv

lemma deriv2_spatialHeightPower_v (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (deriv (spatialHeightPower s A B C D x y)) v =
      spatialHeightPower s A B C D x y v *
        (s^2*(heightLogDv A B C D x y v : ℂ)^2 +
          s*(heightLogDvv A B C D x y v : ℂ)) := by
  change deriv (deriv (fun t => logRatioPower s t
    (quadraticHeightDenominator A B C D x y t))) v = _
  have h := hasDerivAt_deriv_logRatioPower s (fun t => t)
    (fun t => quadraticHeightDenominator A B C D x y t) (fun _ => 1)
    (fun t => 2*A*t) v 0 (2*A)
    (fun t => hasDerivAt_id t)
    (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D x y t)
    (hasDerivAt_const v 1) (by simpa only [id_eq,mul_one] using (hasDerivAt_id v).const_mul (2*A))
    hv hq
  simpa only [spatialHeightPower,heightLogDv,heightLogDvv,zero_mul,zero_sub,one_mul,neg_div] using h.deriv

lemma quadraticHeight_gradient_square (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) :
    (A*x+B)^2 + (A*y+C)^2 + (A*v)^2 =
      A*quadraticHeightDenominator A B C D x y v := by
  unfold quadraticHeightDenominator
  nlinarith [hrel]

lemma heightLog_eikonal (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    v^2 * ((heightLogDx A B C D x y v)^2 +
      (heightLogDy A B C D x y v)^2 + (heightLogDv A B C D x y v)^2) = 1 := by
  calc
    _ = 1 + 4*v^2/(quadraticHeightDenominator A B C D x y v)^2 *
        ((A*x+B)^2+(A*y+C)^2+(A*v)^2 - A*quadraticHeightDenominator A B C D x y v) := by
      unfold heightLogDx heightLogDy heightLogDv
      field_simp [hv,hq]
      ; ring
    _ = 1 := by rw [quadraticHeight_gradient_square A B C D x y v hrel]; ring

lemma heightLog_laplacian (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    v^2 * (heightLogDxx A B C D x y v +
      heightLogDyy A B C D x y v + heightLogDvv A B C D x y v) -
      v*heightLogDv A B C D x y v = -2 := by
  calc
    _ = -2 + 4*v^2/(quadraticHeightDenominator A B C D x y v)^2 *
        ((A*x+B)^2+(A*y+C)^2+(A*v)^2 - A*quadraticHeightDenominator A B C D x y v) := by
      unfold heightLogDxx heightLogDyy heightLogDvv heightLogDv
      field_simp [hv,hq]
      ; ring
    _ = -2 := by rw [quadraticHeight_gradient_square A B C D x y v hrel]; ring

def hyperbolicLaplacian (f : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^2 * (deriv (deriv (fun t => f t y v)) x +
    deriv (deriv (fun t => f x t v)) y + deriv (deriv (f x y)) v) -
    (v:ℂ)*deriv (f x y) v

theorem spatialHeightPower_eigenfunction (s : ℂ) (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    hyperbolicLaplacian (spatialHeightPower s A B C D) x y v =
      s*(s-2)*spatialHeightPower s A B C D x y v := by
  have he : (v:ℂ)^2 * ((heightLogDx A B C D x y v : ℂ)^2 +
      (heightLogDy A B C D x y v : ℂ)^2 + (heightLogDv A B C D x y v : ℂ)^2) = 1 := by
    exact_mod_cast heightLog_eikonal A B C D x y v hrel hv hq
  have hl : (v:ℂ)^2 * ((heightLogDxx A B C D x y v : ℂ) +
      (heightLogDyy A B C D x y v : ℂ) + (heightLogDvv A B C D x y v : ℂ)) -
      (v:ℂ)*(heightLogDv A B C D x y v : ℂ) = -2 := by
    exact_mod_cast heightLog_laplacian A B C D x y v hrel hv hq
  unfold hyperbolicLaplacian
  rw [deriv2_spatialHeightPower_x s A B C D x y v hv hq,
    deriv2_spatialHeightPower_y s A B C D x y v hv hq,
    deriv2_spatialHeightPower_v s A B C D x y v hv hq,
    deriv_spatialHeightPower_v s A B C D x y v hv hq]
  calc
    _ = spatialHeightPower s A B C D x y v *
        (s^2*((v:ℂ)^2*((heightLogDx A B C D x y v : ℂ)^2 +
          (heightLogDy A B C D x y v : ℂ)^2 + (heightLogDv A B C D x y v : ℂ)^2)) +
        s*((v:ℂ)^2*((heightLogDxx A B C D x y v : ℂ) +
          (heightLogDyy A B C D x y v : ℂ) + (heightLogDvv A B C D x y v : ℂ)) -
          (v:ℂ)*(heightLogDv A B C D x y v : ℂ))) := by ring
    _ = _ := by rw [he,hl]; ring

lemma complex_row_quadratic_relation (c d : ℂ) :
    Complex.normSq c * Complex.normSq d = (c*star d).re^2 + (-(c*star d).im)^2 := by
  simp only [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im]
  ring

lemma heightDenominator_eq_quadratic (u : Fin 2 → ℂ) (x y v : ℝ) :
    heightDenominator ((x:ℂ)+(y:ℂ)*Complex.I) v u =
      quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  unfold heightDenominator quadraticHeightDenominator
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

def actualHeightPower (s : ℂ) (u : Fin 2 → ℂ) (x y v : ℝ) : ℂ :=
  ((transformedHeight ((x:ℂ)+(y:ℂ)*Complex.I) v u : ℝ) : ℂ)^s

lemma actualHeightPower_eq_spatial (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (x y v : ℝ) (hv : 0<v) :
    actualHeightPower s u x y v =
      spatialHeightPower s (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  rw [actualHeightPower,spatialHeightPower,logRatioPower_eq_cpow s hv]
  · rw [transformedHeight,heightDenominator_eq_quadratic]
  · rw [← heightDenominator_eq_quadratic]
    exact heightDenominator_pos _ _ hv u hu

theorem actualHeightPower_eigenfunction (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (x y v : ℝ) (hv : 0<v) :
    hyperbolicLaplacian (actualHeightPower s u) x y v =
      s*(s-2)*actualHeightPower s u x y v := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have heq (x' y' v' : ℝ) (hv' : 0<v') :
      actualHeightPower s u x' y' v' = spatialHeightPower s A B C D x' y' v' :=
    actualHeightPower_eq_spatial s u hu x' y' v' hv'
  have hxeq : (fun t => actualHeightPower s u t y v) =
      (fun t => spatialHeightPower s A B C D t y v) := funext fun t => heq t y v hv
  have hyeq : (fun t => actualHeightPower s u x t v) =
      (fun t => spatialHeightPower s A B C D x t v) := funext fun t => heq x t v hv
  have hveq : actualHeightPower s u x y =ᶠ[𝓝 v] spatialHeightPower s A B C D x y := by
    filter_upwards [isOpen_Ioi.mem_nhds (show v ∈ Set.Ioi 0 from hv)] with t ht
    exact heq x y t ht
  have hq : quadraticHeightDenominator A B C D x y v≠0 := by
    rw [← heightDenominator_eq_quadratic]
    exact (heightDenominator_pos _ _ hv u hu).ne'
  rw [heq x y v hv]
  convert! spatialHeightPower_eigenfunction s A B C D x y v
    (complex_row_quadratic_relation (u 0) (u 1)) hv.ne' hq using 1
  unfold hyperbolicLaplacian
  rw [hxeq,hyeq,hveq.deriv_eq,hveq.deriv.deriv_eq]

lemma hyperbolicLaplacian_const_mul (c : ℂ) (f : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) :
    hyperbolicLaplacian (fun x y v => c*f x y v) x y v =
      c*hyperbolicLaplacian f x y v := by
  unfold hyperbolicLaplacian
  simp only [deriv_const_mul_field',deriv_const_mul_field]
  ring

theorem eisenstein_summand_eigenfunction (s : ℂ) (r : CuspCosets) (x y v : ℝ) (hv : 0<v) :
    hyperbolicLaplacian
      (fun x y v => (cosetCharacter r)⁻¹ * actualHeightPower s (embeddedRow r) x y v) x y v =
      s*(s-2)*((cosetCharacter r)⁻¹ * actualHeightPower s (embeddedRow r) x y v) := by
  rw [hyperbolicLaplacian_const_mul,
    actualHeightPower_eigenfunction s (embeddedRow r) (embeddedRow_ne_zero r) x y v hv]
  ring

lemma eigenfunction_summand_eq_actual_series (s : ℂ) (r : CuspCosets)
    (x y v : ℝ) (hv : 0<v) :
    (cosetCharacter r)⁻¹ * actualHeightPower s (embeddedRow r) x y v =
      summand (upperSection ((x:ℂ)+(y:ℂ)*Complex.I) v hv) s r := by
  rw [summand_upperSection]
  rfl

end CubicEisenstein

end

end OAI

end


