-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0080
-- name    : PNT_ZeroFree_433_0080
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:42:45.903423+00:00
-- url     : https://prove2.me/theorems/fb65b7ea-3c21-4b9e-a557-4288a17b9335
-- title:
--   Zero-free region foundations: CubicSieve.IntegratedTransfer [0080]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.IntegratedTransfer
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/IntegratedTransfer.lean#L88-L683

import Definitions.Def_PNT_ZeroFree_433_0079

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/IntegratedTransfer.lean#L88-L683
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.IntegratedTransfer
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

lemma sideRayMonoid_norm_le_one (negative : Bool) (χ : RayCharacter) (a : O) :
    ‖sideRayMonoid negative χ a‖ ≤ 1 := by
  cases negative <;> simp only [sideRayMonoid, Bool.false_eq_true, ite_false, ite_true,
    conjugateRayMonoid_apply, rayMonoid_apply, norm_star]
  all_goals exact FiniteRayExpansion.norm_char_le_one _ _

lemma firstCoreTwist_norm_le (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ)
    (r : FirstCoreIndex) (a : O) :
    ‖firstCoreTwist negative χ Ψ r a‖ ≤ ‖Ψ a‖ := by
  have hc : ‖coreRayTwist negative r.1 r.2.2 a‖ ≤ 1 := by
    change ‖RayFourExpansion.rayCharacter (FirstPassCubeLabels.coreRayCharacter negative r.1 r.2.2) a‖ ≤ 1
    exact FiniteRayExpansion.norm_char_le_one _ _
  simp only [firstCoreTwist, MonoidHom.mul_apply, norm_mul]
  calc
    _ ≤ 1 * (‖Ψ a‖ * 1) := by gcongr; exact sideRayMonoid_norm_le_one _ _ _
    _ = _ := by ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
theorem firstCoreOuter_norm_le
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (D : Finset ι) (r : FirstCoreIndex) :
    ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ ≤
      ‖coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2‖ *
        ‖Ψ (∏ i ∈ D, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) D m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  have hc : ‖coreRayTwist negative r.1 r.2.2 (∏ i ∈ D, p i)‖ ≤ 1 := by
    change ‖RayFourExpansion.rayCharacter (FirstPassCubeLabels.coreRayCharacter negative r.1 r.2.2) (∏ i ∈ D, p i)‖ ≤ 1
    exact FiniteRayExpansion.norm_char_le_one _ _
  have hs : ‖(if negative then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg D (-1))
      else 1 : ℂ)‖ ≤ 1 := by
    cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true, norm_one, norm_star]
    · exact le_rfl
    · exact finiteSquarefreeRow_norm_le_one _ hg D _
  simp only [firstCoreOuter, norm_mul, MonoidHom.mul_apply]
  calc
    _ ≤ ‖coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2‖ *
        (‖Ψ (∏ i ∈ D, p i)‖ * 1) * 1 * 1 := by gcongr
    _ = _ := by ring

omit [DecidableEq ι] in
theorem firstCoreOuter_mass
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (D : Finset ι)
    (hΨ : ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    (∑ r : FirstCoreIndex, ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖) ≤ 32 * 512 := by
  calc
    _ ≤ ∑ r : FirstCoreIndex,
        ‖coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2‖ := by
      apply Finset.sum_le_sum
      intro r hr
      exact (firstCoreOuter_norm_le p hg B v ε₁ ε₂ negative Ψ m D r).trans
        (mul_le_of_le_one_right (norm_nonneg _) hΨ)
    _ ≤ 32 * 512 := by
      simpa only [Fintype.sum_prod_type] using
        FirstPassCubeLabels.coreRayCoefficient_mass p (cubeOddSupport B v ε₁ ε₂) negative

theorem dilatedCoreRow_sq_le_input_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O)
    (hΨ : ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m H) V y c d t z‖ ^ 2 ≤
    (32 * 512) * ∑ r : FirstCoreIndex, ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
      ‖inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstCoreTest H V y negative t D) (if negative then -z else z)‖ ^ 2 := by
  rw [dilatedCoreRow_eq_input_family p hp hcop hg hc hpr]
  let w := firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D
  let Q := fun r : FirstCoreIndex => inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
    (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (firstCoreTest H V y negative t D) (if negative then -z else z)
  have h := DescentWeightedCauchy.weighted_cauchy_sq Finset.univ w (fun _ => 1) (fun r => star (Q r))
  simp only [mul_one, star_star, norm_one, one_pow, norm_star] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (firstCoreOuter_mass p hg B v ε₁ ε₂ negative Ψ m D hΨ) (by positivity))

theorem firstCoreTest_continuous
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (D U : Finset ι) :
    Continuous (fun t : ℝ => firstCoreTest H V y negative t D U) := by
  have h := FourierBridge.logPhase_continuous_left (-(y (D ∪ U)))
  cases negative <;> simp only [firstCoreTest, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

theorem firstCoreTest_norm
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (D U : Finset ι) (t : ℝ) :
    ‖firstCoreTest H V y negative t D U‖ = ‖firstCoreTest H V y negative 0 D U‖ := by
  cases negative <;> simp only [firstCoreTest, Bool.false_eq_true, ite_false, ite_true,
    norm_mul, norm_star, FourierBridge.logPhase_norm]

def firstCoreInputRow (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (z : O) : ℂ :=
  inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
    (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (firstCoreTest H V y negative t D) (if negative then -z else z)

theorem firstCoreInputRow_continuous
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (z : O) :
    Continuous (fun t : ℝ => firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z) := by
  unfold firstCoreInputRow inputConjugateRow supportConjugateSum secondInputCoefficient
  apply continuous_finsetSum
  intro U hU
  have ht := firstCoreTest_continuous H V y negative D U
  fun_prop

theorem firstCoreInputRow_uniform_bound
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (z : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ≤ M := by
  let q := fun (t : ℝ) (U : Finset ι) =>
    supportMobius (fun i => Ideal.span {p i}) U *
      secondInputCoefficient p hg (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstCoreTest H V y negative t D) U *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U (if negative then -z else z))
  refine ⟨∑ U ∈ (F \ D).powerset, ‖q 0 U‖, by positivity, ?_⟩
  intro t
  change ‖∑ U ∈ (F \ D).powerset, q t U‖ ≤ _
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro U hU
  simp only [q, secondInputCoefficient, norm_mul, firstCoreTest_norm]

theorem firstCoreInputRow_integrable
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (z : O) {k : ℝ → ℝ} (hk : Integrable k volume) :
    Integrable (fun t : ℝ => k t *
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) volume := by
  obtain ⟨M, hM, hb⟩ := firstCoreInputRow_uniform_bound p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z
  apply hk.mul_bdd (c := M ^ 2)
  · exact ((firstCoreInputRow_continuous p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z).norm.pow 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (cubeOddSupport coreRayCoefficient dilatedCoreRow b0Label jLabel
  firstLogDensity columnLog normalizedColumn firstOutputEnergy)
open RayFourExpansion (RayCharacter crossCoeff)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem dilatedCoreRow_energy_le_input_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (T : Finset O) (k : ℝ → ℝ) (hk : Integrable k volume) (hk0 : ∀ t, 0 ≤ k t)
    (hΨ : ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    (∫ t : ℝ, k t * ∑ z ∈ T,
      ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
        (multiplicativeCoreColumn p Ψ m H) V y c d t z‖ ^ 2) ≤
    (32 * 512) * ∑ r : FirstCoreIndex, ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
      ∫ t : ℝ, k t * ∑ z ∈ T,
        ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2 := by
  let P := fun t z => dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
    (multiplicativeCoreColumn p Ψ m H) V y c d t z
  let Q := fun r t z => firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z
  let w := fun r => ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖
  have iP : Integrable (fun t : ℝ => k t * ∑ z ∈ T, ‖P t z‖ ^ 2) volume := by
    simp only [Finset.mul_sum]
    apply integrable_finsetSum
    intro z hz
    exact FirstPassCubeLabels.dilatedCoreRow_integrable p hp hcop hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m H) V y c d z hk
  have iQ (r : FirstCoreIndex) : Integrable (fun t : ℝ => k t * ∑ z ∈ T, ‖Q r t z‖ ^ 2) volume := by
    simp only [Finset.mul_sum]
    apply integrable_finsetSum
    intro z hz
    exact firstCoreInputRow_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z hk
  have iR : Integrable (fun t : ℝ => ∑ r : FirstCoreIndex, w r * (k t * ∑ z ∈ T, ‖Q r t z‖ ^ 2)) volume :=
    integrable_finsetSum _ (fun r hr => (iQ r).const_mul (w r))
  have hpoint (t : ℝ) : k t * (∑ z ∈ T, ‖P t z‖ ^ 2) ≤
      (32 * 512) * ∑ r : FirstCoreIndex, w r * (k t * ∑ z ∈ T, ‖Q r t z‖ ^ 2) := by
    calc
      _ ≤ k t * ∑ z ∈ T, ((32 * 512) * ∑ r : FirstCoreIndex, w r * ‖Q r t z‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (hk0 t)
        apply Finset.sum_le_sum
        intro z hz
        exact dilatedCoreRow_sq_le_input_family p hp hcop hg hc hpr F D B v ε₁ ε₂ negative χ Ψ m
          H V y c d t z hΨ
      _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro z hz
        ring
  calc
    _ ≤ ∫ t : ℝ, (32 * 512) * ∑ r : FirstCoreIndex, w r * (k t * ∑ z ∈ T, ‖Q r t z‖ ^ 2) :=
      integral_mono iP (iR.const_mul _) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun r hr => (iQ r).const_mul (w r))]
      simp only [integral_const_mul]
      rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem normalizedColumn_multiplicativeCoreColumn
    (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) :
    normalizedColumn p (multiplicativeCoreColumn p Ψ m H) =
      multiplicativeCoreColumn p Ψ m (normalizedColumn p H) := by
  funext S
  simp only [normalizedColumn, multiplicativeCoreColumn, div_eq_mul_inv]
  ring

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

theorem firstInputFamilyEnergy_nonneg
    (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) :
    0 ≤ firstInputFamilyEnergy p hg F B v ε₁ ε₂ negative Ψ m H V X c d J T := by
  unfold firstInputFamilyEnergy
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro D hD
  apply mul_nonneg (norm_nonneg _)
  apply Finset.sum_nonneg
  intro r hr
  apply mul_nonneg (norm_nonneg _)
  apply integral_nonneg
  intro t
  exact mul_nonneg (FirstPassCubeLabels.firstLogDensity_nonneg J t)
    (Finset.sum_nonneg (fun z hz => sq_nonneg _))

theorem firstOutputEnergy_le_input_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O)
    (hΨ : ∀ D ∈ F.powerset, ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ negative
      (multiplicativeCoreColumn p Ψ m H) V X c d J T ≤
    (32 * 512) * firstInputFamilyEnergy p hg F B v ε₁ ε₂ negative Ψ m H V X c d J T := by
  unfold firstOutputEnergy firstInputFamilyEnergy
  rw [normalizedColumn_multiplicativeCoreColumn]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro D hD
  have h := dilatedCoreRow_energy_le_input_family p hp hcop hg hc hpr F D B v ε₁ ε₂ negative
    (if negative then a.1 else a.2) Ψ m (normalizedColumn p H) V (columnLog p X) c d T
    (firstLogDensity J) (FirstPassCubeLabels.firstLogDensity_integrable J)
    (FirstPassCubeLabels.firstLogDensity_nonneg J) (hΨ D hD)
  have hh := mul_le_mul_of_nonneg_left h (norm_nonneg (crossCoeff a.1 a.2))
  simpa only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hh

end

open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label jLabel)
open RayFourExpansion (RayCharacter)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem firstCoreInputRow_smoothed_sign
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)) =
    ∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstCoreTest H V y negative t D) z‖ ^ 2) : ℂ) := by
  cases negative
  · rfl
  · simpa only [firstCoreInputRow, Bool.true_eq, ite_true, Equiv.neg_apply, map_neg, norm_neg] using
      (Equiv.neg O).tsum_eq (fun z : O => W (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖inputConjugateRow p hg (F \ D) (firstCoreTwist true χ Ψ r)
          (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (firstCoreTest H V y true t D) z‖ ^ 2) : ℂ))

theorem firstCoreInputRow_smoothed_second_poisson
    (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)) =
    ∑ G ∈ (F \ D).powerset, ∑ U ∈ ((F \ D) \ G).powerset, ∑ V' ∈ ((F \ D) \ G).powerset,
      if Disjoint U V' then
        overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
          (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (firstCoreTest H V y negative t D) G U V' *
          maskedSecondDual p hg hp hinj G U V' W Y
      else 0 := by
  rw [firstCoreInputRow_smoothed_sign]
  exact inputConjugateRow_smoothed_second_poisson p hg hp hinj hc (F \ D)
    (firstCoreTwist negative χ Ψ r) (m * b0Label p B v ε₁ ε₂)
    (c * jLabel p B v ε₁ ε₂) d (firstCoreTest H V y negative t D) W Y hY

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace JointLogSeparation

abbrev Frequency := ℝ × ℝ × ℝ

def tripleCoefficient (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (t : Frequency) : ℂ :=
  b₁ t.1 * (b₂ t.2.1 * b₃ t.2.2)

lemma tripleCoefficient_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) :
    Integrable (tripleCoefficient b₁ b₂ b₃) :=
  b₁.integrable.mul_prod (b₂.integrable.mul_prod b₃.integrable)

lemma tripleCoefficient_bounded_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (F : Frequency → ℂ) (hF : Continuous F) (M : ℝ) (hM : ∀ t, ‖F t‖ ≤ M) :
    Integrable (fun t => tripleCoefficient b₁ b₂ b₃ t * F t) :=
  (tripleCoefficient_integrable b₁ b₂ b₃).mul_bdd hF.aestronglyMeasurable
    (Filter.Eventually.of_forall hM)

lemma tripleCoefficient_norm_bounded_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (G : Frequency → ℝ) (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) :
    Integrable (fun t => ‖tripleCoefficient b₁ b₂ b₃ t‖ * G t) :=
  (tripleCoefficient_integrable b₁ b₂ b₃).norm.mul_bdd hG.aestronglyMeasurable
    (Filter.Eventually.of_forall hM)

lemma tripleCoefficient_slice_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (F : Frequency → ℂ) (hF : Continuous F) (M : ℝ) (hM : ∀ t, ‖F t‖ ≤ M) (x : ℝ) :
    Integrable (fun t : ℝ × ℝ => tripleCoefficient b₁ b₂ b₃ (x,t) * F (x,t)) := by
  have hc : Integrable (fun t : ℝ × ℝ => b₁ x * (b₂ t.1 * b₃ t.2)) :=
    (b₂.integrable.mul_prod b₃.integrable).const_mul (b₁ x)
  apply hc.mul_bdd
  · exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => hM (x,t))

lemma tripleCoefficient_norm_slice_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (G : Frequency → ℝ) (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) (x : ℝ) :
    Integrable (fun t : ℝ × ℝ => ‖tripleCoefficient b₁ b₂ b₃ (x,t)‖ * G (x,t)) := by
  have hc : Integrable (fun t : ℝ × ℝ => ‖b₁ x * (b₂ t.1 * b₃ t.2)‖) :=
    ((b₂.integrable.mul_prod b₃.integrable).const_mul (b₁ x)).norm
  apply hc.mul_bdd
  · exact (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => hM (x,t))

lemma nested_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Frequency → E) (hf : Integrable f)
    (hslice : ∀ x : ℝ, Integrable (fun yz : ℝ × ℝ => f (x,yz))) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, f (x,y,z)) = ∫ t : Frequency, f t := by
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), integral_prod _ hf]
  apply integral_congr_ae
  filter_upwards [] with x
  simpa only [Measure.volume_eq_prod] using (integral_prod _ (hslice x)).symm

theorem triple_integral_bound (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (F : Frequency → ℂ) (G : Frequency → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (D M : ℝ) (hD : 0 ≤ D) (hM : ∀ t, G t ≤ M)
    (hpoint : ∀ t, ‖F t‖ ≤ D * G t) :
    ‖∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) * F (t₁,t₂,t₃)‖ ≤
    D * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ * G (t₁,t₂,t₃)) := by
  have hFb : ∀ t, ‖F t‖ ≤ D * M := fun t => (hpoint t).trans (mul_le_mul_of_nonneg_left (hM t) hD)
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by simpa [Real.norm_of_nonneg (hG0 t)] using hM t
  have hfi := tripleCoefficient_bounded_integrable b₁ b₂ b₃ F hF (D*M) hFb
  have hgi := tripleCoefficient_norm_bounded_integrable b₁ b₂ b₃ G hG M hGb
  rw [nested_eq_integral _ hfi (tripleCoefficient_slice_integrable b₁ b₂ b₃ F hF (D*M) hFb),
    nested_eq_integral _ hgi (tripleCoefficient_norm_slice_integrable b₁ b₂ b₃ G hG M hGb)]
  calc
    _ ≤ ∫ t : Frequency, ‖tripleCoefficient b₁ b₂ b₃ t * F t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : Frequency, D * (‖tripleCoefficient b₁ b₂ b₃ t‖ * G t) := by
      apply integral_mono hfi.norm (hgi.const_mul D)
      intro t
      simp only [norm_mul]
      calc
        _ ≤ ‖tripleCoefficient b₁ b₂ b₃ t‖ * (D * G t) :=
          mul_le_mul_of_nonneg_left (hpoint t) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

end JointLogSeparation

namespace SecondPassIntegration
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open FirstPassCubeLabels (columnLog)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma fixedTest_continuous (V : ℝ → ℂ) (X : ℝ) (negative : Bool) (N : Finset ι)
    (τ σ : Frequency → ℝ) (hτ : Continuous τ) (hσ : Continuous σ) :
    Continuous (fun t => fixedSecondTest p V X (τ t) (σ t) negative N) := by
  have hh := (FourierBridge.logPhase_continuous_left (columnLog p X N)).comp (hτ.sub hσ)
  cases negative <;> simp only [fixedSecondTest, Bool.false_eq_true, ite_false, ite_true,
    fixedColumnTest] <;> fun_prop

lemma fixedColumn_norm_frequency (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X a b : ℝ)
    (negative : Bool) (N : Finset ι) :
    ‖secondChildColumn p hp hcop hg Ψ m f y (fixedSecondTest p V X a b negative) N‖ =
    ‖secondChildColumn p hp hcop hg Ψ m f y (fixedSecondTest p V X 0 0 negative) N‖ := by
  cases negative <;> simp only [secondChildColumn, fixedSecondTest, Bool.false_eq_true, ite_false,
    ite_true, fixedColumnTest, norm_mul, norm_star, FourierBridge.logPhase_norm]

lemma fixedRow_continuous (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X : ℝ)
    (negative : Bool) (τ σ : Frequency → ℝ) (hτ : Continuous τ) (hσ : Continuous σ) :
    Continuous (fun t => fixedChildRow p hp hcop hg F Ψ m
      (fixedSecondTest p V X (τ t) (σ t) negative) f y) := by
  unfold fixedChildRow
  apply continuous_finsetSum
  intro N hN
  have hh := fixedTest_continuous p V X negative N τ σ hτ hσ
  unfold secondChildColumn
  fun_prop

def rowMagnitude (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X : ℝ)
    (negative : Bool) : ℝ :=
  ∑ N ∈ F.powerset,
    ‖secondChildColumn p hp hcop hg Ψ m f y (fixedSecondTest p V X 0 0 negative) N‖

lemma rowMagnitude_nonneg (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X : ℝ)
    (negative : Bool) : 0 ≤ rowMagnitude p hp hcop hg F Ψ m f y V X negative := by
  unfold rowMagnitude
  positivity

lemma fixedRow_norm_le (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X a b : ℝ)
    (negative : Bool) :
    ‖fixedChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b negative) f y‖ ≤
      rowMagnitude p hp hcop hg F Ψ m f y V X negative := by
  unfold fixedChildRow rowMagnitude
  apply (norm_sum_le _ _).trans_eq
  exact Finset.sum_congr rfl (fun N hN => fixedColumn_norm_frequency p hp hcop hg Ψ m f y V X a b negative N)

def childEnergy (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) : ℝ :=
  ∑ u : Oˣ, ∑ z ∈ T,
    ‖idealChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b testNegative) rowNegative u z‖ ^ 2

def energyMagnitude (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) : ℝ :=
  ∑ u : Oˣ, ∑ z ∈ T,
    (rowMagnitude p hp hcop hg F Ψ m ((u : O) * ConcretePrimeRowBridge.idealGenerator z.1)
      (if rowNegative then -z.2 else z.2) V X testNegative) ^ 2

lemma childEnergy_nonneg (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) :
    0 ≤ childEnergy p hp hcop hg F Ψ m T V X testNegative rowNegative a b := by
  unfold childEnergy
  positivity

lemma childEnergy_le (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) :
    childEnergy p hp hcop hg F Ψ m T V X testNegative rowNegative a b ≤
      energyMagnitude p hp hcop hg F Ψ m T V X testNegative rowNegative := by
  unfold childEnergy energyMagnitude idealChildRow
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro z hz
  exact pow_le_pow_left₀ (norm_nonneg _) (fixedRow_norm_le p hp hcop hg F Ψ m _ _ V X a b testNegative) 2

lemma childEnergy_continuous (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool)
    (τ σ : Frequency → ℝ) (hτ : Continuous τ) (hσ : Continuous σ) :
    Continuous (fun t => childEnergy p hp hcop hg F Ψ m T V X testNegative rowNegative (τ t) (σ t)) := by
  unfold childEnergy
  apply continuous_finsetSum
  intro u hu
  apply continuous_finsetSum
  intro z hz
  unfold idealChildRow
  exact (fixedRow_continuous p hp hcop hg F Ψ m _ _ V X testNegative τ σ hτ hσ).norm.pow 2

end SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
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

theorem integrated_fixed_second_mode_transfer (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (T : Finset (Ideal O × O))
      (b0 : Ideal O) (w : Frequency → OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
      (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ T) →
      (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ q, ∀ x ∈ s, ‖w q x‖ ≤ B) → (∀ x ∈ s, Continuous (fun q => w q x)) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      ‖integratedSecondMode p hp hcop hg b₁ b₂ b₃ s w label F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂‖ ≤
        (B * C * (lengthScale * Ideal.absNorm b0)^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨C, hC, hb⟩ := fixed_second_mode_transfer p hp hcop hg ε hε
  refine ⟨C, hC, ?_⟩
  intro s T b0 w B lengthScale label F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ b₁ b₂ b₃ hb0 hB hL hv hm ht hn hw hwc hl
  let f : Frequency → ℂ := fun q => fixedSecondMode p hp hcop hg s (w q) label F Ψ₁ Ψ₂ m
    (fixedSecondTest p V₁ X₁ q.1 q.2.2 true) (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false)
  let G := childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false) *
    Real.sqrt (energyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀ q, G q ≤ M := by
    intro q
    dsimp [G, childGeometricMean, M]
    gcongr
    · exact childEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact childEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  have hf : Continuous f := by
    unfold f fixedSecondMode
    apply continuous_finsetSum
    intro x hx
    have hwx := hwc x hx
    have hc₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (label x) (newRow x) V₁ X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have hc₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (label x) (-newRow x) V₂ X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hwx.mul hc₁.star).mul hc₂
  have hpoint : ∀ q, ‖f q‖ ≤ (B * C * (lengthScale * Ideal.absNorm b0)^ε) * G q := by
    intro q
    have hh := hb s T b0 (w q) B lengthScale label F Ψ₁ Ψ₂ m
      (fixedSecondTest p V₁ X₁ q.1 q.2.2 true) (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false)
      hb0 hB hL hv hm ht hn (hw q) hl
    simpa only [f, G, childGeometricMean, childEnergy, mul_assoc] using hh
  exact triple_integral_bound b₁ b₂ b₃ f G hf hG hG0
    (B * C * (lengthScale * Ideal.absNorm b0)^ε) M (by positivity) hM hpoint

end SecondPassIntegration

end

end OAI

end


