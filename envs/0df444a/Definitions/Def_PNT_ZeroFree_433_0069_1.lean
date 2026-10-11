-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0069_1
-- name    : PNT_ZeroFree_433_0069_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T20:50:09.22601+00:00
-- url     : https://prove2.me/theorems/97879bdb-bd0a-402f-a2a1-d2844ade3b2b
-- title:
--   Zero-free region foundations: Poisson.QuadraticProfiles [0069_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Poisson.QuadraticProfiles
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/QuadraticProfiles.lean#L78-L350

import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0068

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/QuadraticProfiles.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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

open scoped BigOperators Classical SchwartzMap FourierTransform
namespace EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcreteTraceCRT

def quadraticSquareProfileCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℝ
    (show (fun x : ℝ => x ^ 2).HasTemperateGrowth by fun_prop)
    ⟨1, 1, fun x => by
      simp only [pow_one, one_mul, norm_pow]
      nlinarith [sq_nonneg (‖x‖ - 1)]⟩

@[simp] theorem quadraticSquareProfileCLM_apply (W : 𝓢(ℝ, ℂ)) :
    quadraticSquareProfileCLM W = quadraticSquareProfile W := by
  ext x
  rw [quadraticSquareProfile_apply]
  rfl

def realAxisProfileCLM : 𝓢(ℂ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℝ
    (show (fun x : ℝ => (x : ℂ)).HasTemperateGrowth by fun_prop)
    ⟨1, 1, fun x => by simp only [pow_one, one_mul, Complex.norm_real]; linarith⟩

@[simp] theorem realAxisProfileCLM_apply (f : 𝓢(ℂ, ℂ)) :
    realAxisProfileCLM f = horizontalSlice f 0 := by
  ext x
  simp only [realAxisProfileCLM, SchwartzMap.compCLM_apply, Function.comp_apply,
    horizontalSlice_apply, complexPoint_eq, Complex.ofReal_zero, mul_zero, add_zero]

def squareFrequencyScaleCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (2 / Real.sqrt 3) (by positivity)))).restrictScalars ℝ

def quadraticTransformedSquareProfileCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) •
    squareFrequencyScaleCLM.comp (realAxisProfileCLM.comp radialFourierCLM)

@[simp] theorem quadraticTransformedSquareProfileCLM_apply (W : 𝓢(ℝ, ℂ)) :
    quadraticTransformedSquareProfileCLM W = quadraticTransformedSquareProfile W := by
  simp only [quadraticTransformedSquareProfileCLM, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, radialFourierCLM_apply, realAxisProfileCLM_apply,
    squareFrequencyScaleCLM, quadraticTransformedSquareProfile]
  rfl

theorem two_profile_seminorm_control
    (T₁ T₂ : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (s : Finset (ℕ × ℕ)) :
    ∃ (t : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (T₁ W) +
        s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (T₂ W) ≤
          C * t.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨t₁, C₁, hC₁, h₁⟩ := schwartzCLM_finite_seminorm_control T₁ s
  obtain ⟨t₂, C₂, hC₂, h₂⟩ := schwartzCLM_finite_seminorm_control T₂ s
  refine ⟨t₁ ∪ t₂, C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro W
  have ht₁ : t₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ≤
      (t₁ ∪ t₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) := Finset.sup_mono Finset.subset_union_left
  have ht₂ : t₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) ≤
      (t₁ ∪ t₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) := Finset.sup_mono Finset.subset_union_right
  have hb₁ := (h₁ W).trans (mul_le_mul_of_nonneg_left (Seminorm.le_def.mp ht₁ W) hC₁.le)
  have hb₂ := (h₂ W).trans (mul_le_mul_of_nonneg_left (Seminorm.le_def.mp ht₂ W) hC₂.le)
  nlinarith

theorem quadratic_principal_difference_large_scale (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) ≤ M →
        ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
          (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by
  obtain ⟨t, C₀, hC₀, hrem⟩ := maskedPrincipalRemainder_large_scale A
  obtain ⟨s, C₁, hC₁, hctrl⟩ := two_profile_seminorm_control
    quadraticTransformedSquareProfileCLM quadraticSquareProfileCLM t
  refine ⟨s, C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro α _ P _ hinj S W M hM hsize
  have hbound := hctrl W
  simp only [quadraticTransformedSquareProfileCLM_apply, quadraticSquareProfileCLM_apply] at hbound
  have h₁ := hrem P S (quadraticTransformedSquareProfile W) M hM hsize
  have h₂ := hrem P S (quadraticSquareProfile W) M hM hsize
  rw [quadratic_square_poisson_main_cancel P hinj S W M hM]
  calc
    _ ≤ ‖maskedPrincipalRemainder P S (quadraticTransformedSquareProfile W) M‖ +
        ‖maskedPrincipalRemainder P S (quadraticSquareProfile W) M‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ S.card * (C₀ * t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)) *
          ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A +
        (2 : ℝ) ^ S.card * (C₀ * t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) *
          ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := add_le_add h₁ h₂
    _ = (2 : ℝ) ^ S.card * C₀ *
        (t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W) +
          t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) *
          ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by ring
    _ ≤ (2 : ℝ) ^ S.card * C₀ *
        (C₁ * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
          ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by
      gcongr
    _ = _ := by ring

open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound

theorem paperRadialFourier_nonzero_sum_uniform (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    K * ‖∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖ ≤
      pvControl W := by
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  have he : (∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)) =
      ∑' h : {h : O // h ≠ 0}, paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2) := by
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
      intro h hh hz
      subst h
      exact hh (by simp))]
    apply tsum_congr
    intro h
    simp only [if_neg h.property]
  rw [he]
  exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hs.subtype _)) hK.le).trans
    (pv_lattice_bound W K hK)

theorem maskedPrincipalRemainder_uniform {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖maskedPrincipalRemainder P S W M‖ ≤ (2 : ℝ) ^ S.card * pvControl W := by
  let n := fun E : Finset α => (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)
  have hn (E : Finset α) : 0 < n E := by
    dsimp [n]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  let f := fun E : Finset α =>
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)
  have hf (E : Finset α) : M * ‖f E‖ ≤ pvControl W := by
    have ht := paperRadialFourier_nonzero_sum_uniform W (M / n E) (div_pos hM (hn E))
    have he (h : O) : M / n E * ‖eisEmbedding h‖ ^ 2 = M * ‖eisEmbedding h‖ ^ 2 / n E := by ring
    simp only [he] at ht
    have hm := norm_ideal_moebius_le_one (∏ i ∈ E, P i)
    dsimp only [f]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    calc
      _ = ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ)‖ *
          ((M / n E) * ‖∑' h : O, if h = 0 then 0 else
            paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)‖) := by dsimp [n]; ring
      _ ≤ 1 * pvControl W := mul_le_mul hm ht (by positivity) zero_le_one
      _ = _ := one_mul _
  change ‖(M : ℂ) * ∑ E ∈ S.powerset, f E‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  calc
    _ ≤ M * ∑ E ∈ S.powerset, ‖f E‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hM.le
    _ = ∑ E ∈ S.powerset, M * ‖f E‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ E ∈ S.powerset, pvControl W := Finset.sum_le_sum (fun E _ => hf E)
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem quadratic_principal_difference_uniform :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
          (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s, C, hC, hb⟩ := two_profile_seminorm_control
    quadraticTransformedSquareProfileCLM quadraticSquareProfileCLM pvSeminorms
  refine ⟨s, pvConstant * C, mul_pos pvConstant_pos hC, ?_⟩
  intro α _ P _ hinj S W M hM
  have hbound := hb W
  simp only [quadraticTransformedSquareProfileCLM_apply, quadraticSquareProfileCLM_apply] at hbound
  rw [quadratic_square_poisson_main_cancel P hinj S W M hM]
  calc
    _ ≤ ‖maskedPrincipalRemainder P S (quadraticTransformedSquareProfile W) M‖ +
        ‖maskedPrincipalRemainder P S (quadraticSquareProfile W) M‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ S.card * pvControl (quadraticTransformedSquareProfile W) +
        (2 : ℝ) ^ S.card * pvControl (quadraticSquareProfile W) :=
      add_le_add (maskedPrincipalRemainder_uniform P S _ M hM) (maskedPrincipalRemainder_uniform P S _ M hM)
    _ = (2 : ℝ) ^ S.card * pvConstant *
        (pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W) +
          pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) := by unfold pvControl; ring
    _ ≤ (2 : ℝ) ^ S.card * pvConstant * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
      exact mul_le_mul_of_nonneg_left hbound (mul_nonneg (by positivity) pvConstant_pos.le)
    _ = _ := by ring

theorem two_regime_decay (A : ℕ) (f B₀ B₁ M N : ℝ)
    (_hf : 0 ≤ f) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hM : 0 < M) (hN : 0 < N)
    (hsmall : f ≤ B₀) (hlarge : N ≤ M → f ≤ B₁ * (N / M) ^ A) :
    f ≤ (2 : ℝ) ^ A * (B₀ + B₁) / (1 + M / N) ^ A := by
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + M / N) A)).mpr
  by_cases hMN : M ≤ N
  · have hratio : M / N ≤ 1 := (div_le_one hN).mpr hMN
    have hp : (1 + M / N) ^ A ≤ (2 : ℝ) ^ A :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      _ ≤ B₀ * (2 : ℝ) ^ A := mul_le_mul hsmall hp (by positivity) hB₀
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) A]
  · have hNM : N ≤ M := le_of_not_ge hMN
    have hratio : N / M ≤ 1 := (div_le_one hM).mpr hNM
    have hp : (1 + N / M) ^ A ≤ (2 : ℝ) ^ A :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have he : N / M * (1 + M / N) = 1 + N / M := by field_simp; ring
    calc
      _ ≤ (B₁ * (N / M) ^ A) * (1 + M / N) ^ A :=
        mul_le_mul_of_nonneg_right (hlarge hNM) (by positivity)
      _ = B₁ * (1 + N / M) ^ A := by rw [mul_assoc, ← mul_pow, he]
      _ ≤ B₁ * (2 : ℝ) ^ A := mul_le_mul_of_nonneg_left hp hB₁
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) A]

theorem quadratic_principal_difference_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
          (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            (1 + M / (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)) ^ A := by
  obtain ⟨s₀, C₀, hC₀, h₀⟩ := quadratic_principal_difference_uniform
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := quadratic_principal_difference_large_scale A
  refine ⟨s₀ ∪ s₁, (2 : ℝ) ^ A * (C₀ + C₁), by positivity, ?_⟩
  intro α _ P _ hinj S W M hM
  let N := (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)
  let Q := (s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let d := (2 : ℝ) ^ S.card
  let deltaLoss := ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
    (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖
  have hN : 0 < N := by
    dsimp [N]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P S)))
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hd : 0 ≤ d := by positivity
  have hq₀ : s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W
  have hq₁ : s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W
  have hb₀ : deltaLoss ≤ d * (C₀ * Q) := by
    apply (h₀ P hinj S W M hM).trans
    dsimp only [d]
    gcongr
  have hb₁ : N ≤ M → deltaLoss ≤ d * (C₁ * Q) * (N / M) ^ A := by
    intro hsize
    apply (h₁ P hinj S W M hM hsize).trans
    dsimp only [d, N]
    gcongr
  have h := two_regime_decay A deltaLoss (d * (C₀ * Q)) (d * (C₁ * Q)) M N
    (norm_nonneg _) (by positivity) (by positivity) hM hN hb₀ hb₁
  calc
    _ = deltaLoss := rfl
    _ ≤ (2 : ℝ) ^ A * (d * (C₀ * Q) + d * (C₁ * Q)) / (1 + M / N) ^ A := h
    _ = _ := by dsimp [d, N, Q]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic MixedCrossSeparation FirstCauchyArithmetic RayFourExpansion

theorem supportRay_star {ι : Type*} (p : ι → ActualEisensteinCubic.O) (χ : RayCharacter) (S : Finset ι) :
    supportRay p (star χ) S = star (supportRay p χ S) := by
  simp only [supportRay, rayCharacter, MulChar.star_apply]

theorem supportRay_mul {ι : Type*} (p : ι → ActualEisensteinCubic.O) (χ η : RayCharacter) (S : Finset ι) :
    supportRay p (χ * η) S = supportRay p χ S * supportRay p η S := by
  simp only [supportRay, rayCharacter, MulChar.mul_apply]

theorem columnG_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    columnG p hp hcop hg S = ∑ χ : RayCharacter, gCoeff χ * supportRay p χ S := by
  have h := canonicalProductG_character_expansion (fun i : S => p i.val)
    (fun i => hp i.val) (columnPrimeCoprime p hcop S) (fun i => hg i.val)
    (fun i => hc i.val) (fun i => hpr i.val)
  simpa only [columnG, supportRay, Finset.prod_coe_sort] using h

def coreRayCharacter (negative : Bool) (χ ξ : RayCharacter) : RayCharacter :=
  (if negative then star χ else χ) * ξ

def coreRayCoefficient {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) : ℂ :=
  (if negative then star (crossCoeff χ η * supportRay p η F)
    else crossCoeff χ η * supportRay p η F) * gCoeff ξ


end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)


end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportConjugateSum)
open RayFourExpansion (RayCharacter crossCoeff)

section FixedColumn
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
  (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
  (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)


end FixedColumn


end FirstPassCubeLabels

end

end OAI

end


