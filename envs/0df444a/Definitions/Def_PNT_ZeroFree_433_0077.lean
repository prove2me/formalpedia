-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0077
-- name    : PNT_ZeroFree_433_0077
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T21:23:17.443345+00:00
-- url     : https://prove2.me/theorems/36ebf609-d6b1-4e08-9726-c7919d324b99
-- title:
--   Zero-free region foundations: Poisson.PrincipalTruncation, RSPhaseCompat [0077]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation
--   - RSPhaseCompat
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/PrincipalTruncation.lean#L79-L682
--   Locally proved Lean 4.33.1 compatibility lemmas: RSPhaseCompat.lean#L11-L33

import Definitions.Def_PNT_ZeroFree_433_0076
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/PrincipalTruncation.lean#L79-L682
Locally proved Lean 4.33.1 compatibility lemmas: RSPhaseCompat.lean#L11-L33
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation
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

open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

theorem mem_rowNormDisk_floor {lengthScale : ℝ} (hL : 0 ≤ lengthScale) (z : O) :
    z ∈ rowNormDisk ⌊lengthScale⌋₊ ↔ z ≠ 0 ∧ ‖eisEmbedding z‖ ^ 2 ≤ lengthScale := by
  rw [mem_rowNormDisk]
  constructor
  · rintro ⟨hp, hN⟩
    refine ⟨?_, ?_⟩
    · intro hz
      subst z
      simp at hp
    · rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hL)
  · rintro ⟨hz, hN⟩
    have hp := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hz))
    rw [eisEmbedding_norm_sq_eq_absNorm_span] at hp hN
    exact ⟨by exact_mod_cast hp, Nat.le_floor hN⟩

theorem dualNear_eq_finite (W : ℝ → ℂ) (X lengthScale : ℝ) (hL : 0 ≤ lengthScale) :
    dualNear W X lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2) := by
  unfold dualNear
  rw [tsum_eq_sum (s := rowNormDisk ⌊lengthScale⌋₊) (fun h hh => ?_)]
  · apply Finset.sum_congr rfl
    intro h hh
    have hd := (mem_rowNormDisk_floor hL h).mp hh
    simp only [if_pos hd.2, if_neg hd.1]
  · by_cases hz : h = 0
    · simp [hz]
    · have hn : ¬ ‖eisEmbedding h‖ ^ 2 ≤ lengthScale := fun hn => hh ((mem_rowNormDisk_floor hL h).mpr ⟨hz, hn⟩)
      simp only [if_neg hn]

theorem dualFar_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K lengthScale : ℝ), 0 < K → 0 ≤ lengthScale →
        ‖dualFar W K lengthScale‖ ≤ (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + K * lengthScale) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K lengthScale hK hL
  have he : dualFar W K lengthScale =
      ∑' h : {h : O // lengthScale < ‖eisEmbedding h‖ ^ 2}, paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2) := by
    unfold dualFar
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | lengthScale < ‖eisEmbedding h‖ ^ 2}) (by
      intro h hh
      by_contra hn
      change ¬ lengthScale < ‖eisEmbedding h‖ ^ 2 at hn
      exact hh (by simp only [if_neg hn]))]
    apply tsum_congr
    intro h
    have hqh : lengthScale < ‖eisEmbedding h.val‖ ^ 2 := h.property
    have hz : h.val ≠ 0 := by
      intro hz
      have hp := hqh
      simp only [hz, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hp
      linarith
    simp only [if_pos hqh, if_neg hz]
  rw [he]
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  let f : {h : O // lengthScale < ‖eisEmbedding h‖ ^ 2} →
      {h : O // K * lengthScale ≤ K * ‖eisEmbedding h‖ ^ 2} :=
    fun h => ⟨h.val, mul_le_mul_of_nonneg_left h.property.le hK.le⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {h : O // K * lengthScale ≤ K * ‖eisEmbedding h‖ ^ 2} => z.val) hab)
  have hi : (∑' h : {h : O // lengthScale < ‖eisEmbedding h‖ ^ 2},
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
      ∑' h : {h : O // K * lengthScale ≤ K * ‖eisEmbedding h‖ ^ 2},
        ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
    (hs.subtype _).tsum_le_tsum_of_inj f hf (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype _)
  exact (norm_tsum_le_tsum_norm (hs.subtype _)).trans (hi.trans (hb W K (K * lengthScale) hK (mul_nonneg hK.le hL)))

end

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem middle_divisor_frequency_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ Z → 0 ≤ lengthScale →
        ‖(X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
          (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale‖ ≤
          (2 : ℝ) ^ S.card * (X / Y) * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := dualFar_decay A
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Y Z lengthScale hX hY hYZ hL
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let Q := (min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 < Z := hY.trans_le hYZ
  have hQ : 0 < Q := by dsimp [Q]; positivity
  rw [Finset.mul_sum]
  have hf (E : Finset ι) (hE : E ∈ middleDivisors P S Y Z) :
      ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) *
        dualFar W (X / subsetNorm P E) lengthScale)‖ ≤ (X / Y) * (B / Q) := by
    have hn := subsetNorm_pos P E
    have hEY : Y < subsetNorm P E := (Finset.mem_filter.mp hE).2
    have hEZ : subsetNorm P E ≤ Z := (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).2
    have hk : X / Z ≤ X / subsetNorm P E := div_le_div_of_nonneg_left hX.le hn hEZ
    have hden : Q ≤ (min 1 (X / subsetNorm P E)) ^ 2 *
        (1 + (X / subsetNorm P E) * lengthScale) ^ A := by
      dsimp [Q]
      have hmul : X * lengthScale / Z ≤ (X / subsetNorm P E) * lengthScale := by
        calc
          _ = (X / Z) * lengthScale := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hk hL
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) (min_le_min_left _ hk) 2
      · exact pow_le_pow_left₀ (by positivity) (by linarith) A
      · positivity
      · positivity
    have hh : ‖dualFar W (X / subsetNorm P E) lengthScale‖ ≤ B / Q :=
      (hb W _ lengthScale (div_pos hX hn) hL).trans (div_le_div_of_nonneg_left hB hQ hden)
    calc
      _ = (X / subsetNorm P E) * ‖subsetMobius P E‖ * ‖dualFar W (X / subsetNorm P E) lengthScale‖ := by
        simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hX, abs_of_pos hn]
        ring
      _ ≤ (X / Y) * 1 * (B / Q) := by
        apply mul_le_mul
        · exact mul_le_mul (div_le_div_of_nonneg_left hX.le hY hEY.le)
            (subsetMobius_norm_le_one P E) (norm_nonneg _) (by positivity)
        · exact hh
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  calc
    _ ≤ ∑ E ∈ middleDivisors P S Y Z,
        ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale)‖ := norm_sum_le _ _
    _ ≤ ∑ E ∈ middleDivisors P S Y Z, (X / Y) * (B / Q) := Finset.sum_le_sum hf
    _ = ((middleDivisors P S Y Z).card : ℝ) * ((X / Y) * (B / Q)) := by simp
    _ ≤ (2 : ℝ) ^ S.card * ((X / Y) * (B / Q)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hsub : middleDivisors P S Y Z ⊆ S.powerset :=
        (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_powerset] at hc
      exact_mod_cast hc
    _ = _ := by dsimp [B, Q]; ring

end

local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

def principalTruncation {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Z : ℝ) : ℂ :=
  (X : ℂ) * paperRadialFourier W 0 * (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
  (X : ℂ) * paperRadialFourier W 0 *
    (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
  W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E)

def middleTruncation {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
    (subsetMobius P E / (subsetNorm P E : ℂ)) *
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, paperRadialFourier W ((X / subsetNorm P E) * ‖eisEmbedding h‖ ^ 2)

def truncationError {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (∑' z : O, rowCoprimeMask P S z * (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) -
    (principalTruncation P S W X Z + middleTruncation P S W X Y Z lengthScale)

theorem truncationError_eq {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ) (hX : 0 < X) (hYZ : Y ≤ Z) (hL : 0 ≤ lengthScale) :
    truncationError P S W X Y Z lengthScale =
      (X : ℂ) * (∑ E ∈ smallDivisors P S Y,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  unfold truncationError principalTruncation middleTruncation
  rw [masked_radialSource_five_pieces P hinj S W X Y Z lengthScale hX hYZ]
  simp_rw [dualNear_eq_finite W _ lengthScale hL]
  ring

theorem truncationError_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ X → X ≤ Z → 0 ≤ lengthScale →
        ‖truncationError P S W X Y Z lengthScale‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Y / X) ^ A + (1 / (1 + Z / X) ^ A) +
              (X / Y) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A)) := by
  obtain ⟨s₀, C₀, hC₀, h₀⟩ := small_divisor_dual_tail A
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := large_divisor_source_tail A
  obtain ⟨s₂, C₂, hC₂, h₂⟩ := middle_divisor_frequency_tail A
  refine ⟨(s₀ ∪ s₁) ∪ s₂, C₀ + C₁ + C₂, by positivity, ?_⟩
  intro ι _ P _ hinj S W X Y Z lengthScale hX hY hYX hXZ hL
  let Q := ((s₀ ∪ s₁) ∪ s₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let C := C₀ + C₁ + C₂
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hc₀ : C₀ ≤ C := by dsimp [C]; linarith
  have hc₁ : C₁ ≤ C := by dsimp [C]; linarith
  have hc₂ : C₂ ≤ C := by dsimp [C]; linarith
  have hq₀ : s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left.trans Finset.subset_union_left)) W
  have hq₁ : s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right.trans Finset.subset_union_left)) W
  have hq₂ : s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W
  have hz : 0 < Z := hX.trans_le hXZ
  let lo : ℂ := (X : ℂ) * ∑ E ∈ smallDivisors P S Y,
    (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)
  let mid : ℂ := (X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
    (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale
  let hi : ℂ := ∑ E ∈ largeDivisors P S Z,
    subsetMobius P E * radialSource W (X / subsetNorm P E)
  have hlo : ‖lo‖ ≤ (2 : ℝ) ^ S.card * (C * Q) * (Y / X) ^ A := by
    apply (h₀ P S W X Y hX hY.le hYX).trans
    gcongr
  have hhi : ‖hi‖ ≤ (2 : ℝ) ^ S.card * (C * Q) / (1 + Z / X) ^ A := by
    apply (h₁ P S W X Z hX hXZ).trans
    gcongr
  have hmid : ‖mid‖ ≤ (2 : ℝ) ^ S.card * (X / Y) * (C * Q) /
      ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) := by
    apply (h₂ P S W X Y Z lengthScale hX hY (hYX.trans hXZ) hL).trans
    gcongr
  rw [truncationError_eq P hinj S W X Y Z lengthScale hX (hYX.trans hXZ) hL]
  change ‖lo + mid + hi‖ ≤ _
  calc
    _ ≤ ‖lo‖ + ‖mid‖ + ‖hi‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le lo mid) le_rfl)
    _ ≤ (2 : ℝ) ^ S.card * (C * Q) * (Y / X) ^ A +
        (2 : ℝ) ^ S.card * (X / Y) * (C * Q) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) +
        (2 : ℝ) ^ S.card * (C * Q) / (1 + Z / X) ^ A := add_le_add (add_le_add hlo hmid) hhi
    _ = _ := by change _ = (2 : ℝ) ^ S.card * (C * Q) * _; ring

end TruncatedPrincipalPoisson

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

section
open FourierBridge FirstPassCubeLabels

lemma schwartz_phase_inversion (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    g x = ∫ t : ℝ, logPhase t x * (𝓕 g) t := by
  simpa only [logPhase, Real.inner_apply, mul_assoc, mul_comm, mul_left_comm] using
    FourierBridge.schwartz_log_inversion g x

lemma product_three_integrals (f g h : ℝ → ℂ) :
    (∫ t, f t) * (∫ t, g t) * (∫ t, h t) =
      ∫ t₁, ∫ t₂, ∫ t₃, f t₁ * g t₂ * h t₃ := by
  simp_rw [integral_const_mul, integral_mul_const]
  simp_rw [integral_const_mul, integral_mul_const]

def profileSourceBound (g : 𝓢(ℝ, ℂ)) (J : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (J + 1),
    ((SchwartzMap.seminorm ℝ 0 i) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)

lemma profileSourceBound_nonneg (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    0 ≤ profileSourceBound g J := by
  unfold profileSourceBound
  positivity

lemma source_le_profileSourceBound (g : 𝓢(ℝ, ℂ)) (J i : ℕ) (hi : i ≤ J) :
    (SchwartzMap.seminorm ℝ 0 i) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g ≤
      profileSourceBound g J := by
  unfold profileSourceBound
  apply Finset.single_le_sum (s := Finset.range (J + 1)) (a := i)
    (f := fun k : ℕ => (SchwartzMap.seminorm ℝ 0 k) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower k) g)
  · intro j hj
    positivity
  · exact Finset.mem_range.mpr (by omega)

lemma profile_fourier_envelope (g : 𝓢(ℝ, ℂ)) (J : ℕ) (t : ℝ) :
    ‖(𝓕 g) t‖ ≤ fourierPointBound (J + 2) (profileSourceBound g (J + 2)) *
      firstLogDensity J t := by
  have h := uniform_fourier_pointwise g (J + 2) 1 (profileSourceBound g (J + 2))
    (by norm_num) (profileSourceBound_nonneg g _)
    (fun i hi => by simpa using source_le_profileSourceBound g (J + 2) i hi) t
  rw [firstLogDensity, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t‖) (J + 2))).mpr
  simpa only [one_mul, mul_comm] using h

theorem joint_separation_identity
    (A₁ A₂ : 𝓢(ℝ, ℂ)) (b : 𝓢(ℝ, ℂ)) (P F : ℂ) (s₁ s₂ s₃ : ℝ)
    (hr : P * F = ∫ t : ℝ, P * logPhase t s₃ * b t) :
    P * A₁ s₁ * A₂ s₂ * F =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        P * logPhase t₁ s₁ * logPhase t₂ s₂ * logPhase t₃ s₃ *
          ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by
  calc
    _ = A₁ s₁ * A₂ s₂ * (P * F) := by ring
    _ = (∫ t : ℝ, logPhase t s₁ * (𝓕 A₁) t) *
        (∫ t : ℝ, logPhase t s₂ * (𝓕 A₂) t) *
        (∫ t : ℝ, P * logPhase t s₃ * b t) := by
      rw [← schwartz_phase_inversion, ← schwartz_phase_inversion, ← hr]
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        (logPhase t₁ s₁ * (𝓕 A₁) t₁) * (logPhase t₂ s₂ * (𝓕 A₂) t₂) *
          (P * logPhase t₃ s₃ * b t₃) := by
      exact product_three_integrals
        (fun t : ℝ => logPhase t s₁ * (𝓕 A₁) t)
        (fun t : ℝ => logPhase t s₂ * (𝓕 A₂) t)
        (fun t : ℝ => P * logPhase t s₃ * b t)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      ring

theorem joint_separation_envelope {ι : Type*} [Fintype ι]
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ a₃ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ j, V j (y j)) * A₁ (∑ j, a₁ j * y j) * A₂ (∑ j, a₂ j * y j) *
          EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp (∑ j, a₃ j * y j)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          (∏ j, V j (y j)) * logPhase t₁ (∑ j, a₁ j * y j) *
            logPhase t₂ (∑ j, a₂ j * y j) * logPhase t₃ (∑ j, a₃ j * y j) *
            ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  classical
  obtain ⟨C₃, hC₃, hsep⟩ := EisensteinSchwartzPoisson.paperRadialFourier_log_separation_envelope
    W V a₃ M hM hV A (J + 2)
  let C₁ := fourierPointBound (J + 2) (profileSourceBound A₁ (J + 2))
  let C₂ := fourierPointBound (J + 2) (profileSourceBound A₂ (J + 2))
  have hC₁ : 0 ≤ C₁ := fourierPointBound_nonneg _ _ (profileSourceBound_nonneg _ _)
  have hC₂ : 0 ≤ C₂ := fourierPointBound_nonneg _ _ (profileSourceBound_nonneg _ _)
  refine ⟨C₁ * C₂ * C₃, by positivity, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, _, hpoint⟩ := hsep R hR
  refine ⟨b, ?_, ?_, AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J |>.congr ?_⟩
  · intro y
    let P : ℂ := ∏ j, V j (y j)
    let s₁ : ℝ := ∑ j, a₁ j * y j
    let s₂ : ℝ := ∑ j, a₂ j * y j
    let s₃ : ℝ := ∑ j, a₃ j * y j
    have hr : P * EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp s₃) =
        ∫ t, P * logPhase t s₃ * b t := by
      have hh := hb y
      simpa only [Finset.prod_mul_distrib, ← logPhase_sum, P, s₃] using hh
    exact joint_separation_identity A₁ A₂ b P
      (EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp s₃)) s₁ s₂ s₃ hr
  · intro t₁ t₂ t₃
    have hb₃ : (1 + R) ^ A * ‖b t₃‖ ≤ C₃ * firstLogDensity J t₃ := by
      rw [firstLogDensity, ← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t₃‖) (J + 2))).mpr
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hpoint t₃
    have h₁ := profile_fourier_envelope A₁ J t₁
    have h₂ := profile_fourier_envelope A₂ J t₂
    simp only [norm_mul]
    calc
      _ = ‖(𝓕 A₁) t₁‖ * ‖(𝓕 A₂) t₂‖ * ((1 + R)^A * ‖b t₃‖) := by ring
      _ ≤ (C₁ * firstLogDensity J t₁) * (C₂ * firstLogDensity J t₂) * (C₃ * firstLogDensity J t₃) := by
        exact mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) (mul_nonneg hC₁ (firstLogDensity_nonneg _ _))) hb₃ (by positivity)
          (mul_nonneg (mul_nonneg hC₁ (firstLogDensity_nonneg _ _))
            (mul_nonneg hC₂ (firstLogDensity_nonneg _ _)))
      _ = _ := by ring
  · filter_upwards [] with t
    simp

lemma seven_phase_factor (z ud ue uv kap x₁ x₂ t₁ t₂ t₃ : ℝ) :
    logPhase t₁ (z + x₁) * logPhase t₂ (z + x₂) *
      logPhase t₃ (kap - ud - 2 * ue - 2 * uv - x₁ - x₂) =
    logPhase (t₁ + t₂) z * logPhase t₃ (kap - ud - 2 * ue - 2 * uv) *
      logPhase (t₁ - t₃) x₁ * logPhase (t₂ - t₃) x₂ := by
  unfold logPhase
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

def outerWindow (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : ℝ) : ℂ :=
  V 0 z * V 1 ud * V 2 ue * V 3 uv * V 4 kap

def fixedColumnTest (V : ℝ → ℂ) (t : ℝ) (x : ℝ) : ℂ := V x * logPhase t x

theorem seven_kernel_separation (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ z ud ue uv kap x₁ x₂ : ℝ,
        outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂ * A₁ (z + x₁) * A₂ (z + x₂) *
          EisensteinSchwartzPoisson.paperRadialFourier W
            (R * Real.exp (kap - ud - 2 * ue - 2 * uv - x₁ - x₂)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          outerWindow V z ud ue uv kap * logPhase (t₁ + t₂) z *
            logPhase t₃ (kap - ud - 2 * ue - 2 * uv) *
            fixedColumnTest (V 5) (t₁ - t₃) x₁ * fixedColumnTest (V 6) (t₂ - t₃) x₂ *
            ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  let a₁ : Fin 7 → ℝ := ![1, 0, 0, 0, 0, 1, 0]
  let a₂ : Fin 7 → ℝ := ![1, 0, 0, 0, 0, 0, 1]
  let a₃ : Fin 7 → ℝ := ![0, -1, -2, -2, 1, -1, -1]
  obtain ⟨C, hC, hsep⟩ := joint_separation_envelope A₁ A₂ W V a₁ a₂ a₃ M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hpoint, hint⟩ := hsep R hR
  refine ⟨b, ?_, hpoint, hint⟩
  intro z ud ue uv kap x₁ x₂
  let y : Fin 7 → ℝ := ![z, ud, ue, uv, kap, x₁, x₂]
  have h₁ : (∑ j, a₁ j * y j) = z + x₁ := by
    simp [a₁, y, Fin.sum_univ_succ]
  have h₂ : (∑ j, a₂ j * y j) = z + x₂ := by
    simp [a₂, y, Fin.sum_univ_succ]
  have h₃ : (∑ j, a₃ j * y j) = kap - ud - 2 * ue - 2 * uv - x₁ - x₂ := by
    simp [a₃, y, Fin.sum_univ_succ]
    ring
  have hp : (∏ j, V j (y j)) = outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂ := by
    simp [outerWindow, y, Fin.prod_univ_succ, mul_assoc]
  have h := hb y
  rw [h₁, h₂, h₃, hp] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with t₁
  apply integral_congr_ae
  filter_upwards [] with t₂
  apply integral_congr_ae
  filter_upwards [] with t₃
  have heq := seven_phase_factor z ud ue uv kap x₁ x₂ t₁ t₂ t₃
  unfold fixedColumnTest
  calc
    _ = (outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂) *
      (logPhase t₁ (z + x₁) * logPhase t₂ (z + x₂) *
      logPhase t₃ (kap - ud - 2 * ue - 2 * uv - x₁ - x₂)) *
      ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by ring
    _ = _ := by rw [heq]; ring

end

open FirstPassCubeLabels

lemma weighted_schwartz_integrable (b : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  simpa using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J

lemma density_weight_identity (J : ℕ) (t : ℝ) :
    (1 + ‖t‖) ^ J * firstLogDensity J t = firstLogDensity 0 t := by
  have ht : 1 + ‖t‖ ≠ 0 := ne_of_gt (by positivity)
  simp only [firstLogDensity, zero_add, pow_add, mul_inv_rev]
  field_simp

lemma triple_product_integral_bound (f₁ f₂ f₃ g₁ g₂ g₃ : ℝ → ℝ)
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (hf₃ : Integrable f₃)
    (hg₁ : Integrable g₁) (hg₂ : Integrable g₂) (hg₃ : Integrable g₃)
    (S C : ℝ) (hpoint : ∀ x y z, S * f₁ x * f₂ y * f₃ z ≤ C * g₁ x * g₂ y * g₃ z) :
    S * (∫ x, f₁ x) * (∫ y, f₂ y) * (∫ z, f₃ z) ≤
      C * (∫ x, g₁ x) * (∫ y, g₂ y) * (∫ z, g₃ z) := by
  have hi₃ (x y : ℝ) := integral_mono (hf₃.const_mul (S * f₁ x * f₂ y))
    (hg₃.const_mul (C * g₁ x * g₂ y)) (hpoint x y)
  simp only [integral_const_mul] at hi₃
  have hi₂ (x : ℝ) := integral_mono
    ((hf₂.const_mul (S * f₁ x)).mul_const (∫ z, f₃ z))
    ((hg₂.const_mul (C * g₁ x)).mul_const (∫ z, g₃ z)) (hi₃ x)
  simp only [integral_const_mul, integral_mul_const] at hi₂
  have hi₁ := integral_mono
    (((hf₁.const_mul S).mul_const (∫ y, f₂ y)).mul_const (∫ z, f₃ z))
    (((hg₁.const_mul C).mul_const (∫ y, g₂ y)).mul_const (∫ z, g₃ z)) hi₂
  simpa only [integral_const_mul, integral_mul_const] using hi₁

theorem triple_coefficient_moment_bound (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hpoint : ∀ t₁ t₂ t₃ : ℝ, S * ‖b₁ t₁ * b₂ t₂ * b₃ t₃‖ ≤
      C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) :
    S * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * (1 + ‖t₃‖) ^ J *
        ‖b₁ t₁ * b₂ t₂ * b₃ t₃‖) ≤ C * (∫ t : ℝ, firstLogDensity 0 t) ^ 3 := by
  let f₁ : ℝ → ℝ := fun t => (1 + ‖t‖) ^ J * ‖b₁ t‖
  let f₂ : ℝ → ℝ := fun t => (1 + ‖t‖) ^ J * ‖b₂ t‖
  let f₃ : ℝ → ℝ := fun t => (1 + ‖t‖) ^ J * ‖b₃ t‖
  have hprod : ∀ t₁ t₂ t₃ : ℝ,
      (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * (1 + ‖t₃‖) ^ J *
        ‖b₁ t₁ * b₂ t₂ * b₃ t₃‖ = f₁ t₁ * (f₂ t₂ * f₃ t₃) := by
    intro t₁ t₂ t₃
    simp only [norm_mul, f₁, f₂, f₃]
    ring
  have hb : ∀ t₁ t₂ t₃ : ℝ, S * f₁ t₁ * f₂ t₂ * f₃ t₃ ≤
      C * firstLogDensity 0 t₁ * firstLogDensity 0 t₂ * firstLogDensity 0 t₃ := by
    intro t₁ t₂ t₃
    have h := mul_le_mul_of_nonneg_left (hpoint t₁ t₂ t₃)
      (show 0 ≤ (1 + ‖t₁‖)^J * (1 + ‖t₂‖)^J * (1 + ‖t₃‖)^J by positivity)
    have hd₁ := density_weight_identity J t₁
    have hd₂ := density_weight_identity J t₂
    have hd₃ := density_weight_identity J t₃
    simp only [norm_mul] at h
    rw [← hd₁, ← hd₂, ← hd₃]
    dsimp [f₁, f₂, f₃]
    simpa only [Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using h
  have hbound := triple_product_integral_bound f₁ f₂ f₃
    (firstLogDensity 0) (firstLogDensity 0) (firstLogDensity 0)
    (weighted_schwartz_integrable b₁ J) (weighted_schwartz_integrable b₂ J)
    (weighted_schwartz_integrable b₃ J)
    (firstLogDensity_integrable 0) (firstLogDensity_integrable 0) (firstLogDensity_integrable 0)
    S C hb
  simp_rw [hprod, integral_const_mul]
  simp_rw [integral_mul_const]
  convert! hbound using 1 <;> ring

end JointLogSeparation

open scoped BigOperators
namespace FiniteOverlapDecomposition
variable {ι : Type*} [DecidableEq ι]

abbrev Triple (ι : Type*) := Σ _ : Finset ι, Finset ι × Finset ι

def triples (F : Finset ι) : Finset (Triple ι) :=
  F.powerset.sigma fun G => ((F \ G).powerset ×ˢ (F \ G).powerset).filter fun UV => Disjoint UV.1 UV.2

def split (ST : Finset ι × Finset ι) : Triple ι :=
  ⟨ST.1 ∩ ST.2, ST.1 \ ST.2, ST.2 \ ST.1⟩

def join (GUV : Triple ι) : Finset ι × Finset ι :=
  (GUV.1 ∪ GUV.2.1, GUV.1 ∪ GUV.2.2)

lemma join_split (ST : Finset ι × Finset ι) : join (split ST) = ST := by
  apply Prod.ext
  · ext i
    simp only [join, split, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · ext i
    simp only [join, split, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto

lemma split_mem {F : Finset ι} {ST : Finset ι × Finset ι}
    (hST : ST ∈ F.powerset ×ˢ F.powerset) : split ST ∈ triples F := by
  rcases Finset.mem_product.mp hST with ⟨hS, hT⟩
  have hSF := Finset.mem_powerset.mp hS
  have hTF := Finset.mem_powerset.mp hT
  simp only [triples, split, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  refine ⟨Finset.inter_subset_left.trans hSF, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hi ⊢
    exact ⟨hSF hi.1, by tauto⟩
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hi ⊢
    exact ⟨hTF hi.1, by tauto⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1

lemma join_mem {F : Finset ι} {GUV : Triple ι} (h : GUV ∈ triples F) :
    join GUV ∈ F.powerset ×ˢ F.powerset := by
  rcases (by simpa only [triples, Finset.mem_sigma, Finset.mem_filter,
    Finset.mem_product, Finset.mem_powerset] using h) with ⟨hG, ⟨hU, hV⟩, _⟩
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_powerset.mpr
  · exact Finset.union_subset hG (hU.trans Finset.sdiff_subset)
  · exact Finset.union_subset hG (hV.trans Finset.sdiff_subset)

lemma split_join {F : Finset ι} {GUV : Triple ι} (h : GUV ∈ triples F) :
    split (join GUV) = GUV := by
  rcases GUV with ⟨G, U, V⟩
  have hh : G ⊆ F ∧ (U ⊆ F \ G ∧ V ⊆ F \ G) ∧ Disjoint U V := by
    simpa only [triples, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_product, Finset.mem_powerset] using h
  rcases hh with ⟨_, ⟨hU, hV⟩, hd⟩
  have hUG : Disjoint U G := Finset.disjoint_left.mpr (fun i hi hg => (Finset.mem_sdiff.mp (hU hi)).2 hg)
  have hVG : Disjoint V G := Finset.disjoint_left.mpr (fun i hi hg => (Finset.mem_sdiff.mp (hV hi)).2 hg)
  have h₀ : (G ∪ U) ∩ (G ∪ V) = G := by
    ext i
    have hi : i ∈ U → i ∈ V → False := fun hi hj => Finset.disjoint_left.mp hd hi hj
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have h₁ : (G ∪ U) \ (G ∪ V) = U := by
    ext i
    have hi : i ∈ U → i ∈ V → False := fun hi hj => Finset.disjoint_left.mp hd hi hj
    have hj : i ∈ U → i ∈ G → False := fun hi hj => Finset.disjoint_left.mp hUG hi hj
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have h₂ : (G ∪ V) \ (G ∪ U) = V := by
    ext i
    have hi : i ∈ V → i ∈ U → False := fun hi hj => Finset.disjoint_left.mp hd.symm hi hj
    have hj : i ∈ V → i ∈ G → False := fun hi hj => Finset.disjoint_left.mp hVG hi hj
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  simp only [split, join, h₀, h₁, h₂]

theorem sum_pair_eq_overlap {β : Type*} [AddCommMonoid β]
    (F : Finset ι) (C : Finset ι → Finset ι → β) :
    (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, C S T) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then C (G ∪ U) (G ∪ V) else 0 := by
  classical
  have hs : (∑ ST ∈ F.powerset ×ˢ F.powerset, C ST.1 ST.2) =
      ∑ GUV ∈ triples F, C (join GUV).1 (join GUV).2 := by
    apply Finset.sum_bij (fun ST _ => split ST)
    · intro ST hST
      exact split_mem hST
    · intro ST hST SU hSU heq
      have hh := congrArg join heq
      simpa only [join_split] using hh
    · intro GUV hGUV
      exact ⟨join GUV, join_mem hGUV, split_join hGUV⟩
    · intro ST hST
      rw [join_split]
  simpa only [triples, Finset.sum_sigma, Finset.sum_filter, Finset.sum_product, join] using hs

end FiniteOverlapDecomposition

end

end OAI

end

-- Source module: RSPhaseCompat
section
open scoped ContDiff

namespace Complex

theorem hasTemperateGrowth_exp_mul_I :
    Function.HasTemperateGrowth (fun x : ℝ => exp ((x : ℂ) * I)) := by
  let f : ℝ → ℂ := fun x => exp ((x : ℂ) * I)
  have hd (x : ℝ) : HasDerivAt f (I * f x) x := by
    simpa [f, mul_comm] using
      ((ofRealCLM.hasDerivAt (x := x)).mul_const I).cexp
  have hi (n : ℕ) : iteratedDeriv n f = fun x => I ^ n * f x := by
    induction n with
    | zero => ext x; simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      ext x
      rw [deriv_const_mul_field, (hd x).deriv, pow_succ]
      ring
  have hc : ContDiff ℝ ∞ f :=
    Complex.contDiff_exp.comp
      ((ofRealCLM.contDiff : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ))).mul contDiff_const)
  refine ⟨hc, fun n => ⟨0, 1, ?_⟩⟩
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv n f x‖ ≤ _
  rw [hi]
  simp [f, norm_pow, norm_exp]

end Complex

#print axioms Complex.hasTemperateGrowth_exp_mul_I

end


