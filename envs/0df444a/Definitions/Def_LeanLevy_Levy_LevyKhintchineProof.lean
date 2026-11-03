-- Prove2me | Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
-- name    : LeanLevy_Levy_LevyKhintchineProof
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-31T10:22:13.46585+00:00
-- url     : https://prove2.me/theorems/2667927c-5dfd-4a6c-b079-62881e7e5105
-- title:
--   LeanLevy source module: Levy.LevyKhintchineProof
-- statement:
--   Source-faithful, comment-compacted copy of the pinned LeanLevy module LeanLevy.Levy.LevyKhintchineProof. Its Lean declarations and proofs are retained, with imports mapped to corresponding definitions in this mission, including the source-faithful Fourier.Bochner module containing the complete Bochner proof. Prove2Me remote verification is pending.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Probability_Characteristic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Definitions.Def_LeanLevy_Fourier_Bochner
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
/-! -/
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder
namespace ProbabilityTheory
/-! ## Sub-lemma 1: Non-vanishing -/
section NonVanishing
/-! -/
/-- -/
theorem norm_charFun_half_le_of_charFun_eq_zero
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {ξ₀ : ℝ} (hξ : charFun ν ξ₀ = 0) :
    ‖charFun ν (ξ₀ / 2)‖ ≤ 3 / 4 := by
  set z := charFun ν (ξ₀ / 2) with hz_def
  by_cases hz : z = 0
  · simp [hz]; positivity
  · have hr_pos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have hr_ne : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
    set u := z / (↑‖z‖ : ℂ) with hu_def
    set P : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩
    have hφ0 : charFun ν 0 = 1 := by simp [charFun_zero, Measure.real, measure_univ]
    have hpsd := MeasureTheory.ProbabilityMeasure.characteristicFun_positiveSemiDefinite P
      (![0, ξ₀ / 2, ξ₀]) (![(starRingEnd ℂ) u, -2, u])
    simp only [MeasureTheory.ProbabilityMeasure.characteristicFun_def,
      show (↑P : Measure ℝ) = ν from rfl] at hpsd
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at hpsd
    rw [show (0 : ℝ) - ξ₀ / 2 = -(ξ₀ / 2) from by ring,
        show (0 : ℝ) - ξ₀ = -ξ₀ from by ring,
        show ξ₀ / 2 - ξ₀ = -(ξ₀ / 2) from by ring,
        show ξ₀ - ξ₀ / 2 = ξ₀ / 2 from by ring] at hpsd
    simp only [_root_.sub_self, _root_.sub_zero, charFun_neg, hξ, hφ0, map_zero,
      starRingEnd_self_apply, map_neg, map_ofNat, mul_zero, add_zero, mul_one] at hpsd
    have hu_norm : ‖u‖ = 1 := by
      rw [hu_def, norm_div, Complex.norm_real, Real.norm_of_nonneg hr_pos.le,
        div_self (ne_of_gt hr_pos)]
    have huu : u * (starRingEnd ℂ) u = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu_norm, one_pow, Complex.ofReal_one]
    have huu' : (starRingEnd ℂ) u * u = 1 := by rw [mul_comm, huu]
    simp only [huu, huu'] at hpsd
    have hre1 : (u * (starRingEnd ℂ) z).re = ‖z‖ := by
      rw [hu_def, div_mul_eq_mul_div, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [show (↑(‖z‖ ^ 2) : ℂ) / ↑‖z‖ = ↑‖z‖ from by
        rw [Complex.ofReal_pow, sq, mul_div_cancel_left₀ _ hr_ne]]
      exact Complex.ofReal_re ‖z‖
    have hre2 : ((starRingEnd ℂ) u * z).re = ‖z‖ := by
      have : ((starRingEnd ℂ) u * z).re = (u * (starRingEnd ℂ) z).re := by
        rw [show ((starRingEnd ℂ) u * z).re = ((starRingEnd ℂ) (u * (starRingEnd ℂ) z)).re from by
          simp [map_mul]]
        exact Complex.conj_re _
      rw [this, hre1]
    change 0 ≤ _ at hpsd
    simp only [show charFun ν (ξ₀ / 2) = z from rfl] at hpsd
    simp only [Complex.add_re] at hpsd
    have hscalar : ∀ (w : ℂ), ((-2 : ℂ) * w).re = -2 * w.re := by
      intro w; simp [Complex.mul_re]
    rw [show (-2 : ℂ) * (starRingEnd ℂ) u * z = (-2) * ((starRingEnd ℂ) u * z) from by ring,
        show (-2 : ℂ) * u * (starRingEnd ℂ) z = (-2) * (u * (starRingEnd ℂ) z) from by ring,
        show u * (-2 : ℂ) * (starRingEnd ℂ) z = (-2) * (u * (starRingEnd ℂ) z) from by ring,
        show (starRingEnd ℂ) u * (-2 : ℂ) * z = (-2) * ((starRingEnd ℂ) u * z) from by ring]
      at hpsd
    simp only [hscalar, hre1, hre2, Complex.one_re, Complex.zero_re,
      Complex.neg_re, Complex.re_ofNat] at hpsd
    linarith
/-- -/
private theorem charFun_half_eq_zero_of_charFun_eq_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ)
    {ξ₀ : ℝ} (hξ : charFun μ ξ₀ = 0) :
    charFun μ (ξ₀ / 2) = 0 := by
  rw [← norm_eq_zero]
  suffices hle : ∀ n : ℕ, 0 < n → ‖charFun μ (ξ₀ / 2)‖ ≤ (3 / 4 : ℝ) ^ n by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hc; push Not at hc
    have htend : Tendsto (fun n : ℕ => (3 / 4 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    have hev := htend.eventually (Iio_mem_nhds hc)
    obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
    have h1 := hle (N + 1) (Nat.succ_pos N)
    have h2 := hN (N + 1) (by omega)
    linarith
  intro n hn
  obtain ⟨ν, hν_prob, hμ_eq⟩ := h n hn
  have hpow : ∀ ξ, charFun μ ξ = (charFun ν ξ) ^ n := by
    intro ξ; rw [hμ_eq, charFun_iteratedConv]
  have hν_zero : charFun ν ξ₀ = 0 := by
    have h1 := hpow ξ₀; rw [hξ] at h1
    exact (pow_eq_zero_iff (by omega : n ≠ 0)).mp h1.symm
  have hν_half := norm_charFun_half_le_of_charFun_eq_zero hν_zero
  calc ‖charFun μ (ξ₀ / 2)‖
      = ‖charFun ν (ξ₀ / 2)‖ ^ n := by rw [hpow, norm_pow]
    _ ≤ (3 / 4 : ℝ) ^ n := pow_le_pow_left₀ (norm_nonneg _) hν_half n
/-- -/
theorem IsInfinitelyDivisible.charFun_ne_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) (ξ : ℝ) :
    charFun μ ξ ≠ 0 := by
  intro habs
  have hzero : ∀ k : ℕ, charFun μ (ξ / 2 ^ k) = 0 := by
    intro k; induction k with
    | zero => simpa using habs
    | succ k ih =>
      rw [show ξ / 2 ^ (k + 1) = ξ / 2 ^ k / 2 from by rw [div_div, ← pow_succ]]
      exact charFun_half_eq_zero_of_charFun_eq_zero h ih
  have htend : Tendsto (fun k : ℕ => ξ / (2 : ℝ) ^ k) atTop (nhds 0) := by
    have h2 : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
    exact tendsto_const_nhds.div_atTop h2
  have hcont : Continuous (charFun μ) := MeasureTheory.continuous_charFun
  have hφ0 : charFun μ 0 = 1 := by simp [charFun_zero, Measure.real, measure_univ]
  have hlim : Tendsto (fun k => charFun μ (ξ / 2 ^ k)) atTop (nhds 1) := by
    rw [← hφ0]; exact (hcont.tendsto 0).comp htend
  have hlim0 : Tendsto (fun k => charFun μ (ξ / 2 ^ k)) atTop (nhds 0) := by
    rw [show (fun k => charFun μ (ξ / 2 ^ k)) = fun _ => (0 : ℂ) from funext hzero]
    exact tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique hlim0 hlim).symm
end NonVanishing
/-! ## Sub-lemma 2: Continuous logarithm -/
/-- -/
theorem IsInfinitelyDivisible.exists_continuous_log
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    ∃ ψ : ℝ → ℂ, Continuous ψ ∧ ψ 0 = 0 ∧ ∀ ξ, charFun μ ξ = exp (ψ ξ) := by
  have hcont : Continuous (charFun μ) := MeasureTheory.continuous_charFun
  have hne : ∀ ξ, charFun μ ξ ≠ 0 := h.charFun_ne_zero
  have hφ0 : charFun μ 0 = 1 := by simp [charFun_zero, Measure.real, measure_univ]
  set f : C(ℝ, ℂ) := ⟨charFun μ, hcont⟩
  have he : Complex.exp (0 : ℂ) = f (0 : ℝ) := by simp [f, hφ0]
  have hs : ∀ ξ : ℝ, f ξ ∈ ({0}ᶜ : Set ℂ) := fun ξ => Set.mem_compl_singleton_iff.mpr (hne ξ)
  obtain ⟨F, ⟨hF0, hFexp⟩, _⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he hs
  exact ⟨F, F.continuous, hF0, fun ξ => by
    have := congr_fun hFexp ξ
    simp [Function.comp] at this
    exact this.symm⟩
/-- -/
theorem IsInfinitelyDivisible.hermitian_log
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ)
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_exp : ∀ ξ, charFun μ ξ = exp (ψ ξ)) :
    ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ) := by
  have hcont : Continuous (charFun μ) := MeasureTheory.continuous_charFun
  have hne : ∀ ξ, charFun μ ξ ≠ 0 := h.charFun_ne_zero
  have hφ0 : charFun μ 0 = 1 := by simp [charFun_zero, Measure.real, measure_univ]
  set f : C(ℝ, ℂ) := ⟨charFun μ, hcont⟩
  have he : Complex.exp (0 : ℂ) = f (0 : ℝ) := by simp [f, hφ0]
  have hs : ∀ ξ : ℝ, f ξ ∈ ({0}ᶜ : Set ℂ) := fun ξ => Set.mem_compl_singleton_iff.mpr (hne ξ)
  obtain ⟨F, ⟨_hF0, _hFexp⟩, hF_unique⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he hs
  set Ψ : C(ℝ, ℂ) := ⟨ψ, hψ_cont⟩
  have hΨ_lift : Ψ 0 = 0 ∧ Complex.exp ∘ Ψ = f := by
    refine ⟨hψ_zero, ?_⟩
    ext ξ; simp [Ψ, f, hψ_exp ξ]
  set G : C(ℝ, ℂ) := ⟨fun ξ => starRingEnd ℂ (ψ (-ξ)), by
    exact continuous_star.comp (hψ_cont.comp continuous_neg)⟩
  have hG_lift : G 0 = 0 ∧ Complex.exp ∘ G = f := by
    refine ⟨by simp [G, hψ_zero], ?_⟩
    ext ξ; simp only [G, ContinuousMap.coe_mk, Function.comp_apply, f]
    rw [exp_conj, ← hψ_exp (-ξ), charFun_neg, starRingEnd_self_apply]
  have hΨ_eq : Ψ = F := hF_unique Ψ hΨ_lift
  have hG_eq : G = F := hF_unique G hG_lift
  have hΨG : ∀ ξ, ψ ξ = starRingEnd ℂ (ψ (-ξ)) := fun ξ => by
    have := congr_arg (· ξ) (hΨ_eq.trans hG_eq.symm)
    exact this
  intro ξ
  have := hΨG (-ξ)
  simp only [neg_neg] at this
  exact this
/-! ## Sub-lemma 3: Conditional negative definiteness -/
/-- -/
def IsConditionallyNegativeDefinite (ψ : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (ξ : Fin n → ℝ) (c : Fin n → ℂ),
    ∑ i, c i = 0 →
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ (ξ i - ξ j)).re
/-- For a probability measure, `charFun ν 0 = 1`. -/
private theorem charFun_zero_eq_one {ν : Measure ℝ} [IsProbabilityMeasure ν] :
    charFun ν 0 = 1 := by
  simp [charFun_zero, Measure.real, measure_univ]
/-- When `∑ c = 0`, the constant term `∑ᵢ ∑ⱼ c̄ᵢ cⱼ` equals zero. -/
private theorem double_sum_conj_mul_eq_zero {n : ℕ} {c : Fin n → ℂ} (hc : ∑ i, c i = 0) :
    ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j = 0 := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp [hc]
/-! -/
/-! -/
/-- -/
private theorem charFun_psd {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * charFun ν (ξ i - ξ j)).re := by
  exact MeasureTheory.ProbabilityMeasure.characteristicFun_positiveSemiDefinite
    (⟨ν, inferInstance⟩ : ProbabilityMeasure ℝ) ξ c
/-- When `∑ c = 0`, PSD implies the "1 minus charFun" form is non-positive. -/
private theorem one_sub_charFun_form_nonpos {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) (hc : ∑ i, c i = 0) :
    (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (1 - charFun ν (ξ i - ξ j))).re ≤ 0 := by
  have hpsd := charFun_psd ξ c (ν := ν)
  have hzero := double_sum_conj_mul_eq_zero hc
  have : ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (1 - charFun ν (ξ i - ξ j)) =
    -(∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * charFun ν (ξ i - ξ j)) := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
    simp [hzero]
  rw [this, Complex.neg_re]
  linarith
/-- -/
private theorem charFun_eq_exp_div {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    {m : ℕ} (hm : 0 < m) (hpow : ∀ ξ, (charFun ν ξ) ^ m = exp (ψ ξ)) :
    ∀ ξ, charFun ν ξ = exp (ψ ξ / ↑m) := by
  have hcont : Continuous (charFun ν) := MeasureTheory.continuous_charFun
  have hne : ∀ ξ, charFun ν ξ ≠ 0 := by
    intro ξ habs
    have : (charFun ν ξ) ^ m = 0 := by rw [habs, zero_pow (by omega)]
    rw [hpow] at this
    exact exp_ne_zero _ this
  have hφ0 : charFun ν 0 = 1 := charFun_zero_eq_one
  set fν : C(ℝ, ℂ) := ⟨charFun ν, hcont⟩
  have heν : Complex.exp (0 : ℂ) = fν (0 : ℝ) := by simp [fν, hφ0]
  have hsν : ∀ ξ : ℝ, fν ξ ∈ ({0}ᶜ : Set ℂ) := fun ξ =>
    Set.mem_compl_singleton_iff.mpr (hne ξ)
  obtain ⟨logν, ⟨hlogν0, hlogν_exp⟩, hlogν_unique⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts fν heν hsν
  set g : C(ℝ, ℂ) := ⟨fun ξ => exp (ψ ξ), hψ_cont.cexp⟩
  have hsg : ∀ ξ : ℝ, g ξ ∈ ({0}ᶜ : Set ℂ) := fun ξ =>
    Set.mem_compl_singleton_iff.mpr (exp_ne_zero _)
  have heg : Complex.exp (0 : ℂ) = g (0 : ℝ) := by simp [g, hψ_zero]
  set ψ_cm : C(ℝ, ℂ) := ⟨ψ, hψ_cont⟩
  have hψ_lift_val : ψ_cm (0 : ℝ) = 0 := hψ_zero
  have hψ_lift_comp : Complex.exp ∘ ψ_cm = g := by
    ext ξ; simp [ψ_cm, g]
  set mlogν : C(ℝ, ℂ) := ⟨fun ξ => (↑m : ℂ) * logν ξ,
    continuous_const.mul logν.continuous⟩
  have hmlogν_val : mlogν (0 : ℝ) = 0 := by simp [mlogν, hlogν0]
  have hmlogν_comp : Complex.exp ∘ mlogν = g := by
    ext ξ
    simp only [Function.comp_apply, ContinuousMap.coe_mk, mlogν, g]
    rw [Complex.exp_nat_mul]
    have hexp_logν : Complex.exp (logν ξ) = charFun ν ξ := by
      have := congr_fun hlogν_exp ξ
      simp [Function.comp_apply] at this
      exact this
    rw [hexp_logν, hpow]
  obtain ⟨_, ⟨_, _⟩, huniq⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts g heg hsg
  have hψ_eq_mlogν : ψ_cm = mlogν := by
    have hψ_uniq := huniq ψ_cm ⟨hψ_lift_val, hψ_lift_comp⟩
    have hmlogν_uniq := huniq mlogν ⟨hmlogν_val, hmlogν_comp⟩
    rw [hψ_uniq, hmlogν_uniq]
  intro ξ
  have hexp_logν : Complex.exp (logν ξ) = charFun ν ξ := by
    have := congr_fun hlogν_exp ξ
    simp [Function.comp_apply] at this
    exact this
  rw [← hexp_logν]
  congr 1
  have hψ_eq : ψ ξ = (↑m : ℂ) * logν ξ := by
    have := congr_fun (congrArg DFunLike.coe hψ_eq_mlogν) ξ
    simp [ψ_cm, mlogν] at this
    exact this
  rw [hψ_eq]
  rw [mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.mpr (by omega)
/-- The complex limit `m * (1 - exp(z / m)) → -z` as `m → ∞`. -/
private theorem tendsto_mul_one_sub_exp_div (z : ℂ) :
    Tendsto (fun m : ℕ => (↑m : ℂ) * (1 - exp (z / ↑m))) atTop (nhds (-z)) := by
  by_cases hz : z = 0
  · -- Case z = 0: everything is zero
    simp [hz]
  · -- Case z ≠ 0: use (exp w - 1)/w → 1 as w → 0
    have hslope : Tendsto (slope cexp 0) (𝓝[≠] 0) (nhds 1) := by
      have h := hasDerivAt_exp (0 : ℂ)
      rw [exp_zero] at h
      exact h.tendsto_slope
    have hdiv_tendsto : Tendsto (fun m : ℕ => z / (↑m : ℂ)) atTop (nhds 0) := by
      have hinv : Tendsto (fun m : ℕ => (↑m : ℂ)⁻¹) atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have : (fun m : ℕ => ‖(↑m : ℂ)⁻¹‖) = fun m : ℕ => ((↑m : ℝ))⁻¹ := by
          ext m; rw [norm_inv, Complex.norm_natCast]
        rw [this]
        exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      rw [show (0 : ℂ) = z * 0 from by ring]
      simp only [div_eq_mul_inv]
      exact tendsto_const_nhds.mul hinv
    have hdiv_ne : ∀ᶠ m : ℕ in atTop, z / (↑m : ℂ) ∈ ({0}ᶜ : Set ℂ) := by
      filter_upwards [Filter.Ici_mem_atTop 1] with m (hm : 1 ≤ m)
      exact Set.mem_compl_singleton_iff.mpr
        (div_ne_zero hz (Nat.cast_ne_zero.mpr (by omega)))
    have hcomp : Tendsto (fun m : ℕ => slope cexp 0 (z / (↑m : ℂ))) atTop (nhds 1) :=
      hslope.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hdiv_tendsto hdiv_ne)
    have hmul_z : Tendsto (fun m : ℕ => slope cexp 0 (z / (↑m : ℂ)) * z) atTop (nhds z) := by
      have := hcomp.mul_const z
      rwa [one_mul] at this
    have hneg_z : Tendsto (fun m : ℕ => -(slope cexp 0 (z / (↑m : ℂ)) * z)) atTop (nhds (-z)) :=
      hmul_z.neg
    have heq : ∀ᶠ m : ℕ in atTop,
        (↑m : ℂ) * (1 - exp (z / ↑m)) = -(slope cexp 0 (z / (↑m : ℂ)) * z) := by
      filter_upwards [Filter.Ici_mem_atTop 1] with m (hm : 1 ≤ m)
      have hm_ne : (↑m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp only [slope, sub_zero, exp_zero, vsub_eq_sub, smul_eq_mul]
      have hz_div_ne : z / (↑m : ℂ) ≠ 0 := div_ne_zero hz hm_ne
      field_simp
      ring
    exact (tendsto_congr' heq).mpr hneg_z
/-- -/
theorem IsInfinitelyDivisible.isConditionallyNegativeDefinite_log
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ)
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_exp : ∀ ξ, charFun μ ξ = exp (ψ ξ)) :
    IsConditionallyNegativeDefinite ψ := by
  intro n ξ c hc
  have hbound : ∀ m : ℕ, 0 < m →
      (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j *
          ((↑m : ℂ) * (1 - exp (ψ (ξ i - ξ j) / ↑m)))).re ≤ 0 := by
    intro m hm
    obtain ⟨ν, hνP, hμ_eq⟩ := h m hm
    haveI := hνP
    have hpow : ∀ ξ', (charFun ν ξ') ^ m = exp (ψ ξ') := by
      intro ξ'; rw [← hψ_exp, hμ_eq, charFun_iteratedConv]
    have hν_exp := charFun_eq_exp_div hψ_cont hψ_zero hm hpow
    have hsub : ∀ i j : Fin n,
        1 - charFun ν (ξ i - ξ j) = 1 - exp (ψ (ξ i - ξ j) / ↑m) := by
      intro i j; rw [hν_exp]
    have hnonpos := one_sub_charFun_form_nonpos ξ c hc (ν := ν)
    simp_rw [hsub] at hnonpos
    have hfactor : ∀ i j : Fin n,
        starRingEnd ℂ (c i) * c j * ((↑m : ℂ) * (1 - exp (ψ (ξ i - ξ j) / ↑m))) =
        (↑m : ℂ) * (starRingEnd ℂ (c i) * c j * (1 - exp (ψ (ξ i - ξ j) / ↑m))) := by
      intro i j; ring
    simp_rw [hfactor, ← Finset.mul_sum]
    have hm_re : ((↑m : ℂ) * (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * (1 - exp (ψ (ξ i - ξ j) / ↑m)))).re =
      ↑m * (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * (1 - exp (ψ (ξ i - ξ j) / ↑m))).re := by
      rw [Complex.mul_re]
      simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    rw [hm_re]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg' m) hnonpos
  have hlim : Tendsto
      (fun m : ℕ => (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j *
          ((↑m : ℂ) * (1 - exp (ψ (ξ i - ξ j) / ↑m)))).re)
      atTop
      (nhds (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * (-ψ (ξ i - ξ j))).re) := by
    apply Complex.continuous_re.continuousAt.tendsto.comp
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    apply Filter.Tendsto.const_mul
    exact tendsto_mul_one_sub_exp_div (ψ (ξ i - ξ j))
  have hle : (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (-ψ (ξ i - ξ j))).re ≤ 0 :=
    le_of_tendsto hlim (Eventually.of_forall fun m => by
      by_cases hm : m = 0
      · simp [hm]
      · exact hbound m (Nat.pos_of_ne_zero hm))
  have hneg : (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (-ψ (ξ i - ξ j))).re =
    -(∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * ψ (ξ i - ξ j)).re := by
    simp_rw [mul_neg, Finset.sum_neg_distrib, Complex.neg_re]
  linarith [hneg]
/-! ## Schoenberg's theorem -/
/-- -/
private theorem cnd_kernel_pd
    {ψ : ℝ → ℂ} (hψ_cnd : IsConditionallyNegativeDefinite ψ) (hψ_zero : ψ 0 = 0)
    (hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ))
    (n : ℕ) (ξ : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j))) := by
  rw [Complex.nonneg_iff]
  constructor
  · -- .re ≥ 0: the (n+1)-point CND sum with c₀ = -∑cᵢ, ξ₀ = 0 equals our kernel sum
    set ξ' : Fin (n + 1) → ℝ := Fin.cons 0 ξ
    set c' : Fin (n + 1) → ℂ := Fin.cons (-∑ i, c i) c
    have hc'_sum : ∑ i, c' i = 0 := by
      simp only [c', Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring
    have hcnd := hψ_cnd (n + 1) ξ' c' hc'_sum
    suffices heq : (∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        starRingEnd ℂ (c' a) * c' b * ψ (ξ' a - ξ' b)).re =
      (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j)))).re by
      linarith
    have key : ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        starRingEnd ℂ (c' a) * c' b * ψ (ξ' a - ξ' b) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j))) := by
      simp_rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, c', ξ']
      simp only [sub_zero, hψ_zero, mul_zero, zero_add]
      simp_rw [show ∀ x, (0 : ℝ) - ξ x = -(ξ x) from fun x => by ring, hψ_herm]
      have hT1 : ∑ x, (starRingEnd ℂ) (-∑ i, c i) * c x * (starRingEnd ℂ) (ψ (ξ x)) =
          -(∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (starRingEnd ℂ) (ψ (ξ j))) := by
        simp_rw [map_neg, _root_.map_sum, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
        rw [Finset.sum_comm]
      have hT2 : ∀ x, ((starRingEnd ℂ) (c x) * -∑ i, c i) * ψ (ξ x) =
          -(∑ j, (starRingEnd ℂ) (c x) * c j * ψ (ξ x)) := by
        intro x; ring_nf
        congr 1
        rw [show (starRingEnd ℂ) (c x) * (∑ i, c i) * ψ (ξ x) =
          (starRingEnd ℂ) (c x) * ψ (ξ x) * ∑ i, c i from by ring]
        rw [Finset.mul_sum]
      rw [hT1]; simp_rw [hT2]
      simp_rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [key]
  · -- .im = 0: kernel K_{ij} is Hermitian so the quadratic form is real
    have hK_herm : ∀ i j : Fin n,
        starRingEnd ℂ (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j))) =
        ψ (ξ j - ξ i) - ψ (ξ j) - starRingEnd ℂ (ψ (ξ i)) := by
      intro i j
      simp only [map_sub, starRingEnd_self_apply]
      rw [← hψ_herm (ξ i - ξ j), show -(ξ i - ξ j) = ξ j - ξ i from by ring]; ring
    have hself_conj : starRingEnd ℂ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j)))) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j))) := by
      simp only [_root_.map_sum, map_mul, starRingEnd_self_apply, hK_herm]
      rw [Finset.sum_comm]
      congr 1; ext i; congr 1; ext j; ring
    have h := congr_arg Complex.im hself_conj
    simp only [Complex.conj_im, neg_eq_iff_eq_neg] at h
    linarith
open Matrix in
private theorem pd_kernel_to_posSemidef {n : ℕ} {K : Fin n → Fin n → ℂ}
    (hK : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j) :
    (Matrix.of K).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun c => ?_⟩
  · -- Hermitianness: conj(K j i) = K i j
    have hself_conj : ∀ c : Fin n → ℂ,
        starRingEnd ℂ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j) =
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j := by
      intro c
      have h0 := hK c
      rw [Complex.nonneg_iff] at h0
      rw [Complex.conj_eq_iff_im]
      exact h0.2.symm
    have hswap : ∀ c : Fin n → ℂ,
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * starRingEnd ℂ (K j i) =
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j := by
      intro c
      have h := hself_conj c
      simp only [_root_.map_sum, map_mul, starRingEnd_self_apply] at h
      rw [Finset.sum_comm] at h
      have := h
      simp_rw [show ∀ i j : Fin n, c j * (starRingEnd ℂ) (c i) * (starRingEnd ℂ) (K j i) =
        (starRingEnd ℂ) (c i) * c j * (starRingEnd ℂ) (K j i) from fun i j => by ring] at this
      exact this
    have hdiff_zero : ∀ c : Fin n → ℂ,
        ∑ a, ∑ b, starRingEnd ℂ (c a) * c b * (K a b - starRingEnd ℂ (K b a)) = 0 := by
      intro c
      have h := hswap c
      have : ∑ a, ∑ b, starRingEnd ℂ (c a) * c b * (K a b - starRingEnd ℂ (K b a)) =
          (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * K a b) -
          (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * starRingEnd ℂ (K b a)) := by
        simp_rw [mul_sub, ← Finset.sum_sub_distrib]
      rw [this, h, _root_.sub_self]
    have hD_diag : ∀ a : Fin n, K a a - starRingEnd ℂ (K a a) = 0 := by
      intro a
      have := hdiff_zero (Pi.single a 1)
      simp only [Pi.single_apply, apply_ite (starRingEnd ℂ), map_one, map_zero, ite_mul,
        one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true] at this
      exact this
    ext i j
    simp only [conjTranspose_apply, of_apply, star_def]
    suffices hD : ∀ a b : Fin n, K a b - starRingEnd ℂ (K b a) = 0 by
      have := hD i j; rw [sub_eq_zero] at this; exact this.symm
    intro a b
    by_cases hab : a = b
    · subst hab; exact hD_diag a
    · -- Use two-point test vectors to show D(a,b) = K(a,b) - conj(K(b,a)) = 0
      have heval : ∀ s t : ℂ,
          starRingEnd ℂ s * s * (K a a - starRingEnd ℂ (K a a)) +
          starRingEnd ℂ s * t * (K a b - starRingEnd ℂ (K b a)) +
          (starRingEnd ℂ t * s * (K b a - starRingEnd ℂ (K a b)) +
          starRingEnd ℂ t * t * (K b b - starRingEnd ℂ (K b b))) = 0 := by
        intro s t
        have key := hdiff_zero (fun k => (if k = a then s else 0) + (if k = b then t else 0))
        simp only [map_add, apply_ite (starRingEnd ℂ), map_zero, add_mul, mul_add,
          ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_add_distrib,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true] at key
        convert key using 1
        ring
      have hDa := hD_diag a
      have hDb := hD_diag b
      have htest1 := heval 1 1
      simp only [map_one, one_mul, hDa, hDb, mul_zero, zero_add, add_zero] at htest1
      have htest2 := heval 1 I
      simp only [map_one, one_mul, mul_one, conj_I, hDa, hDb, mul_zero, zero_add,
        add_zero] at htest2
      set D₁ := K a b - starRingEnd ℂ (K b a)
      set D₂ := K b a - starRingEnd ℂ (K a b)
      have h_sum : D₁ + D₂ = 0 := htest1
      have h_eq : D₁ = D₂ := by
        have h_Idiff : I * D₁ - I * D₂ = 0 := by
          have := htest2
          linear_combination this
        have : I * (D₁ - D₂) = 0 := by rw [mul_sub]; exact h_Idiff
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left I_ne_zero)
      have : D₁ + D₁ = 0 := by rw [show D₁ + D₁ = D₁ + D₂ from by rw [h_eq]]; exact h_sum
      rw [show D₁ = (2 : ℂ)⁻¹ * (D₁ + D₁) from by ring, this, mul_zero]
  · change 0 ≤ dotProduct (star c) (mulVec (Matrix.of K) c)
    have key : dotProduct (star c) (mulVec (Matrix.of K) c) =
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j := by
      simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
      congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
    rw [key]; exact hK c
private theorem pd_kernel_mul
    {n : ℕ} {M N : Fin n → Fin n → ℂ}
    (hM : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * M i j)
    (hN : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * N i j) :
    ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (M i j * N i j) := by
  open Matrix in
  intro c
  have hN_psd := pd_kernel_to_posSemidef hN
  have hN_herm := hN_psd.isHermitian
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.of N
  set ev := hN_herm.eigenvalues
  set U : Matrix (Fin n) (Fin n) ℂ := ↑hN_herm.eigenvectorUnitary
  have hev_nonneg : ∀ k, 0 ≤ ev k := fun k => hN_psd.eigenvalues_nonneg k
  have hN_spec : ∀ i j : Fin n, N i j = ∑ k, (↑(ev k) : ℂ) * U i k *
      starRingEnd ℂ (U j k) := by
    intro i j
    have h := hN_herm.spectral_theorem
    have hBij : B i j = ((Unitary.conjStarAlgAut ℂ _) hN_herm.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hN_herm.eigenvalues))) i j :=
      congr_fun (congr_fun h i) j
    rw [show N i j = B i j from rfl, hBij, Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
    congr 1; ext k
    simp only [Matrix.star_apply, star_def, Matrix.mul_apply, Matrix.diagonal_apply,
      Function.comp]
    have key := Fintype.sum_eq_single k
      (show ∀ l : Fin n, l ≠ k →
        (↑hN_herm.eigenvectorUnitary : Matrix _ _ ℂ) i l *
        (if l = k then (↑(hN_herm.eigenvalues l) : ℂ) else 0) = 0
      from fun l hlk => by simp [hlk])
    calc _ = (↑hN_herm.eigenvectorUnitary : Matrix _ _ ℂ) i k *
            (if k = k then (↑(hN_herm.eigenvalues k) : ℂ) else 0) *
            starRingEnd ℂ ((↑hN_herm.eigenvectorUnitary : Matrix _ _ ℂ) j k) := by
              exact congrArg (· * _) key
         _ = (↑(ev k) : ℂ) * U i k * starRingEnd ℂ (U j k) := by
              simp only [ite_true, U, ev]; ring
  set d : Fin n → Fin n → ℂ := fun k i => c i * starRingEnd ℂ (U i k)
  have hsuff : ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (M i j * N i j) =
      ∑ k, (↑(ev k) : ℂ) *
        (∑ i, ∑ j, starRingEnd ℂ (d k i) * d k j * M i j) := by
    simp_rw [hN_spec]
    simp_rw [Finset.mul_sum]
    conv_lhs =>
      arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    congr 1; ext k
    have hterm : ∀ i j : Fin n,
        starRingEnd ℂ (c i) * c j * (M i j * (↑(ev k) * U i k * starRingEnd ℂ (U j k)))
        = ↑(ev k) * (starRingEnd ℂ (d k i) * d k j * M i j) := by
      intro i j; simp only [d, map_mul, starRingEnd_self_apply]; ring
    simp_rw [hterm]
  rw [hsuff]
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (by exact_mod_cast hev_nonneg k) (hM (d k))
private theorem pd_kernel_pow
    {n : ℕ} {M : Fin n → Fin n → ℂ}
    (hM : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * M i j)
    (k : ℕ) :
    ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * M i j ^ k := by
  induction k with
  | zero =>
    intro c; simp only [pow_zero, mul_one]
    rw [show ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j =
        starRingEnd ℂ (∑ i, c i) * ∑ j, c j from by
      rw [_root_.map_sum]; simp_rw [Finset.sum_mul, Finset.mul_sum]]
    exact star_mul_self_nonneg _
  | succ k ih =>
    intro c
    have hpow : ∀ i j : Fin n, M i j ^ (k + 1) = M i j ^ k * M i j :=
      fun i j => pow_succ (M i j) k
    simp_rw [hpow]
    exact pd_kernel_mul ih hM c
private theorem exp_pd_kernel
    {n : ℕ} {M : Fin n → Fin n → ℂ}
    (hM : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * M i j)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * exp (↑t * M i j) := by
  intro c
  have hbase : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ d : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (d i) * d j *
        (1 + ↑t / (↑N : ℂ) * M i j) := by
    filter_upwards [Filter.Ici_mem_atTop 1] with N (hN : 1 ≤ N)
    intro d
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have htN : 0 ≤ t / N := div_nonneg ht (le_of_lt hN_pos)
    have hsplit : ∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (d i) * d j * (1 + ↑t / (↑N : ℂ) * M i j) =
      ∑ i, ∑ j, starRingEnd ℂ (d i) * d j +
        (↑t / ↑N : ℂ) * ∑ i, ∑ j, starRingEnd ℂ (d i) * d j * M i j := by
      trans ∑ i : Fin n, (∑ j, starRingEnd ℂ (d i) * d j +
        ↑t / ↑N * ∑ j, starRingEnd ℂ (d i) * d j * M i j)
      · congr 1; ext i
        trans ∑ j : Fin n, (starRingEnd ℂ (d i) * d j +
          ↑t / ↑N * (starRingEnd ℂ (d i) * d j * M i j))
        · congr 1; ext j; ring
        · rw [Finset.sum_add_distrib, Finset.mul_sum]
      · rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsplit]
    apply add_nonneg
    · -- |∑dᵢ|² ≥ 0
      rw [show ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (d i) * d j =
          starRingEnd ℂ (∑ i, d i) * ∑ j, d j from by
        rw [_root_.map_sum]; simp_rw [Finset.sum_mul, Finset.mul_sum]]
      exact star_mul_self_nonneg _
    · -- (t/N) · (PD sum) ≥ 0
      have hcoeff : (0 : ℂ) ≤ ↑t / ↑N := by
        rw [Complex.nonneg_iff]; constructor
        · simp; exact div_nonneg ht (le_of_lt hN_pos)
        · simp
      exact mul_nonneg hcoeff (hM d)
  have hpow_pd : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ d : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (d i) * d j *
        (1 + ↑t / (↑N : ℂ) * M i j) ^ N := by
    filter_upwards [hbase] with N hN
    intro d
    have hpow_eq : ∀ i j, (1 + ↑t / (↑N : ℂ) * M i j) ^ N =
        (fun i j => 1 + ↑t / (↑N : ℂ) * M i j) i j ^ N := fun i j => rfl
    simp_rw [hpow_eq]
    exact pd_kernel_pow hN N d
  have hlim : ∀ i j : Fin n, Filter.Tendsto
      (fun N : ℕ => starRingEnd ℂ (c i) * c j * (1 + ↑t / (↑N : ℂ) * M i j) ^ N)
      Filter.atTop (nhds (starRingEnd ℂ (c i) * c j * exp (↑t * M i j))) := by
    intro i j
    apply Filter.Tendsto.const_mul
    exact (Complex.tendsto_one_add_div_pow_exp (↑t * M i j)).congr fun N => by
      by_cases hN : (N : ℕ) = 0
      · simp [hN]
      · have hNne : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
        congr 1; field_simp
  have hsum_lim : Filter.Tendsto
      (fun N : ℕ => ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j *
        (1 + ↑t / (↑N : ℂ) * M i j) ^ N)
      Filter.atTop
      (nhds (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * exp (↑t * M i j))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => hlim i j
  exact ge_of_tendsto hsum_lim (by filter_upwards [hpow_pd] with N hN; exact hN c)
theorem schoenberg_exp_of_cnd
    {ψ : ℝ → ℂ} (_hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_cnd : IsConditionallyNegativeDefinite ψ)
    (hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ))
    (t : ℝ) (ht : 0 < t) :
    IsPositiveDefinite (fun ξ => exp (↑t * ψ ξ)) := by
  intro n x c
  have hM := fun d => cnd_kernel_pd hψ_cnd hψ_zero hψ_herm n x d
  have hexpM := exp_pd_kernel hM t (le_of_lt ht)
  set d : Fin n → ℂ := fun i => c i * exp (↑t * starRingEnd ℂ (ψ (x i)))
  suffices hsuff : ∀ i j : Fin n,
      starRingEnd ℂ (c i) * c j * exp (↑t * ψ (x i - x j)) =
      starRingEnd ℂ (d i) * d j *
        exp (↑t * (ψ (x i - x j) - ψ (x i) - starRingEnd ℂ (ψ (x j)))) by
    simp_rw [hsuff]
    exact hexpM d
  intro i j
  simp only [d, map_mul]
  rw [show starRingEnd ℂ (exp (↑t * starRingEnd ℂ (ψ (x i)))) =
      exp (↑t * ψ (x i)) from by
    rw [← Complex.exp_conj]; congr 1
    simp [Complex.conj_ofReal]]
  rw [show starRingEnd ℂ (c i) * exp (↑t * ψ (x i)) *
      (c j * exp (↑t * starRingEnd ℂ (ψ (x j)))) *
      exp (↑t * (ψ (x i - x j) - ψ (x i) - starRingEnd ℂ (ψ (x j)))) =
    starRingEnd ℂ (c i) * c j *
      (exp (↑t * ψ (x i)) * exp (↑t * starRingEnd ℂ (ψ (x j))) *
        exp (↑t * (ψ (x i - x j) - ψ (x i) - starRingEnd ℂ (ψ (x j))))) from by ring]
  congr 1
  rw [← exp_add, ← exp_add]
  congr 1; ring
/-! ## Convolution semigroup structure -/
/-- -/
structure ConvolutionSemigroup where
  /-- The exponent function: `charFun(μ_t) = exp(t · ψ)`. -/
  exponent : ℝ → ℂ
  /-- The exponent is continuous. -/
  exponent_continuous : Continuous exponent
  /-- The exponent vanishes at 0. -/
  exponent_zero : exponent 0 = 0
  /-- For each `t > 0`, a probability measure whose characteristic function is `exp(tψ)`. -/
  measure : {t : ℝ // 0 < t} → MeasureTheory.ProbabilityMeasure ℝ
  /-- The characteristic function identity. -/
  charFun_eq : ∀ (t : {t : ℝ // 0 < t}) (ξ : ℝ),
    MeasureTheory.ProbabilityMeasure.characteristicFun (measure t) ξ =
      exp ((↑t.val : ℂ) * exponent ξ)
namespace ConvolutionSemigroup
variable (S : ConvolutionSemigroup)
/-- -/
noncomputable def scaledMeasure (t : {t : ℝ // 0 < t}) : Measure ℝ :=
  ENNReal.ofReal t.val⁻¹ • (S.measure t : Measure ℝ)
end ConvolutionSemigroup
/-! -/
/-- The "small jump" set `{x | |x| < 1}`. -/
def smallSet : Set ℝ := {x | |x| < 1}
/-- The "large jump" set `{x | ε ≤ |x|}`. -/
def largeSet (ε : ℝ) : Set ℝ := {x | ε ≤ |x|}
/-! -/
/-! -/
section SincBounds
open scoped Real
end SincBounds
namespace ConvolutionSemigroup
variable (S : ConvolutionSemigroup)
/-! ### 3.1 — Uniform boundedness of scaled measures on large sets -/
end ConvolutionSemigroup
/-! -/
/-! -/
namespace ConvolutionSemigroup
variable (S : ConvolutionSemigroup)
/-! ### 3.3 — Monotonicity of large sets -/
/-! ### 3.4 — Large-jump integrand identification -/
/-! -/
/-! -/
/-! -/
/-- The scaled measure `t⁻¹ · μ_t` tilted by the density `min 1 x²`. -/
noncomputable def tiltedScaledMeasure (t : {t : ℝ // 0 < t}) : Measure ℝ :=
  (S.scaledMeasure t).withDensity (fun x => ENNReal.ofReal (min 1 (x ^ 2)))
/-! -/
/-- -/
private noncomputable def largeUpperBCF (ρ : ℝ) (_hρ : 0 < ρ) (n : ℕ) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)),
      Continuous.min continuous_const
        (Continuous.max continuous_const
          (((continuous_abs.sub continuous_const).mul continuous_const).add continuous_const))⟩
    1
    (fun x y => by
      have hbnd : ∀ z : ℝ,
          0 ≤ min 1 (max 0 ((|z| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) ∧
          min 1 (max 0 ((|z| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) ≤ 1 := fun z =>
        ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
      rw [Real.dist_eq]
      simp only [ContinuousMap.coe_mk]
      have hx := hbnd x; have hy := hbnd y
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith)
private lemma largeUpperBCF_apply (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ) :
    largeUpperBCF ρ hρ n x = min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) := rfl
private lemma largeUpperBCF_nonneg (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ) :
    0 ≤ largeUpperBCF ρ hρ n x := by
  rw [largeUpperBCF_apply]; exact le_min zero_le_one (le_max_left _ _)
private lemma largeUpperBCF_le_one (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ) :
    largeUpperBCF ρ hρ n x ≤ 1 := by
  rw [largeUpperBCF_apply]; exact min_le_left _ _
/-- -/
private noncomputable def largeAnnulusBCF (ρ : ℝ) (_hρ : 0 < ρ) (n : ℕ) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ/(n + 1 : ℝ))),
      Continuous.max continuous_const
        (continuous_const.sub (continuous_const.mul
          (Continuous.max continuous_const
            ((continuous_abs.comp (continuous_abs.sub continuous_const)).sub continuous_const))))⟩
    1
    (fun x y => by
      have hbnd : ∀ z : ℝ,
          0 ≤ max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|z| - ρ)| - ρ/(n + 1 : ℝ))) ∧
          max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|z| - ρ)| - ρ/(n + 1 : ℝ))) ≤ 1 := fun z => by
        refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
        have h1 : 0 ≤ ((n + 1 : ℝ) / ρ) * max 0 (|(|z| - ρ)| - ρ/(n + 1 : ℝ)) := by positivity
        linarith
      rw [Real.dist_eq]
      simp only [ContinuousMap.coe_mk]
      have hx := hbnd x; have hy := hbnd y
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith)
/-- BCF representing `largeUpperBCF ρ n · g` for a bounded continuous `g`. -/
private noncomputable def largeUpperMulBCF (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (M : ℝ) (hg_bnd : ∀ x, |g x| ≤ M) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => largeUpperBCF ρ hρ n x * g x,
      (largeUpperBCF ρ hρ n).continuous.mul hg_cont⟩
    (2 * M)
    (fun x y => by
      simp only [ContinuousMap.coe_mk]
      rw [Real.dist_eq]
      have hbnd : ∀ z, |largeUpperBCF ρ hρ n z * g z| ≤ M := fun z => by
        rw [abs_mul, abs_of_nonneg (largeUpperBCF_nonneg ρ hρ n z)]
        calc largeUpperBCF ρ hρ n z * |g z|
            ≤ 1 * |g z| :=
              mul_le_mul_of_nonneg_right (largeUpperBCF_le_one ρ hρ n z) (abs_nonneg _)
          _ ≤ 1 * M := mul_le_mul_of_nonneg_left (hg_bnd z) zero_le_one
          _ = M := one_mul _
      have hx := hbnd x; have hy := hbnd y
      rw [abs_le] at hx hy
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith)
/-! -/
/-! -/
end ConvolutionSemigroup
/-- Build a convolution semigroup from a CND exponent via Schoenberg + Bochner. -/
noncomputable def convolutionSemigroupOfCND
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_cnd : IsConditionallyNegativeDefinite ψ)
    (hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ)) :
    ConvolutionSemigroup where
  exponent := ψ
  exponent_continuous := hψ_cont
  exponent_zero := hψ_zero
  measure := fun ⟨t, ht⟩ =>
    (bochner _ (by fun_prop : Continuous (fun ξ => exp ((↑t : ℂ) * ψ ξ)))
      (schoenberg_exp_of_cnd hψ_cont hψ_zero hψ_cnd hψ_herm t ht)
      (by rw [hψ_zero, mul_zero, exp_zero])).choose
  charFun_eq := fun ⟨t, ht⟩ ξ =>
    (bochner _ (by fun_prop : Continuous (fun ξ => exp ((↑t : ℂ) * ψ ξ)))
      (schoenberg_exp_of_cnd hψ_cont hψ_zero hψ_cnd hψ_herm t ht)
      (by rw [hψ_zero, mul_zero, exp_zero])).choose_spec ξ
/-- -/
noncomputable def convolutionSemigroupOfMeasure
    (μ : Measure ℝ) [hμ : IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    ConvolutionSemigroup :=
  let ψ_data := h.exists_continuous_log
  let ψ := ψ_data.choose
  let hψ_cont := ψ_data.choose_spec.1
  let hψ_zero := ψ_data.choose_spec.2.1
  let hψ_exp := ψ_data.choose_spec.2.2
  let hψ_cnd := h.isConditionallyNegativeDefinite_log hψ_cont hψ_zero hψ_exp
  let hψ_herm := h.hermitian_log hψ_cont hψ_zero hψ_exp
  let S₀ := convolutionSemigroupOfCND hψ_cont hψ_zero hψ_cnd hψ_herm
  { exponent := S₀.exponent
    exponent_continuous := S₀.exponent_continuous
    exponent_zero := S₀.exponent_zero
    measure := fun t =>
      if h1 : t.val = 1 then ⟨μ, hμ⟩ else S₀.measure t
    charFun_eq := by
      intro t ξ
      by_cases ht : t.val = 1
      · have hmain : MeasureTheory.ProbabilityMeasure.characteristicFun
            (⟨μ, hμ⟩ : MeasureTheory.ProbabilityMeasure ℝ) ξ =
            exp ((↑t.val : ℂ) * S₀.exponent ξ) := by
          change charFun μ ξ = exp ((↑t.val : ℂ) * S₀.exponent ξ)
          rw [ht]
          show charFun μ ξ = exp ((1 : ℂ) * ψ ξ)
          rw [one_mul, hψ_exp ξ]
        simpa [ht, MeasureTheory.ProbabilityMeasure.characteristicFun_def] using hmain
      · simpa [ht] using S₀.charFun_eq t ξ }
/-! ## Sub-lemma 4: Integral representation -/
/-! ## Assembly: Lévy-Khintchine representation -/
/-! ## Converse: every Lévy-Khintchine triple yields an infinitely divisible law -/
/-- -/
noncomputable def LevyKhintchineTriple.exponent (T : LevyKhintchineTriple) (ξ : ℝ) : ℂ :=
  ↑T.drift * ↑ξ * I - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
    + ∫ x, levyCompensatedIntegrand ξ x ∂T.levyMeasure
end ProbabilityTheory


