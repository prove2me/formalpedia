-- Prove2me | Definitions.Def_LevyStochCalc_Ito_SmallJumpProcess_F001
-- name    : LevyStochCalc_Ito_SmallJumpProcess_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:16:40.144469+00:00
-- url     : https://prove2.me/theorems/83ee3e5a-0b1a-4e4e-aec4-503587a5528b
-- title:
--   Source declarations: LevyStochCalc.Ito.SmallJumpProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.SmallJumpProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SmallJumpProcess_F000
import Definitions.Def_SourceProof_11bae7bcfc13ecd9e06ddd2d
import Definitions.Def_SourceProof_7c1e051c1c1f9aebd6c80fa9
import Definitions.Def_SourceProof_a4dbeae1c9a6b22bf7020922
import Definitions.Def_SourceProof_beebe463528d222d5e910101
import Definitions.Def_SourceProof_d535c014a12fb1a12728f5c9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Removing the small jumps of a jump diffusion

For a jump diffusion `X` and an antitone family `A : ℕ → Set E` of mark sets whose intersection
is `ν`-null, the *big-jump process* is the path with the compensated integral of the jump
coefficient over `A m` subtracted coordinatewise. The subtracted term is the everywhere-càdlàg
modification of the compensated integral of a mark cut, so its `L²` size is the energy carried
by `A m` and vanishes as `m → ∞`; the big-jump processes therefore converge to the path at every
fixed nonnegative time in `L²`, almost surely along a subsequence, at almost every time of a
bounded window along a subsequence, and — after composing with a `C²` function of time and
state — pathwise along that subsequence.

## Main definitions

* `LevyStochCalc.Ito.SmallJump.JumpIntegrand` — the filtration and admissibility data with
  which the coordinates of the jump coefficient along a path are integrated against `Ñ`.
* `LevyStochCalc.Ito.SmallJump.smallJumpIntegral` — the everywhere-càdlàg modification of the
  compensated integral of one coordinate of the jump coefficient, restricted to the marks
  in `A m`.
* `LevyStochCalc.Ito.SmallJump.bigJumpProcess` — the path with that integral subtracted.

## Main statements

* `LevyStochCalc.Ito.SmallJump.measurable_uncurry_bigJumpProcess` — joint measurability of a
  coordinate of the big-jump process in the sample point and the time.
* `LevyStochCalc.Ito.SmallJump.tendsto_lintegral_sq_bigJumpProcess_sub` — `L²` convergence of
  the big-jump processes to the path at a fixed nonnegative time.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_bigJumpProcess_pi` — almost-sure
  convergence of the big-jump vectors along a subsequence.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_ae_tendsto_bigJumpProcess_pi` — almost-sure
  convergence of the big-jump vectors at almost every time of a bounded window, along a
  subsequence.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_comp` — the same, transported through a
  `C²` function of time and state.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_drift_bigJumpProcess`,
  `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_quadVar_bigJumpProcess` — pathwise
  convergence of the drift and quadratic-variation integrals along the big-jump processes.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.SmallJump

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
variable {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable {Xp : ℝ → Ω → (Fin n → ℝ)} {A : ℕ → Set E}

section Basic

variable (G : JumpIntegrand N coeffs Xp) (hA : ∀ m, MeasurableSet (A m))
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)

end Basic

section Limits

variable (G : JumpIntegrand N coeffs Xp) (hA : ∀ m, MeasurableSet (A m))
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)

/-- **Along a subsequence the big-jump processes converge to the path almost surely, in every
coordinate at once.** -/
theorem exists_seq_ae_tendsto_bigJumpProcess (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P, ∀ i : Fin n,
        Tendsto (fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k) t ω i) atTop
          (𝓝 (Xp t ω i)) :=
  _root_.Prove2MeSourceProof.h_7c1e051c1c1f9aebd6c80fa9
    (u := fun m i ω => bigJumpProcess G hA hℱ0 hnull0 m t ω i) (v := fun i ω => Xp t ω i)
    (fun m i => measurable_bigJumpProcess G hA hℱ0 hnull0 m t i)
    (fun i => measurable_pathCoord G.measurable_path t i)
    fun i => _root_.Prove2MeSourceProof.h_11bae7bcfc13ecd9e06ddd2d G hA hℱ0 hnull0 hanti hnull i ht
/-- **Along a subsequence the big-jump vectors converge to the path almost surely.** -/
theorem exists_seq_ae_tendsto_bigJumpProcess_pi (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P,
        Tendsto (fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k) t ω) atTop (𝓝 (Xp t ω)) := by
  obtain ⟨ms, hms, hae⟩ :=
    exists_seq_ae_tendsto_bigJumpProcess G hA hℱ0 hnull0 hanti hnull ht
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hae] with ω hω
  exact tendsto_pi_nhds.mpr hω
/-- The `L²` size of the compensated integral over the small marks at a time of the window is
bounded by the energy carried by those marks over the whole window. -/
theorem lintegral_sq_smallJumpIntegral_le (m : ℕ) (i : Fin n) {s T : ℝ}
    (hs : 0 ≤ s) (hsT : s ≤ T) :
    ∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rcases eq_or_lt_of_le hs with h0 | h0
  · have hz : ∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i s ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [smallJumpIntegral_ae_zero G hA hℱ0 hnull0 m i (le_of_eq h0.symm)]
        with ω hω
      simp [hω]
    rw [hz]
    exact zero_le
  · have hrw : ∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖stochasticIntegral N G.ℱ G.isPoisson
            (markCut (A m) (pathJumpCoeff coeffs Xp i))
            (measurable_markCut (G.meas i) (hA m)) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog i)) (hA m))
            (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') s ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [smallJumpIntegral_ae_eq G hA hℱ0 hnull0 m i s] with ω hω
      rw [hω]
    rw [hrw, isometry_stochasticIntegral N G.ℱ G.isPoisson
      (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
      ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog i)) (hA m))
      (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') s h0]
    exact lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right hsT)
include G hA in
/-- The energies carried by a shrinking family of marks over a fixed window vanish. -/
theorem tendsto_markCut_energy (hanti : Antitone A) (hnull : ν (⋂ m, A m) = 0) (i : Fin n)
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun m => ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      atTop (𝓝 0) := by
  have hiso : ∀ m : ℕ, ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
        = ∫⁻ ω, (‖stochasticIntegral N G.ℱ G.isPoisson
            (markCut (A m) (pathJumpCoeff coeffs Xp i))
            (measurable_markCut (G.meas i) (hA m)) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog i)) (hA m))
            (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro m
    exact (isometry_stochasticIntegral N G.ℱ G.isPoisson
      (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
      ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog i)) (hA m))
      (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') T hT).symm
  simp_rw [hiso]
  exact _root_.Prove2MeSourceProof.h_091ddfc298ddfc0879414135 N G.ℱ G.isPoisson
    (pathJumpCoeff coeffs Xp i) (G.meas i) (G.prog i) (G.sq i) A hA hanti hnull hT
/-- The energy over a bounded window of the compensated integral over the small marks is bounded
by the length of the window times the energy carried by those marks over it. -/
theorem lintegral_window_sq_smallJumpIntegral_le (m : ℕ) (i : Fin n) (T : ℝ) :
    ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖smallJumpIntegral G hA hℱ0 hnull0 m i s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P
      ≤ ENNReal.ofReal T * ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [MeasureTheory.lintegral_lintegral_swap
    (measurable_uncurry_sq_smallJumpIntegral G hA hℱ0 hnull0 m i).aemeasurable]
  calc ∫⁻ s in Set.Icc (0 : ℝ) T,
        (∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T, (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2
            ∂ν ∂volume ∂P) ∂volume := by
        refine MeasureTheory.setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        exact lintegral_sq_smallJumpIntegral_le G hA hℱ0 hnull0 m i hs.1 hs.2
    _ = ENNReal.ofReal T * ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2
            ∂ν ∂volume ∂P := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]
/-- The energy over a bounded window of the error between a coordinate of the big-jump process
and the path is bounded by the length of the window times the energy carried by the small
marks over it. -/
theorem lintegral_window_sq_bigJumpProcess_sub_le (m : ℕ) (i : Fin n) (T : ℝ) :
    ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖bigJumpProcess G hA hℱ0 hnull0 m s ω i - Xp s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P
      ≤ ENNReal.ofReal T * ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  have hnorm : ∀ (s : ℝ) (ω : Ω),
      (‖bigJumpProcess G hA hℱ0 hnull0 m s ω i - Xp s ω i‖₊ : ℝ≥0∞) ^ 2
        = (‖smallJumpIntegral G hA hℱ0 hnull0 m i s ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro s ω
    rw [bigJumpProcess_sub, nnnorm_neg]
  simp_rw [hnorm]
  exact lintegral_window_sq_smallJumpIntegral_le G hA hℱ0 hnull0 m i T
/-- **Along a subsequence the big-jump processes converge to the path at almost every time of a
bounded window, almost surely, in every coordinate at once.** -/
theorem exists_seq_ae_ae_tendsto_bigJumpProcess (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
        Tendsto (fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k) s ω i) atTop
          (𝓝 (Xp s ω i)) := by
  classical
  have hsumTendsto : Tendsto (fun m => ∑ i : Fin n, ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      atTop (𝓝 0) := by
    have hfin := tendsto_finsetSum (Finset.univ : Finset (Fin n))
      fun i _ => tendsto_markCut_energy G hA hanti hnull i hT
    simpa using hfin
  obtain ⟨ms, hmsge, hmslt⟩ :=
    LevyStochCalc.Brownian.Ito.exists_seq_lt_of_tendsto_zero hsumTendsto
  refine ⟨ms, hmsge, ?_⟩
  have hper : ∀ i : Fin n, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k) s ω i) atTop
        (𝓝 (Xp s ω i)) := by
    intro i
    have hsum : ∑' k : ℕ, ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖bigJumpProcess G hA hℱ0 hnull0 (ms k) s ω i - Xp s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P
          ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => ?_)
        (lt_top_iff_ne_top.mpr
          (LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top (ENNReal.ofReal T)
            ENNReal.ofReal_ne_top)))
      refine (lintegral_window_sq_bigJumpProcess_sub_le G hA hℱ0 hnull0 (ms k) i T).trans ?_
      refine mul_le_mul' le_rfl (le_of_lt (lt_of_le_of_lt ?_ (hmslt k)))
      exact Finset.single_le_sum
        (f := fun j : Fin n => ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut (A (ms k)) (pathJumpCoeff coeffs Xp j) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
        (fun _ _ => zero_le) (Finset.mem_univ i)
    filter_upwards [LevyStochCalc.Brownian.Ito.ae_tsum_ne_top_of_lintegral_summable (μ := P)
      (fun k => measurable_lintegral_sq_bigJumpProcess_sub G hA hℱ0 hnull0 (ms k) i T)
      hsum] with ω hω
    filter_upwards [LevyStochCalc.Brownian.Ito.ae_tendsto_zero_of_lintegral_summable
      (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (fun k => measurable_sq_bigJumpProcess_sub_time G hA hℱ0 hnull0 (ms k) i ω) hω] with s hs
    exact _root_.Prove2MeSourceProof.h_a4dbeae1c9a6b22bf7020922 hs
  filter_upwards [MeasureTheory.ae_all_iff.mpr hper] with ω hω
  exact MeasureTheory.ae_all_iff.mpr hω
/-- **Along a subsequence the big-jump vectors converge to the path at almost every time of a
bounded window, almost surely.** -/
theorem exists_seq_ae_ae_tendsto_bigJumpProcess_pi (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        Tendsto (fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k) s ω) atTop (𝓝 (Xp s ω)) := by
  obtain ⟨ms, hms, hae⟩ :=
    exists_seq_ae_ae_tendsto_bigJumpProcess G hA hℱ0 hnull0 hanti hnull hT
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hae] with ω hω
  filter_upwards [hω] with s hs
  exact tendsto_pi_nhds.mpr hs
/-- **The drift integrals along the big-jump processes, with the drift clamped at the levels of
the subsequence, converge to the drift integral along the path, at almost every sample
point.** -/
theorem exists_seq_ae_tendsto_drift_bigJumpProcess (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T)
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P, ∀ p : Fin n, Tendsto (fun k => ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (bigJumpProcess G hA hℱ0 hnull0 (ms k) s ω)
            * LevyStochCalc.Brownian.Ito.clampDrift b (ms k) p ω s ∂volume) atTop
        (𝓝 (∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (Xp s ω) * b p ω s ∂volume)) := by
  obtain ⟨ms, hms, hae⟩ :=
    exists_seq_ae_ae_tendsto_bigJumpProcess_pi G hA hℱ0 hnull0 hanti hnull hT
  refine ⟨ms, hms, ?_⟩
  exact _root_.Prove2MeSourceProof.h_d535c014a12fb1a12728f5c9 hf'c hf'bd hbm hbq
    (Y := fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k)) (X := Xp)
    (fun k => measurable_uncurry_bigJumpProcess_pi G hA hℱ0 hnull0 (ms k))
    hms hae
/-- **The quadratic-variation integrals along the big-jump processes, with the diffusion matrix
clamped at the levels of the subsequence, converge to the quadratic-variation integral along the
path, at almost every sample point.** -/
theorem exists_seq_ae_tendsto_quadVar_bigJumpProcess (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T)
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} (hf''c : Continuous f'')
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p l, Measurable (Function.uncurry (H p l)))
    (hq : ∀ (p : Fin n) (l : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p l ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P, ∀ p q : Fin n, Tendsto (fun k => ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv₂ f'' p q (bigJumpProcess G hA hℱ0 hnull0 (ms k) s ω)
            * ∑ l : Fin d, LevyStochCalc.Brownian.Ito.clampCoeff H (ms k) p l ω s
                * LevyStochCalc.Brownian.Ito.clampCoeff H (ms k) q l ω s ∂volume) atTop
        (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv₂ f'' p q (Xp s ω) * ∑ l : Fin d, H p l ω s * H q l ω s ∂volume)) := by
  obtain ⟨ms, hms, hae⟩ :=
    exists_seq_ae_ae_tendsto_bigJumpProcess_pi G hA hℱ0 hnull0 hanti hnull hT
  refine ⟨ms, hms, ?_⟩
  exact _root_.Prove2MeSourceProof.h_beebe463528d222d5e910101 hf''c hK₂0 hf''bd hm hq
    (Y := fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k)) (X := Xp)
    (fun k => measurable_uncurry_bigJumpProcess_pi G hA hℱ0 hnull0 (ms k)) hms hae
end Limits

/-- A twice continuously differentiable function of time and state is continuous in the state,
so it transports convergence of vectors. -/
theorem tendsto_comp_of_tendsto {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (t : ℝ) {z : ℕ → Fin n → ℝ} {w : Fin n → ℝ}
    (h : Tendsto z atTop (𝓝 w)) : Tendsto (fun k => u t (z k)) atTop (𝓝 (u t w)) := by
  have hc : Continuous fun y : Fin n → ℝ => u t y := by
    have heq : (fun y : Fin n → ℝ => u t y) = Function.uncurry u ∘ fun y => (t, y) := rfl
    rw [heq]
    exact hu.continuous.comp (continuous_const.prodMk continuous_id)
  exact (hc.tendsto w).comp h
/-- **A `C²` function of time and state, evaluated along the big-jump processes, converges to
its value along the path almost surely, along a subsequence.** -/
theorem exists_seq_ae_tendsto_comp (G : JumpIntegrand N coeffs Xp)
    (hA : ∀ m, MeasurableSet (A m))
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)
    (hanti : Antitone A) (hnull : ν (⋂ m, A m) = 0)
    {t : ℝ} (ht : 0 ≤ t) {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 (Function.uncurry u)) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k) t ω) atTop (𝓝 (Xp t ω))) ∧
      ∀ᵐ ω ∂P, Tendsto (fun k => u t (bigJumpProcess G hA hℱ0 hnull0 (ms k) t ω)) atTop
        (𝓝 (u t (Xp t ω))) := by
  obtain ⟨ms, hms, hae⟩ :=
    exists_seq_ae_tendsto_bigJumpProcess_pi G hA hℱ0 hnull0 hanti hnull ht
  refine ⟨ms, hms, hae, ?_⟩
  filter_upwards [hae] with ω hω
  exact tendsto_comp_of_tendsto hu t hω
end LevyStochCalc.Ito.SmallJump


