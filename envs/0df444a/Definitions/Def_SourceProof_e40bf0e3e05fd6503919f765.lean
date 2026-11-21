-- Prove2me | Definitions.Def_SourceProof_e40bf0e3e05fd6503919f765
-- name    : SourceProof_e40bf0e3e05fd6503919f765
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:15:07.500583+00:00
-- url     : https://prove2.me/theorems/a20edd05-2bca-49f9-acb6-7da19a558b8d
-- title:
--   LevyStochCalc source module: SourceProof_e40bf0e3e05fd6503919f765
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded` comes from the `LevyStochCalc.Ito.VectorItoVersionLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F002
import Definitions.Def_LevyStochCalc_Ito_VectorItoVersionLimit_F000
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F001
import Definitions.Def_SourceProof_0ac980e224d4498dc611b565
import Definitions.Def_SourceProof_755d31da2fec92eb2a10cfd6
import Definitions.Def_SourceProof_a4dbeae1c9a6b22bf7020922
import Definitions.Def_SourceProof_e9ca47f3989207170842a61a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Continuous versions of vector Itô processes with unbounded coefficients

Clamping the coefficients at a level whose mesh decays geometrically on every bounded window
produces versions whose window suprema of consecutive differences are summable almost surely,
hence converge uniformly on compact time sets; the limit is a continuous adapted version of the
vector Itô process driven by the unclamped coefficients.

## Main statements

* `LevyStochCalc.Brownian.Ito.clampMesh_mono_window` — the clamping mesh grows with the window.
* `LevyStochCalc.Brownian.Ito.exists_seq_clampMesh_window_lt` — clamping levels along which the
  mesh of every window decays geometrically.
* `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded` — a continuous adapted
  version of a vector Itô process whose coefficients have finite energy on every window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal Topology

universe u

section Elementary

end Elementary

section Mesh

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

end Mesh

section Limit

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}


theorem _root_.Prove2MeSourceProof.h_e40bf0e3e05fd6503919f765
    (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ (bdrift p))
    (hbq : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ X : ℝ → Ω → Fin n → ℝ,
      IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X := by
  classical
  have hle0 : ∀ t : ℝ, ℱ 0 ≤ ℱ t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact ℱ.mono ht
    · exact hℱ0 t ht.le
  have hX₀' : ∀ p : Fin n, Measurable fun ω => X₀ ω p := fun p => (hX₀ p).mono (ℱ.le 0) le_rfl
  obtain ⟨ms, hmsge, hmslt⟩ := LevyStochCalc.Brownian.Ito.exists_seq_clampMesh_window_lt (P := P) hHm hbm hHs hbq
  have hex : ∀ j : ℕ, ∃ Z : ℝ → Ω → Fin n → ℝ,
      LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord (LevyStochCalc.Brownian.Ito.clampCoeff H j)
        (fun p k => LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm j p k)
        (fun p k => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp j p k)
        (fun p k T' hT' => LevyStochCalc.Brownian.Ito.energy_clampCoeff_lt_top j p k T' hT')
        X₀ (LevyStochCalc.Brownian.Ito.clampDrift bdrift j) Z := fun j =>
    _root_.Prove2MeSourceProof.h_e135e60f4c0109b1a168208c W ℱ hcoord (LevyStochCalc.Brownian.Ito.clampCoeff H j)
      (fun p k => LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm j p k)
      (fun p k => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp j p k)
      (fun p k T' hT' => LevyStochCalc.Brownian.Ito.energy_clampCoeff_lt_top j p k T' hT')
      (Nat.cast_nonneg j) (LevyStochCalc.Brownian.Ito.abs_clampCoeff_le H j) hℱ0 hnull hX₀ (LevyStochCalc.Brownian.Ito.clampDrift bdrift j)
      (fun p => LevyStochCalc.Brownian.Ito.measurable_clampDrift hbm j p)
      (fun p => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampDrift hbp j p)
      (Nat.cast_nonneg j) (LevyStochCalc.Brownian.Ito.abs_clampDrift_le bdrift j)
  choose Xj hXj using hex
  -- the window suprema of consecutive differences, in dyadic form
  obtain ⟨Sraw, hSraw⟩ : ∃ Sraw : ℕ → ℕ → Ω → ℝ≥0∞,
      Sraw = fun (m i : ℕ) (ω : Ω) => ⨆ q : ℕ,
      (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => ‖Xj (ms (i + 1)) t ω - Xj (ms i) t ω‖)
        ((m : ℝ) + 1) q ω‖₊ : ℝ≥0∞) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → ℕ → Ω → ℝ≥0∞,
      S = fun (m i : ℕ) (ω : Ω) => if m ≤ i then Sraw m i ω else 0 := ⟨_, rfl⟩
  have hArm : ∀ (i : ℕ) (t : ℝ),
      Measurable fun ω => ‖Xj (ms (i + 1)) t ω - Xj (ms i) t ω‖ :=
    fun i t => (((hXj (ms (i + 1))).measurable t).sub ((hXj (ms i)).measurable t)).norm
  have hSrawm : ∀ m i : ℕ, Measurable (Sraw m i) := by
    intro m i
    simp only [hSraw]
    exact Measurable.iSup fun q => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hArm i) ((m : ℝ) + 1) q
  have hSm : ∀ m i : ℕ, Measurable (S m i) := by
    intro m i
    by_cases h : m ≤ i
    · simpa [hSdef, h] using hSrawm m i
    · simp [hSdef, h]
  have hSrawEq : ∀ (m i : ℕ) (ω : Ω), Sraw m i ω
      = ⨆ t : Set.Icc (0 : ℝ) ((m : ℝ) + 1),
        (‖Xj (ms (i + 1)) (t : ℝ) ω - Xj (ms i) (t : ℝ) ω‖₊ : ℝ≥0∞) := by
    intro m i ω
    have hcont : Continuous fun t : ℝ => ‖Xj (ms (i + 1)) t ω - Xj (ms i) t ω‖ :=
      (((hXj (ms (i + 1))).continuous_path ω).sub ((hXj (ms i)).continuous_path ω)).norm
    have hcad : ∀ t : ℝ, Filter.Tendsto
        (fun s => ‖Xj (ms (i + 1)) s ω - Xj (ms i) s ω‖) (nhdsWithin t (Set.Ioi t))
        (nhds ‖Xj (ms (i + 1)) t ω - Xj (ms i) t ω‖) :=
      fun t => (hcont.tendsto t).mono_left nhdsWithin_le_nhds
    simp only [hSraw]
    rw [← _root_.Prove2MeSourceProof.h_755d31da2fec92eb2a10cfd6
      (M := fun t ω => ‖Xj (ms (i + 1)) t ω - Xj (ms i) t ω‖) (T := (m : ℝ) + 1) (ω := ω)
      (by positivity) hcad]
    exact iSup_congr fun t => by rw [nnnorm_norm]
  -- the geometric decay of the window energies
  have hSsq : ∀ m i : ℕ, m ≤ i →
      ∫⁻ ω, (S m i ω) ^ 2 ∂P ≤ 64 * (n : ℝ≥0∞) ^ 2 * ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by
    intro m i hmi
    have hTpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hkey := _root_.Prove2MeSourceProof.h_e9ca47f3989207170842a61a W ℱ hcoord (H := H)
      (hm := hHm) (hpg := hHp) hbm (hXj (ms i)) (hXj (ms (i + 1))) hTpos
    have hmr : (m : ℝ) ≤ (i : ℝ) := by exact_mod_cast hmi
    have hmle : ((m : ℝ) + 1) ≤ (i : ℝ) + 1 := by linarith
    have hle1 : LevyStochCalc.Brownian.Ito.clampMesh P H bdrift ((m : ℝ) + 1) (ms i) ≤ ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) :=
      le_trans (LevyStochCalc.Brownian.Ito.clampMesh_mono_window P H bdrift hmle (ms i)) (hmslt i).le
    have hmle2 : ((m : ℝ) + 1) ≤ ((i + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    have hle2 : LevyStochCalc.Brownian.Ito.clampMesh P H bdrift ((m : ℝ) + 1) (ms (i + 1))
        ≤ ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by
      refine le_trans (LevyStochCalc.Brownian.Ito.clampMesh_mono_window P H bdrift hmle2 (ms (i + 1))) ?_
      exact le_trans (hmslt (i + 1)).le (LevyStochCalc.Brownian.Ito.pow_inv_two_antitone (by omega))
    have hrw : ∀ ω : Ω, S m i ω
        = ⨆ t : Set.Icc (0 : ℝ) ((m : ℝ) + 1),
          (‖Xj (ms (i + 1)) (t : ℝ) ω - Xj (ms i) (t : ℝ) ω‖₊ : ℝ≥0∞) := by
      intro ω
      simp only [hSdef]
      rw [if_pos hmi]
      exact hSrawEq m i ω
    calc ∫⁻ ω, (S m i ω) ^ 2 ∂P
        = ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) ((m : ℝ) + 1),
            (‖Xj (ms (i + 1)) (t : ℝ) ω - Xj (ms i) (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P := by
          exact MeasureTheory.lintegral_congr fun ω => by rw [hrw ω]
      _ ≤ 32 * (n : ℝ≥0∞) ^ 2 * (LevyStochCalc.Brownian.Ito.clampMesh P H bdrift ((m : ℝ) + 1) (ms i)
            + LevyStochCalc.Brownian.Ito.clampMesh P H bdrift ((m : ℝ) + 1) (ms (i + 1))) := hkey
      _ ≤ 32 * (n : ℝ≥0∞) ^ 2 * (((2 : ℝ≥0∞)⁻¹) ^ (2 * i) + ((2 : ℝ≥0∞)⁻¹) ^ (2 * i)) := by
          gcongr
      _ = 64 * (n : ℝ≥0∞) ^ 2 * ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by ring
  have hSint : ∀ m i : ℕ, m ≤ i →
      ∫⁻ ω, S m i ω ∂P ≤ (1 + 64 * (n : ℝ≥0∞) ^ 2) * ((2 : ℝ≥0∞)⁻¹) ^ i := by
    intro m i hmi
    have h2 : ((2 : ℝ≥0∞)⁻¹) ≠ 0 := by simp
    have h2t : ((2 : ℝ≥0∞)⁻¹) ≠ ⊤ := by simp
    have hε0 : ((2 : ℝ≥0∞)⁻¹) ^ i ≠ 0 := pow_ne_zero i h2
    have hεt : ((2 : ℝ≥0∞)⁻¹) ^ i ≠ ⊤ := ENNReal.pow_ne_top h2t
    have hsq : ∫⁻ ω, (S m i ω) ^ 2 ∂P
        ≤ 64 * (n : ℝ≥0∞) ^ 2 * (((2 : ℝ≥0∞)⁻¹) ^ i) ^ 2 := by
      have h := hSsq m i hmi
      rwa [show ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) = (((2 : ℝ≥0∞)⁻¹) ^ i) ^ 2 by
        rw [two_mul, pow_add, sq]] at h
    refine (LevyStochCalc.Brownian.Ito.lintegral_le_add_inv_mul_of_sq_le (S m i) hε0 hεt hsq).trans (le_of_eq ?_)
    have hcancel : (((2 : ℝ≥0∞)⁻¹) ^ i)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ i = 1 :=
      ENNReal.inv_mul_cancel hε0 hεt
    calc ((2 : ℝ≥0∞)⁻¹) ^ i
          + (((2 : ℝ≥0∞)⁻¹) ^ i)⁻¹ * (64 * (n : ℝ≥0∞) ^ 2 * (((2 : ℝ≥0∞)⁻¹) ^ i) ^ 2)
        = ((2 : ℝ≥0∞)⁻¹) ^ i + 64 * (n : ℝ≥0∞) ^ 2
            * ((((2 : ℝ≥0∞)⁻¹) ^ i)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ i * ((2 : ℝ≥0∞)⁻¹) ^ i) := by ring
      _ = (1 + 64 * (n : ℝ≥0∞) ^ 2) * ((2 : ℝ≥0∞)⁻¹) ^ i := by rw [hcancel]; ring
  have htsum : ∀ m : ℕ, ∑' i : ℕ, ∫⁻ ω, S m i ω ∂P ≠ ⊤ := by
    intro m
    have hC : (1 + 64 * (n : ℝ≥0∞) ^ 2) ≠ ⊤ := by finiteness
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => ?_)
      (lt_top_iff_ne_top.mpr (LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top _ hC)))
    by_cases hmi : m ≤ i
    · exact hSint m i hmi
    · have hz : ∫⁻ ω, S m i ω ∂P = 0 := by simp [hSdef, hmi]
      rw [hz]
      exact zero_le
  have hae : ∀ᵐ ω ∂P, ∀ m : ℕ, ∑' i : ℕ, S m i ω ≠ ⊤ := by
    rw [MeasureTheory.ae_all_iff]
    intro m
    exact LevyStochCalc.Brownian.Ito.ae_tsum_ne_top_of_lintegral_summable (μ := P) (hSm m) (htsum m)
  -- the almost sure event of uniform convergence
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ∀ m : ℕ, ∑' i : ℕ, S m i ω ≠ ⊤} := ⟨_, rfl⟩
  have hGmeas : MeasurableSet G := by
    have hGeq : G = ⋂ m : ℕ, (fun ω => ∑' i : ℕ, S m i ω) ⁻¹' {(⊤ : ℝ≥0∞)}ᶜ := by
      ext ω
      simp [hGdef]
    rw [hGeq]
    refine MeasurableSet.iInter fun m => ?_
    exact (Measurable.tsum fun i => hSm m i) (measurableSet_singleton _).compl
  have hGnull : P Gᶜ = 0 := by
    have h1 : ∀ᵐ ω ∂P, ω ∈ G := by
      filter_upwards [hae] with ω hω
      rw [hGdef]
      exact hω
    exact MeasureTheory.ae_iff.mp h1
  have hG0 : MeasurableSet[ℱ 0] G := by
    have h := hnull Gᶜ hGmeas.compl hGnull
    simpa using h.compl
  -- uniform convergence of the clamped versions on every bounded window
  have hUnif : ∀ ω : Ω, ω ∈ G → ∀ m : ℕ, ∃ L : ℝ → Fin n → ℝ,
      TendstoUniformlyOn (fun N (t : ℝ) => Xj (ms N) (max t 0) ω) L Filter.atTop
        (Set.Iic ((m : ℝ) + 1)) := by
    intro ω hωG m
    have hω : ∀ m' : ℕ, ∑' i : ℕ, S m' i ω ≠ ⊤ := by rw [hGdef] at hωG; exact hωG
    have hsum0 : Summable fun i : ℕ => (S m i ω).toReal := ENNReal.summable_toReal (hω m)
    have hsum1 : Summable fun i : ℕ => (S m (i + m) ω).toReal :=
      (summable_nat_add_iff m).mpr hsum0
    have hne : ∀ i : ℕ, S m i ω ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top (hω m)
    have hbnd : ∀ (i : ℕ) (x : ℝ), x ∈ Set.Iic ((m : ℝ) + 1) →
        ‖Xj (ms (i + 1 + m)) (max x 0) ω - Xj (ms (i + m)) (max x 0) ω‖
          ≤ (S m (i + m) ω).toReal := by
      intro i x hx
      have hmem : max x 0 ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1) :=
        ⟨le_max_right x 0, max_le (Set.mem_Iic.mp hx) (by positivity)⟩
      rw [show i + 1 + m = i + m + 1 from by omega]
      have hle : (‖Xj (ms (i + m + 1)) (max x 0) ω
          - Xj (ms (i + m)) (max x 0) ω‖₊ : ℝ≥0∞) ≤ S m (i + m) ω := by
        simp only [hSdef]
        rw [if_pos (Nat.le_add_left m i), hSrawEq]
        exact le_iSup (fun t : Set.Icc (0 : ℝ) ((m : ℝ) + 1) =>
          (‖Xj (ms (i + m + 1)) (t : ℝ) ω - Xj (ms (i + m)) (t : ℝ) ω‖₊ : ℝ≥0∞))
          ⟨max x 0, hmem⟩
      have := ENNReal.toReal_mono (hne (i + m)) hle
      simpa using this
    have hMT := tendstoUniformlyOn_tsum_nat (u := fun i : ℕ => (S m (i + m) ω).toReal) hsum1
      (s := Set.Iic ((m : ℝ) + 1))
      (f := fun (i : ℕ) (x : ℝ) =>
        Xj (ms (i + 1 + m)) (max x 0) ω - Xj (ms (i + m)) (max x 0) ω) hbnd
    have heq : (fun (N : ℕ) (x : ℝ) => ∑ i ∈ Finset.range N,
          (Xj (ms (i + 1 + m)) (max x 0) ω - Xj (ms (i + m)) (max x 0) ω))
        = fun (N : ℕ) (x : ℝ) =>
          Xj (ms (N + m)) (max x 0) ω - Xj (ms (0 + m)) (max x 0) ω := by
      funext N x
      exact Finset.sum_range_sub (fun i => Xj (ms (i + m)) (max x 0) ω) N
    rw [heq] at hMT
    refine ⟨_, LevyStochCalc.Brownian.Ito.tendstoUniformlyOn_of_shift (fun N (t : ℝ) => Xj (ms N) (max t 0) ω) m
      (LevyStochCalc.Brownian.Ito.tendstoUniformlyOn_of_sub_const (fun N (t : ℝ) => Xj (ms (N + m)) (max t 0) ω)
        (fun t : ℝ => Xj (ms (0 + m)) (max t 0) ω) hMT)⟩
  -- the limit process
  obtain ⟨Xlim, hXlim⟩ : ∃ f : ℝ → Ω → Fin n → ℝ, f = fun t ω =>
      if ω ∈ G then Filter.limUnder Filter.atTop (fun N => Xj (ms N) (max t 0) ω)
      else 0 := ⟨_, rfl⟩
  have hPt : ∀ ω : Ω, ω ∈ G → ∀ t : ℝ,
      Filter.Tendsto (fun N => Xj (ms N) (max t 0) ω) Filter.atTop (𝓝 (Xlim t ω)) := by
    intro ω hωG t
    obtain ⟨L, hL⟩ := hUnif ω hωG ⌈t⌉₊
    have hmem : t ∈ Set.Iic ((⌈t⌉₊ : ℝ) + 1) := by
      have := Nat.le_ceil t
      simp only [Set.mem_Iic]
      linarith
    have hLt := hL.tendsto_at hmem
    have hval : Xlim t ω = L t := by
      simp only [hXlim]
      rw [if_pos hωG, hLt.limUnder_eq]
    rw [hval]
    exact hLt
  -- continuity of the limit paths
  have hcont : ∀ ω : Ω, Continuous fun t => Xlim t ω := by
    intro ω
    by_cases hωG : ω ∈ G
    · rw [continuous_iff_continuousAt]
      intro t
      obtain ⟨L, hL⟩ := hUnif ω hωG ⌈|t|⌉₊
      have hEq : Set.EqOn L (fun s => Xlim s ω) (Set.Iic ((⌈|t|⌉₊ : ℝ) + 1)) := by
        intro s hs
        exact tendsto_nhds_unique (hL.tendsto_at hs) (hPt ω hωG s)
      have hL' : TendstoUniformlyOn (fun N (s : ℝ) => Xj (ms N) (max s 0) ω)
          (fun s => Xlim s ω) Filter.atTop (Set.Iic ((⌈|t|⌉₊ : ℝ) + 1)) := hL.congr_right hEq
      have hCon : ContinuousOn (fun s => Xlim s ω) (Set.Iic ((⌈|t|⌉₊ : ℝ) + 1)) := by
        refine hL'.continuousOn (Filter.Eventually.frequently
          (Filter.Eventually.of_forall fun N => ?_))
        have hmax : Continuous fun s : ℝ => max s 0 := continuous_id.max continuous_const
        exact (((hXj (ms N)).continuous_path ω).comp hmax).continuousOn
      refine hCon.continuousAt (Iic_mem_nhds ?_)
      have h1 : |t| ≤ (⌈|t|⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : t ≤ |t| := le_abs_self t
      linarith
    · have hz : (fun t => Xlim t ω) = fun _ => (0 : Fin n → ℝ) := by
        funext t
        simp only [hXlim]
        exact if_neg hωG
      rw [hz]
      exact continuous_const
  -- adaptedness of the limit
  have hadapt : ∀ t : ℝ, StronglyMeasurable[ℱ t] (Xlim t) := by
    intro t
    have hmaxle : ℱ (max t 0) ≤ ℱ t := by
      rcases le_or_gt 0 t with ht | ht
      · rw [max_eq_left ht]
      · rw [max_eq_right ht.le]
        exact hle0 t
    have hGt : MeasurableSet[ℱ t] G := hle0 t _ hG0
    have hFN : ∀ N : ℕ,
        Measurable[ℱ t] (Set.indicator G fun ω => Xj (ms N) (max t 0) ω) := by
      intro N
      refine Measurable.indicator ?_ hGt
      exact ((hXj (ms N)).adapted (max t 0)).measurable.mono hmaxle le_rfl
    refine Measurable.stronglyMeasurable ?_
    letI : MeasurableSpace Ω := ℱ t
    refine measurable_of_tendsto_metrizable' Filter.atTop hFN ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hωG : ω ∈ G
    · simpa [Set.indicator_of_mem hωG] using hPt ω hωG t
    · simp only [Set.indicator_of_notMem hωG]
      simp only [hXlim]
      rw [if_neg hωG]
      exact tendsto_const_nhds
  refine ⟨Xlim, hcont, hadapt, ?_⟩
  intro t ht
  rcases eq_or_lt_of_le ht with h0 | htpos
  · -- the initial time
    have hzero : ∀ᵐ ω ∂P, ∀ j : ℕ, Xj j 0 ω = X₀ ω := by
      rw [MeasureTheory.ae_all_iff]
      intro j
      exact _root_.Prove2MeSourceProof.h_0ac980e224d4498dc611b565 W ℱ hcoord (hXj j)
    have hvip := LevyStochCalc.Brownian.Ito.vectorItoProcess_ae_eq_zero W ℱ hcoord hHm hHp hHs X₀ bdrift
    filter_upwards [hzero, hvip, hae] with ω hz hv hωG
    have hωG' : ω ∈ G := by rw [hGdef]; exact hωG
    have hlim := hPt ω hωG' t
    rw [← h0] at hlim ⊢
    simp only [max_self] at hlim
    have hconst : Filter.Tendsto (fun N => Xj (ms N) (0 : ℝ) ω) Filter.atTop (𝓝 (X₀ ω)) := by
      refine Filter.Tendsto.congr (fun N => (hz (ms N)).symm) tendsto_const_nhds
    rw [tendsto_nhds_unique hlim hconst, hv]
  · -- positive times
    have hN : ∀ i : ℕ, t ≤ ((i + ⌈t⌉₊ : ℕ) : ℝ) + 1 := by
      intro i
      have h1 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
      have h2 : ((⌈t⌉₊ : ℕ) : ℝ) ≤ ((i + ⌈t⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_left ⌈t⌉₊ i
      linarith
    have hbound : ∀ i : ℕ, ∫⁻ ω, (‖Xj (ms (i + ⌈t⌉₊)) t ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          ≤ ((2 : ℝ≥0∞)⁻¹) ^ i := by
      intro i
      refine le_trans (le_of_eq ?_) (le_trans (_root_.Prove2MeSourceProof.h_017cdf5d7acbcd18b949050e W ℱ hcoord
        hHm hHp hHs hX₀' hbm hbq (ms (i + ⌈t⌉₊)) htpos (hN i)) ?_)
      · refine MeasureTheory.lintegral_congr_ae ?_
        filter_upwards [(hXj (ms (i + ⌈t⌉₊))).ae_eq t htpos.le] with ω hω
        rw [hω]
      · exact le_trans (hmslt (i + ⌈t⌉₊)).le (LevyStochCalc.Brownian.Ito.pow_inv_two_antitone (by omega))
    have hmeas : ∀ i : ℕ, Measurable fun ω => (‖Xj (ms (i + ⌈t⌉₊)) t ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro i
      have h1 : Measurable fun ω => Xj (ms (i + ⌈t⌉₊)) t ω := (hXj (ms (i + ⌈t⌉₊))).measurable t
      have h2 : Measurable (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t) :=
        LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess W ℱ hcoord H hHm hHp hHs hX₀' hbm t
      exact (((h1.sub h2).nnnorm).coe_nnreal_ennreal).pow_const 2
    have hsum : ∑' i : ℕ, ∫⁻ ω, (‖Xj (ms (i + ⌈t⌉₊)) t ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≠ ⊤ := by
      have hgeom := LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top (1 : ℝ≥0∞) (by simp)
      refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound) ?_)
      refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_iff_ne_top.mpr hgeom)
      exact tsum_congr fun i => (one_mul _).symm
    filter_upwards [LevyStochCalc.Brownian.Ito.ae_tendsto_zero_of_lintegral_summable (μ := P) hmeas hsum, hae]
      with ω hω hωG
    have hωG' : ω ∈ G := by rw [hGdef]; exact hωG
    have h1 : Filter.Tendsto (fun i => Xj (ms (i + ⌈t⌉₊)) t ω) Filter.atTop
        (𝓝 (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t ω)) :=
      _root_.Prove2MeSourceProof.h_a4dbeae1c9a6b22bf7020922 hω
    have h2 : Filter.Tendsto (fun i => Xj (ms (i + ⌈t⌉₊)) t ω) Filter.atTop (𝓝 (Xlim t ω)) := by
      have h3 := hPt ω hωG' t
      rw [max_eq_left ht] at h3
      exact h3.comp (Filter.tendsto_add_atTop_nat ⌈t⌉₊)
    exact tendsto_nhds_unique h2 h1
end Limit

end LevyStochCalc.Brownian.Ito


