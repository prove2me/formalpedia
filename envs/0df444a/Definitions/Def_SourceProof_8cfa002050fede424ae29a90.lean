-- Prove2me | Definitions.Def_SourceProof_8cfa002050fede424ae29a90
-- name    : SourceProof_8cfa002050fede424ae29a90
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:49:45.750218+00:00
-- url     : https://prove2.me/theorems/60e5ac86-ca42-4077-bafa-e19f038504af
-- title:
--   LevyStochCalc source module: SourceProof_8cfa002050fede424ae29a90
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped` comes from the `LevyStochCalc.Brownian.VectorItoStopped` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoStopped_F001
import Definitions.Def_SourceProof_12c97cbc46c921129491cc08
import Definitions.Def_SourceProof_284ef0277f5e06a285dc439e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a vector Itô process

Cutting the coefficients of a vector Itô process off at a stopping time of finite range leaves a
vector Itô process, whose version is the original one evaluated at the clipped time.

## Main statements

* `LevyStochCalc.Brownian.Ito.clipTime` — the horizon clipped at a stopping time.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_clip` — the Itô integral of a
  stopped integrand is the integral evaluated at the clipped horizon.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped` — the stopped version.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Clip

variable {Ω : Type u}

variable {τ : Ω → WithTop ℝ} {t : ℝ} {ω : Ω}

end Clip

section StoppedIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsBrownianFiltration W ℱ) (τ : Ω → WithTop ℝ)

end StoppedIntegral

section StoppedDrift

variable {Ω : Type u}

end StoppedDrift

section StoppedVersion

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

include hcoord in

theorem _root_.Prove2MeSourceProof.h_8cfa002050fede424ae29a90
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    (J : Finset ℝ) (hJ0 : ∀ c ∈ J, 0 ≤ c)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ τ ω = ⊤) :
    IsVectorItoVersion W ℱ hcoord (fun p k => Probability.stopped τ (H p k))
      (fun p k => Probability.measurable_uncurry_stopped hτ (hHm p k))
      (fun p k => _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ (hHp p k))
      (fun p k => energy_lt_top_of_abs_le
        (fun ω s => Probability.abs_stopped_le τ (H p k) ω s) (hHs p k))
      X₀ (fun p => Probability.stopped τ (bdrift p))
      (fun t ω => X (clipTime τ t ω) ω) := by
  classical
  refine ⟨fun ω => (h.continuous_path ω).comp (LevyStochCalc.Brownian.Ito.continuous_clipTime τ ω),
    fun t => _root_.Prove2MeSourceProof.h_12c97cbc46c921129491cc08 ℱ hτ (fun r => h.adapted r) J hτJ t, ?_⟩
  intro t ht
  rcases eq_or_lt_of_le ht with rfl | ht'
  · have hclip : ∀ ω, LevyStochCalc.Brownian.Ito.clipTime τ (0 : ℝ) ω = 0 := fun ω => LevyStochCalc.Brownian.Ito.clipTime_of_le (hτ0 ω)
    filter_upwards [h.ae_eq 0 le_rfl,
      _root_.Prove2MeSourceProof.h_284ef0277f5e06a285dc439e W ℱ hcoord H hHm hHp hHs X₀ bdrift,
      _root_.Prove2MeSourceProof.h_284ef0277f5e06a285dc439e W ℱ hcoord (fun p k => LevyStochCalc.Probability.stopped τ (H p k))
        (fun p k => LevyStochCalc.Probability.measurable_uncurry_stopped hτ (hHm p k))
        (fun p k => _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ (hHp p k))
        (fun p k => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le
          (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ (H p k) ω s) (hHs p k))
        X₀ (fun p => LevyStochCalc.Probability.stopped τ (bdrift p))] with ω e1 e2 e3
    simp only [hclip ω]
    rw [e1, e2, e3]
  · set J' : Finset ℝ := J.filter (fun c => c < t) with hJ'def
    have hJ'0 : ∀ c ∈ J', 0 ≤ c := fun c hc => hJ0 c (Finset.mem_filter.mp hc).1
    have hJ't : ∀ c ∈ J', c < t := fun c hc => (Finset.mem_filter.mp hc).2
    have hτJ' : ∀ ω, (∃ c ∈ J', τ ω = ((c : ℝ) : WithTop ℝ))
        ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω := by
      intro ω
      rcases hτJ ω with ⟨c, hcJ, hceq⟩ | htop
      · by_cases hlt : c < t
        · exact Or.inl ⟨c, Finset.mem_filter.mpr ⟨hcJ, hlt⟩, hceq⟩
        · refine Or.inr ?_
          rw [hceq]
          exact_mod_cast le_of_not_gt hlt
      · refine Or.inr ?_
        rw [htop]
        exact le_top
    have hclip0 : ∀ ω, 0 ≤ LevyStochCalc.Brownian.Ito.clipTime τ t ω := fun ω => LevyStochCalc.Brownian.Ito.clipTime_nonneg ht (hτ0 ω)
    have hmemc : ∀ ω, LevyStochCalc.Brownian.Ito.clipTime τ t ω ∈ insert t (J : Set ℝ) := by
      intro ω
      rcases hτJ ω with ⟨c, hcJ, hceq⟩ | htop
      · rw [LevyStochCalc.Brownian.Ito.clipTime_eq_min hceq]
        rcases min_choice t c with hmin | hmin
        · rw [hmin]
          exact Set.mem_insert _ _
        · rw [hmin]
          exact Set.mem_insert_of_mem _ hcJ
      · rw [LevyStochCalc.Brownian.Ito.clipTime_eq_self_of_top htop]
        exact Set.mem_insert _ _
    have hcount : (insert t (J : Set ℝ)).Countable := (J.countable_toSet).insert t
    have hval : ∀ᵐ ω ∂P, ∀ c ∈ insert t (J : Set ℝ), 0 ≤ c →
        X c ω = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift c ω := by
      rw [MeasureTheory.ae_ball_iff hcount]
      intro c _
      by_cases hc0 : 0 ≤ c
      · filter_upwards [h.ae_eq c hc0] with ω hω
        exact fun _ => hω
      · exact Filter.Eventually.of_forall fun ω hcon => absurd hcon hc0
    have hSIall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (LevyStochCalc.Probability.stopped τ (H p k))
            (LevyStochCalc.Probability.measurable_uncurry_stopped hτ (hHm p k))
            (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ (hHp p k))
            (LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le
              (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ (H p k) ω s) (hHs p k)) t ω
          = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
              (hHs p k) (LevyStochCalc.Brownian.Ito.clipTime τ t ω) ω := by
      rw [MeasureTheory.ae_all_iff]
      intro p
      rw [MeasureTheory.ae_all_iff]
      intro k
      exact LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_clip (W.W k) ℱ (hcoord k) τ hτ (hHm p k)
        (hHp p k) (hHs p k) ht' J' hJ'0 hJ't hτJ'
    filter_upwards [hval, hSIall] with ω e1 e2
    rw [e1 (LevyStochCalc.Brownian.Ito.clipTime τ t ω) (hmemc ω) (hclip0 ω)]
    funext m
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess, vectorItoMartingale, coordItoIntegral]
    rw [LevyStochCalc.Brownian.Ito.setIntegral_stopped_eq τ (bdrift m) ω]
    congr 1
    exact Finset.sum_congr rfl fun k _ => (e2 m k).symm
end StoppedVersion

end LevyStochCalc.Brownian.Ito


