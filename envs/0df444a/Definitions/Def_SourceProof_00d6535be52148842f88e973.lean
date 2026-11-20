-- Prove2me | Definitions.Def_SourceProof_00d6535be52148842f88e973
-- name    : SourceProof_00d6535be52148842f88e973
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:29:38.198923+00:00
-- url     : https://prove2.me/theorems/3ef0c31a-1c41-4560-99e0-a5b45f0ee7fc
-- title:
--   LevyStochCalc source module: SourceProof_00d6535be52148842f88e973
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification` comes from the `LevyStochCalc.Brownian.Continuity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_14a201cfcde1fac50a3f98f3
import Definitions.Def_SourceProof_4f2f777d7b8195920e6605d0
import Definitions.Def_SourceProof_810e94ff6e782faa7ab0a648

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Kolmogorov-Chentsov continuous modification

Mathlib has only `IsKolmogorovProcess` (the *condition*); the modification
result is missing. We port the classical proof (Karatzas-Shreve §2.2 Thm 2.8 /
Le Gall 2016 Thm 2.9):

  *If `(X_t)_{t ≥ 0}` satisfies `𝔼[ |X_t − X_s|^p ] ≤ M · |t − s|^q` for some
  `p, q > 0` with `q > 1` and constant `M`, then there exists a modification
  `X̃` with continuous paths.*

The sub-lemmas of the proof live in two imported modules of the same namespace:
`LevyStochCalc.Brownian.ContinuityDyadicChaining` (Hölder extension from a dense
set, the dyadic rationals, dyadic truncation and the deterministic chaining
bound) and `LevyStochCalc.Brownian.ContinuityKolmogorovBounds` (the Markov tail
bound, the per-level Borel-Cantelli estimates, almost-sure local Hölder
regularity and the modification identity). This module assembles them into
`kolmogorovChentsov_modification` and applies it to Brownian motion, whose
fourth increment moment is computed here from the Gaussian moment generating
function.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_00d6535be52148842f88e973
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (hq : 1 < q) :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧
      (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω) := by
  have hp : 0 < p := hX.p_pos
  set α : ℝ := (q - 1) / (2 * p) with hα_def
  have hα0 : 0 < α := by rw [hα_def]; exact div_pos (by linarith) (by linarith)
  have hαpq : α * p < q - 1 := by
    have h2p : 0 < 2 * p := by linarith
    rw [hα_def, div_mul_eq_mul_div, div_lt_iff₀ h2p]
    nlinarith [mul_pos (show (0:ℝ) < q - 1 from by linarith) hp]
  set Y : ℝ → Ω → ℝ :=
    fun t ω => extendFrom LevyStochCalc.Brownian.Continuity.dyadicRationals (fun s => X s ω) t with hY_def
  have hnbhd := _root_.Prove2MeSourceProof.h_4f2f777d7b8195920e6605d0 P X hX hα0 hαpq
  have hcont : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω) := by
    filter_upwards [hnbhd] with ω hω
    exact continuous_extendFrom _root_.Prove2MeSourceProof.h_8cc83ed884458283276d879b
      (fun t => _root_.Prove2MeSourceProof.h_14a201cfcde1fac50a3f98f3 _root_.Prove2MeSourceProof.h_8cc83ed884458283276d879b hα0 t (hω t))
  refine ⟨Y, hcont, ?_⟩
  refine _root_.Prove2MeSourceProof.h_810e94ff6e782faa7ab0a648 P X hX Y hcont ?_
  intro s hs
  filter_upwards [hnbhd] with ω hω
  -- `Y s ω = extendFrom dyadicRationals (· ↦ X · ω) s = X s ω`
  refine extendFrom_eq (subset_closure hs) ?_
  obtain ⟨K, ρ, hρ, hK0, hHol⟩ := hω s
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min ρ ((ε / (K + 1)) ^ (1 / α)),
    lt_min hρ (Real.rpow_pos_of_pos (by positivity) _), fun u hu hdu => ?_⟩
  have huρ : u ∈ Set.Ioo (s - ρ) (s + ρ) := by
    rw [Real.dist_eq] at hdu
    have := lt_of_lt_of_le hdu (min_le_left _ _)
    rw [abs_lt] at this; exact ⟨by linarith, by linarith⟩
  have hsρ : s ∈ Set.Ioo (s - ρ) (s + ρ) := ⟨by linarith, by linarith⟩
  have hb := hHol u hu s hs huρ hsρ
  have hdu2 : |u - s| < (ε / (K + 1)) ^ (1 / α) := by
    rw [← Real.dist_eq]; exact lt_of_lt_of_le hdu (min_le_right _ _)
  have hpow : |u - s| ^ α < ε / (K + 1) := by
    have h1 := Real.rpow_lt_rpow (abs_nonneg _) hdu2 hα0
    rwa [show ((ε / (K + 1)) ^ (1 / α)) ^ α = ε / (K + 1) from by
      rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ (ne_of_gt hα0),
          Real.rpow_one]] at h1
  rw [Real.dist_eq]
  calc |X u ω - X s ω| ≤ K * |u - s| ^ α := hb
    _ ≤ (K + 1) * |u - s| ^ α := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ < (K + 1) * (ε / (K + 1)) := by apply mul_lt_mul_of_pos_left hpow (by positivity)
    _ = ε := by field_simp
end LevyStochCalc.Brownian.Continuity


