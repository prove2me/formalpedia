-- Prove2me | solution 1 for Arxivcond_mat_0004049.delay_time_tails
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T13:58:42.824667+00:00
-- url     : https://prove2.me/submissions/bb7eaac9-393a-49f1-8101-78c086da2548
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Arxivcond_mat_0004049_delay_time_tails_localized
import Theorems.Thm_Arxivcond_mat_0004049_pDiff_tails

open MeasureTheory Filter Topology
open Arxivcond_mat_0004049

theorem solution (γ : ℝ) (hγ : 0 < γ) :
    (∃ g : ℝ → ℝ, Continuous g ∧ (∀ y, 0 ≤ g y) ∧
      LawTendsto γ
        (fun N (ω : Sample N) => delayNe ω / (γ * N * Real.sqrt N))
        ((volume : Measure ℝ).withDensity (fun y => ENNReal.ofReal (g y))) ∧
      ∃ c : ℝ, 0 < c ∧ Tendsto (fun y => y ^ 2 * g y) atTop (𝓝 c) ∧
        Tendsto (fun y => y ^ 2 * g y) atBot (𝓝 c)) ∧
    ∀ Q phibar : ℝ, 0 < Q → 0 < phibar → ∃ c : ℝ, 0 < c ∧
      Tendsto (fun φ => |φ| ^ 3 * pDiff Q phibar φ) atTop (𝓝 c) ∧
      Tendsto (fun φ => |φ| ^ 3 * pDiff Q phibar φ) atBot (𝓝 c) :=
  ⟨delay_time_tails_localized γ hγ, fun Q phibar hQ hphibar =>
    ⟨Q * phibar ^ 2 / 2, by positivity, pDiff_tails Q phibar hQ hphibar⟩⟩
