-- Prove2me | solution 1 for Arxivcond_mat_0004049.mean_delay_time_localized_vs_diffusive
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T13:58:41.82434+00:00
-- url     : https://prove2.me/submissions/75df1d1e-fc38-4ab4-83cf-a26ad9d56809

import Theorems.Thm_Arxivcond_mat_0004049_mean_spectral_moment_divergent
import Theorems.Thm_Arxivcond_mat_0004049_mean_abs_delay_divergent
import Theorems.Thm_Arxivcond_mat_0004049_pDiff_mean

open MeasureTheory Filter Topology
open Arxivcond_mat_0004049

theorem solution :
    (∀ N : ℕ, 1 ≤ N → ∀ γ : ℝ, 0 < γ →
      ∫⁻ ω, ENNReal.ofReal |delayNe ω| ∂(localizedModel N γ) = ⊤ ∧
      ∫⁻ ω, ENNReal.ofReal (specMoment 1 ω) ∂(localizedModel N γ) = ⊤) ∧
    ∀ Q phibar : ℝ, 0 < Q → 0 < phibar →
      Integrable (fun φ : ℝ => φ * pDiff Q phibar φ) ∧
      ∫ φ : ℝ, φ * pDiff Q phibar φ = phibar :=
  ⟨fun N hN γ hγ => ⟨mean_abs_delay_divergent N hN γ hγ, mean_spectral_moment_divergent N hN γ hγ⟩,
    fun Q phibar hQ hphibar => pDiff_mean Q phibar hQ hphibar⟩
