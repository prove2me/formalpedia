-- Prove2me | solution 1 for Arxivcond_mat_0004049.rayleigh_law_localized
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T15:19:32.519877+00:00
-- url     : https://prove2.me/submissions/2895f040-ee68-48fb-b4db-f420dcb780e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Arxivcond_mat_0004049_rayleigh_law_ne
import Theorems.Thm_Arxivcond_mat_0004049_rayleigh_law_eq_large_N

open MeasureTheory Filter Topology
open Arxivcond_mat_0004049

theorem solution (γ : ℝ) (hγ : 0 < γ) :
    (∀ N : ℕ, 1 ≤ N → (localizedModel N γ).map intensityNe =
      (volume : Measure ℝ).withDensity
        (fun I => ENNReal.ofReal (if 0 < I then (N : ℝ) * Real.exp (-(N : ℝ) * I) else 0))) ∧
    LawTendsto γ (fun N (ω : Sample N) => (N : ℝ) * intensityEq ω)
      ((volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (if 0 < x then Real.exp (-x / 2) / 2 else 0))) :=
  ⟨rayleigh_law_ne γ hγ, rayleigh_law_eq_large_N γ hγ⟩
