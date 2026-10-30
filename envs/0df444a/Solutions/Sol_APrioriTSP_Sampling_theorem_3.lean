-- Prove2me | solution 1 for APrioriTSP.Sampling.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:11:23.584977+00:00
-- url     : https://prove2.me/submissions/378ba1a1-5885-4c0c-b50e-65f07da2022e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP
import Theorems.Thm_APrioriTSP_Sampling_corollary_16
import Theorems.Thm_APrioriTSP_Sampling_dual_certificate_theorem_3

open APrioriTSP.Sampling

theorem solution : ∃ ρ : ℝ, ρ < 3.1 ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V),
      IsDepotInstance c p d →
      samplingCost 1.5 (powerSampling 0.663) c p ≤ ρ * aPrioriOpt c p := by
  obtain ⟨β, N, x, y, v, w, hβ, hN, hfeas, hy, hρ⟩ := dual_certificate_theorem_3
  exact ⟨(0.663 : ℝ) ^ 2 / y, hρ,
    corollary_16 1.5 0.663 β N hN hβ (by norm_num) (by norm_num) (by norm_num) x y v w hfeas hy⟩
