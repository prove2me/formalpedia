-- Prove2me | solution 1 for Arxiv2003_13288.qca_effective_propagation_constant
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:41:52.799219+00:00
-- url     : https://prove2.me/submissions/c52d6996-8703-463f-99d5-9de7d1f30cb2

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

open Arxiv2003_13288 in
theorem solution (n0 k : ℝ) (hn0 : 0 < n0) (hk : 0 < k) (t0 : ℂ)
    (ht0 : t0 ≠ 0) (h2 : ℝ → ℝ) (K : ℂ)
    (hK : K ^ 2 = (k : ℂ) ^ 2 * effPermittivity k (qcaSelfEnergy n0 k t0 h2)) :
    K ^ 2 = (k : ℂ) ^ 2 - 1 / (1 / (n0 * t0) + 1 / (3 * (k : ℂ) ^ 2) + 2 * corrIntegral k h2 / 3) := by
  have hk2 : ((k : ℂ)) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hk.ne')
  have hn : (n0 : ℂ) * t0 ≠ 0 := mul_ne_zero (by exact_mod_cast hn0.ne') ht0
  rw [hK, effPermittivity, mul_sub, mul_one, mul_div_cancel₀ _ hk2, qcaSelfEnergy]
  congr 1
  have : 1 / ((n0 : ℂ) * t0) + 1 / (3 * (k : ℂ) ^ 2) + 2 * corrIntegral k h2 / 3 =
      (1 + n0 * t0 / (3 * (k : ℂ) ^ 2) + 2 * n0 * t0 * corrIntegral k h2 / 3) / (n0 * t0) := by
    have hn0c : (n0 : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    rw [eq_div_iff hn]
    field_simp
  rw [this, one_div_div]
