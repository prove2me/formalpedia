-- Prove2me | solution 1 for Arxiv2003_13288.static_scatterer_criterion
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:33:30.141092+00:00
-- url     : https://prove2.me/submissions/8db34865-2bc7-453a-b937-444e63399878

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

open Arxiv2003_13288 in
theorem solution (k vp ls c0 : ℝ) (hk : 0 < k) (hvp : 0 ≤ vp) (hls : 0 < ls)
    (hc0 : 0 < c0) :
    k * vp * (ls / c0) = vp / c0 * (k * ls) ∧
    (∀ ε : ℝ, 0 < ε → (k * vp * (ls / c0) ≤ ε ↔ vp / c0 ≤ ε / (k * ls))) ∧
    (1 < k * ls → ∀ ε : ℝ, 0 < ε → ε / (k * ls) < ε) ∧
    (∀ τ τ' : ℝ, 0 < τ → τ < τ' → ∀ ε : ℝ, 0 < ε → ε / (k * τ') < ε / (k * τ)) := by
  have hkl : 0 < k * ls := mul_pos hk hls
  have e : k * vp * (ls / c0) = vp / c0 * (k * ls) := by field_simp
  refine ⟨e, ?_, ?_, ?_⟩
  · intro ε hε
    rw [e, le_div_iff₀ hkl]
  · intro h ε hε
    rw [div_lt_iff₀ hkl]; nlinarith
  · intro τ τ' hτ hττ ε hε
    apply div_lt_div_of_pos_left hε (mul_pos hk hτ)
    exact mul_lt_mul_of_pos_left hττ hk
