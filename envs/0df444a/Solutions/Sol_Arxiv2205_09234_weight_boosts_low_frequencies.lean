-- Prove2me | solution 1 for Arxiv2205_09234.weight_boosts_low_frequencies
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:39:45.053006+00:00
-- url     : https://prove2.me/submissions/7acdc3db-3170-4bf7-8a65-f65cff2e0e09

import Mathlib
import Definitions.Def_Arxiv2205_09234_Basic

set_option autoImplicit false

open Arxiv2205_09234 in
theorem solution (N : ℕ) (hN : 0 < N) (dt α : ℝ) (hdt : 0 < dt)
    (w : Fin N → ℝ) (hw : IsFreqWeight N dt α w) (k l : Fin N)
    (hk : 0 < |sampleFreq N dt k|) (hkl : |sampleFreq N dt k| < |sampleFreq N dt l|) :
    w l < w k ↔ α < 0 := by
  have hl : 0 < |sampleFreq N dt l| := hk.trans hkl
  rw [hw.2 k (Or.inl (abs_pos.1 hk)), hw.2 l (Or.inl (abs_pos.1 hl))]
  constructor
  · intro h
    by_contra ha
    push Not at ha
    have := Real.rpow_le_rpow hk.le hkl.le ha
    linarith
  · intro ha
    exact Real.rpow_lt_rpow_of_neg hk hkl ha
