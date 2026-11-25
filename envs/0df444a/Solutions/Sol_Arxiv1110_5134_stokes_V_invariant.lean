-- Prove2me | solution 1 for Arxiv1110_5134.stokes_V_invariant
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:17:36.882364+00:00
-- url     : https://prove2.me/submissions/51ef0b16-d1af-4fe4-affc-16b672519421

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

theorem solution (n I χ ψ : ℝ → ℝ) (s : ℝ) (hn : 0 < n s)
    (hI : HasDerivAt (fun t => I t / n t ^ 2) 0 s) (hχ : HasDerivAt χ 0 s) :
    HasDerivAt (fun t => stokesVec (I t) (χ t) (ψ t) 3 / n t ^ 2) 0 s := by
  have hsin : HasDerivAt (fun t => Real.sin (2 * χ t)) (Real.cos (2 * χ s) * (2 * 0)) s :=
    (hχ.const_mul 2).sin
  have hmul := hI.mul hsin
  have hfn : (fun t => stokesVec (I t) (χ t) (ψ t) 3 / n t ^ 2) =
      ((fun t => I t / n t ^ 2) * fun t => Real.sin (2 * χ t)) := by
    ext t
    simp [stokesVec, Pi.mul_apply]
    ring
  have hval : (0 : ℝ) =
      0 * Real.sin (2 * χ s) + I s / n s ^ 2 * (Real.cos (2 * χ s) * (2 * 0)) := by
    ring
  rw [hfn, hval]
  exact hmul
