-- Prove2me | solution 1 for Arxiv1801_00461.apparent_parameters_special_cases
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:15:49.519809+00:00
-- url     : https://prove2.me/submissions/61d725c8-657a-4f39-9c57-ea1d76958563

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology
open Arxiv1801_00461

theorem solution (sigInf : ℝ → ℂ) (dsig : ℝ → ℝ) (eps0 : ℝ)
    (chi : ℝ → ℝ) :
    appCond sigInf dsig eps0 chi 0 = (condFreq sigInf dsig 0).re ∧
    (∀ ω : ℝ, (permittivity eps0 chi ω).im = 0 → appCond sigInf dsig eps0 chi ω = (condFreq sigInf dsig ω).re) ∧
    (∀ ω : ℝ, ω ≠ 0 → (condFreq sigInf dsig ω).im = 0 → (permittivity eps0 chi ω).im = 0 →
      appCond sigInf dsig eps0 chi ω = (condFreq sigInf dsig ω).re ∧ appPerm sigInf dsig eps0 chi ω = (permittivity eps0 chi ω).re) := by
  constructor
  · simp [appCond,admittance]
  · constructor
    · intro ω h; simp [appCond,admittance,Complex.mul_re,Complex.mul_im,h]
    · intro ω hω hcond hperm; constructor
      · simp [appCond,admittance,Complex.mul_re,Complex.mul_im,hperm]
      · simp [appPerm,admittance,Complex.mul_re,Complex.mul_im,hcond,hω]
