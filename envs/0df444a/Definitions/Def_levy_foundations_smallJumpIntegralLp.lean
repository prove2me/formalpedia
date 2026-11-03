-- Prove2me | Definitions.Def_levy_foundations_smallJumpIntegralLp
-- name    : levy_foundations_smallJumpIntegralLp
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T12:34:19.853294+00:00
-- url     : https://prove2.me/theorems/3f5b2111-983e-46e3-9aa6-229ccf523bad
-- title:
--   L² compensated small-jump integral at a fixed time
-- statement:
--   Integrate the small-jump band function against the centred time-space Poisson measure via the L² compensated-integral extension. The output is an equivalence class in L² of the probability measure.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Independently authored Prove2Me draft pending exact-revision remote compiler verification. TimeSpacePoisson.lean lines 249–254, adapted to an explicit isometric extension argument.

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Definitions.Def_levy_foundations_isCompensatedPoissonL2Extension
import Definitions.Def_levy_foundations_isLevyMeasure

open MeasureTheory
namespace LevyFoundations
noncomputable def smallJumpIntegralLp
    {Ω : Type} [MeasurableSpace Ω] (ν : Measure ℝ)
    [SigmaFinite ν] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (I : Lp ℝ 2 ((volume : Measure ℝ).prod ν) → Lp ℝ 2 μ)
    (hν : isLevyMeasure ν) (t : ℝ) : Lp ℝ 2 μ :=
  by
    classical
    let f : ℝ × ℝ → ℝ :=
      (Set.Ioc 0 t ×ˢ Set.Ioo (-1) 1).indicator (fun p => p.2)
    exact I (if h : MemLp f 2 ((volume : Measure ℝ).prod ν) then h.toLp f else 0)
end LevyFoundations


