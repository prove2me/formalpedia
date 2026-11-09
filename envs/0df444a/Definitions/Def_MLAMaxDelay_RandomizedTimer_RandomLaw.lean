-- Prove2me | Definitions.Def_MLAMaxDelay_RandomizedTimer_RandomLaw
-- name    : MLAMaxDelay_RandomizedTimer_RandomLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:21.428988+00:00
-- url     : https://prove2.me/theorems/02cdeef1-3576-4f4b-beb3-11d648e2e398
-- title:
--   The continuous global seed distribution and extended expectation
-- statement:
--   The seed law on the real line is Lebesgue measure restricted to $[0,1]$, with density
--   $$f(x)=\frac{\exp(x)}{\exp(1)-1}.$$
--   Its proposed distribution function is zero below zero, $(\exp(x)-1)/(\exp(1)-1)$ on the unit interval, and one above one. Normalization and the CDF identity are conclusions in the goal statement. Expected execution cost is the nonnegative extended integral of the actual schedule cost under this one fixed law. The input lies outside the integral, and the same real seed is passed to every timer update.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 13, equation (17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Potential

namespace MLAMaxDelay.RandomizedTimer

open MeasureTheory
open scoped ENNReal

/-- Equation (17), p. 13: one global real seed with density exp(x)/(exp(1)-1)
on [0,1]. Normalization is a conclusion of the goal, not a model hypothesis. -/
noncomputable def seedLaw : Measure ℝ :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity
    (fun x => ENNReal.ofReal (Real.exp x / (Real.exp 1 - 1)))

noncomputable def seedCDF (x : ℝ) : ℝ :=
  if x < 0 then 0 else if 1 < x then 1 else (Real.exp x - 1) / (Real.exp 1 - 1)

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def expectedCost (T : WeightedTree V) (I : Input V) : ℝ≥0∞ :=
  ∫⁻ θ, cost T I (optTimer T I θ) ∂seedLaw

end MLAMaxDelay.RandomizedTimer


