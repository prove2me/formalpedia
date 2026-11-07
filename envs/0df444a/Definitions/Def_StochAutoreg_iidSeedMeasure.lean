-- Prove2me | Definitions.Def_StochAutoreg_iidSeedMeasure
-- name    : StochAutoreg_iidSeedMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:48.008206+00:00
-- url     : https://prove2.me/theorems/2f34b33d-1892-463e-958f-926f5f3a3b1b
-- title:
--   Joint law of $n$ i.i.d. samples and a seed
-- statement:
--   The product of $n$ independent copies of a sample law $\mu$ with the uniform law on the seed space $[0,1]$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.3

import Mathlib

namespace StochAutoreg

/-- The joint law of `n` i.i.d. samples from `μ` and an independent uniform seed in `[0,1]`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.3. -/
noncomputable def iidSeedMeasure {S : Type} [MeasurableSpace S] (μ : PMF S) (n : ℕ) :
    MeasureTheory.Measure ((Fin n → S) × unitInterval) :=
  (MeasureTheory.Measure.pi fun _ : Fin n => μ.toMeasure).prod MeasureTheory.volume

end StochAutoreg


