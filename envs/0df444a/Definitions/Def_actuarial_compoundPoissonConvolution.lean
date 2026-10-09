-- Prove2me | Definitions.Def_actuarial_compoundPoissonConvolution
-- name    : actuarial_compoundPoissonConvolution
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:24:03.372992+00:00
-- url     : https://prove2.me/theorems/b3b79938-c06a-4816-b6ca-389b05dd2d92
-- title:
--   Finite discrete severity convolution
-- statement:
--   A convolution coefficient at aggregate loss s sums products over every split between one new claim amount j and a previous total s-j. All amounts are nonnegative integers, so only finitely many splits need consideration for any requested loss size.
--
--   **Mathematical statement**
--
--   $$
--   (f*g)(s)=\sum_{j=0}^{s}f(j)g(s-j)
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib

namespace ActuarialValuation

noncomputable def compoundPoissonConvolution (f g : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), f j * g (s - j)

end ActuarialValuation


