-- Prove2me | Definitions.Def_actuarial_compoundPoissonAggregatePMF
-- name    : actuarial_compoundPoissonAggregatePMF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:25:21.479821+00:00
-- url     : https://prove2.me/theorems/00abb4ed-11d6-4731-9eb1-0b5861154f67
-- title:
--   Compound Poisson aggregate mass for strictly positive severities
-- statement:
--   For integer aggregate loss s, the compound model mixes the conditional sum-of-m severity probabilities against Poisson claim-count weights. Its finite truncation to m≤s is exact only when a positive claim has severity at least one, formally f(0)=0. This condition is required in the key theorems, not silently assumed by the definition.
--
--   **Mathematical statement**
--
--   $$
--   g_s=\sum_{m=0}^{s}e^{-\lambda}\frac{\lambda^m}{m!}f^{*m}(s)
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonCountWeight
import Definitions.Def_actuarial_compoundPoissonSeverityPower

namespace ActuarialValuation

noncomputable def compoundPoissonAggregatePMF (rate : ℝ)
  (f : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (s + 1),
    compoundPoissonCountWeight rate m *
      compoundPoissonSeverityPower f m s

end ActuarialValuation


