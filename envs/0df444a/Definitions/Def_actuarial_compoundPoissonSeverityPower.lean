-- Prove2me | Definitions.Def_actuarial_compoundPoissonSeverityPower
-- name    : actuarial_compoundPoissonSeverityPower
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:24:33.983802+00:00
-- url     : https://prove2.me/theorems/ed1caafd-7592-4f43-be77-653dae109e0e
-- title:
--   Claim total for exactly a specified count of independent severities
-- statement:
--   With zero claims the aggregate loss is certainly zero. Adding one claim convolves the single-claim severity mass with the aggregate of the previous m claims, modelling the loss distribution for exactly m+1 independent and identically distributed severities.
--
--   **Mathematical statement**
--
--   $$
--   f^{*0}=\delta_0,\quad f^{*(m+1)}=f*f^{*m}
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonConvolution

namespace ActuarialValuation

noncomputable def compoundPoissonSeverityPower (f : ℕ → ℝ) :
    ℕ → ℕ → ℝ
  | 0 => fun s => if s = 0 then 1 else 0
  | m + 1 => fun s =>
      compoundPoissonConvolution f (compoundPoissonSeverityPower f m) s

end ActuarialValuation


