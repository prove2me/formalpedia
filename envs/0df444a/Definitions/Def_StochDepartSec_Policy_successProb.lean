-- Prove2me | Definitions.Def_StochDepartSec_Policy_successProb
-- name    : StochDepartSec_Policy_successProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:48.20899+00:00
-- url     : https://prove2.me/theorems/001886b4-3543-4578-9810-1473ad5b4aed
-- title:
--   Success probability $\Pr[\mathrm{success}(\mathrm{pol})]$
-- statement:
--   For an arrival distribution $\mathcal A$ and a waiting time distribution $\mathcal L$, the success probability of a policy is $\mathbb P_{n,\mathcal A,\mathcal L}[\mathrm{success}(\mathrm{pol})]$, a number in $[0,1]$.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, §2, p.5

import Mathlib
import Definitions.Def_StochDepartSec_Outcome
import Definitions.Def_StochDepartSec_outcomeLaw
import Definitions.Def_StochDepartSec_Policy
import Definitions.Def_StochDepartSec_Policy_success
open MeasureTheory

namespace StochDepartSec

/-- `Pr[success(pol)]` for the instance with arrival distribution `A` and waiting time
distribution `L`.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §2, p.5: "The goal is to design an algorithm that maximizes the probability of selecting the
best candidate."

**Formalization Note** The probability is converted to a real number with `toReal`; it lies in
`[0, 1]`, so nothing is lost. -/
noncomputable def Policy.successProb {n : ℕ} (pol : Policy n) (A L : Measure ℝ)
    [IsProbabilityMeasure A] [IsProbabilityMeasure L] : ℝ :=
  (outcomeLaw n A L {ω | pol.success ω}).toReal

end StochDepartSec


