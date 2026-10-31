-- Prove2me | Definitions.Def_Underdogs_Params_jointLaw
-- name    : Underdogs_Params_jointLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:35.445982+00:00
-- url     : https://prove2.me/theorems/381cadd4-3cbc-4c12-b879-1e28b8d8e50c
-- title:
--   Joint law of the two-period model
-- statement:
--   The joint law $\mu$ of (quality, first outcome, second outcome) on the eight-point sample space: the measure that puts mass $\Pr(q,o_1,o_2)$ (see `Params.mass`) on each point. Under the standing domain it is a probability measure, and the prior probability of high quality is $1/2$.
--
--   **Formalization Note** $\mu$ is the finite sum $\sum_\omega \mathrm{ofReal}(\Pr(\omega))\,\delta_\omega$ of Dirac measures. Outside the standing domain the weights need not be probabilities, and no theorem uses the law there.
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, p.5 (PDF p.6); Appendix A, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_Underdogs_Params_mass

open MeasureTheory

namespace Underdogs

/-- The joint law of (quality, first-period outcome, second-period outcome) in the two-period
model, as a measure on the finite sample space `Quality × Bool × Bool`: the point mass at each
outcome `ω` weighted by `Params.mass P ω`.
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, p.5 (PDF p.6); Appendix A, p.35 (PDF p.36).

**Formalization Note** The law is a finite sum of Dirac measures with weights
`ENNReal.ofReal (P.mass ω)`. Under `Params.Standing` all weights are nonnegative and sum to 1,
so it is a probability measure; outside that domain it is junk and no theorem uses it there. -/
noncomputable def Params.jointLaw (P : Params) : Measure (Quality × Bool × Bool) :=
  ∑ ω, ENNReal.ofReal (P.mass ω) • Measure.dirac ω

end Underdogs


