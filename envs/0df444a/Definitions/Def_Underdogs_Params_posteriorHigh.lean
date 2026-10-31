-- Prove2me | Definitions.Def_Underdogs_Params_posteriorHigh
-- name    : Underdogs_Params_posteriorHigh
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:20.836426+00:00
-- url     : https://prove2.me/theorems/b3d28603-729a-4d39-bc1b-d6a1e6550a1b
-- title:
--   Posterior probability of high quality $P(H\mid o_1,o_2)$
-- statement:
--   The posterior probability that an agent is of high quality given its two outcomes, in order:
--   $$
--   P(H\mid o_1,o_2)=\mu\bigl(\{q=H\}\,\big|\,\{(\text{first},\text{second})=(o_1,o_2)\}\bigr).
--   $$
--   In particular $P(H\mid F,S)$ conditions on failure first and success second, and $P(H\mid S,S)$ on two successes. This is the quantity the evaluator in the paper uses to judge how impressive a track record is.
--
--   **Formalization Note** The posterior is Mathlib's conditional measure `μ[|s]` of the joint law, converted to a real. It is not defined by the closed formulas of Appendix A, which are separate theorems. On a null conditioning event the value is $0$; the events $(F,S)$ and $(S,S)$ have positive probability in the standing domain.
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, pp.5–8 (PDF pp.6–9); Appendix A, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_Underdogs_Params_jointLaw

open MeasureTheory ProbabilityTheory

namespace Underdogs

/-- The posterior probability `P(H | o₁, o₂)` that an agent is of high quality given its
first-period outcome `o₁` and second-period outcome `o₂` (`true` = success): the conditional
probability, under the joint law of the two-period model, of the event "quality is `H`" given the
event "the outcomes are `(o₁, o₂)`, in this order". Thus `P(H|F,S)` is
`P.posteriorHigh false true` and `P(H|S,S)` is `P.posteriorHigh true true`.
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, pp.5–8 (PDF pp.6–9), and Appendix A, p.35 (PDF p.36).

**Formalization Note** This is Mathlib's conditional measure `μ[|s]` (`ProbabilityTheory.cond`)
evaluated on the event, converted to a real with `.toReal`; it is not the closed form of
Appendix A, which is a theorem. Under `Params.Standing` the events `(F, S)` and `(S, S)` used by
the theorems have positive probability. On a null conditioning event the value is `0`. -/
noncomputable def Params.posteriorHigh (P : Params) (o₁ o₂ : Bool) : ℝ :=
  (P.jointLaw[|{ω : Quality × Bool × Bool | ω.2 = (o₁, o₂)}]
    {ω : Quality × Bool × Bool | ω.1 = Quality.H}).toReal

end Underdogs


