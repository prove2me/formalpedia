-- Prove2me | Definitions.Def_Underdogs_Params_Standing
-- name    : Underdogs_Params_Standing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:43.09308+00:00
-- url     : https://prove2.me/theorems/2ec8be28-04c9-45c1-bbb9-a3cd64b27ab6
-- title:
--   Standing domain of the six success probabilities
-- statement:
--   The standing domain of the two-period model: the first-period probabilities satisfy
--   $$
--   0<p_h<1,\qquad 0<p_l<1,
--   $$
--   and the second-period probabilities satisfy
--   $$
--   0<p_{h,S},\,p_{l,S},\,p_{h,F},\,p_{l,F}\le 1 .
--   $$
--
--   All six are probabilities. The paper's formulas divide by $p_h$, $p_l$, $1-p_h$, $1-p_l$ and by the four second-period probabilities, but never by $1-p_{q,S}$ or $1-p_{q,F}$, so this domain excludes exactly the values at which a formula of the paper is undefined.
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, p.5 (PDF p.6); eq. (4), p.8 (PDF p.9); Appendix A, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_Underdogs_Params

namespace Underdogs

/-- Standing domain of the two-period model: the first-period success probabilities `p_h`, `p_l`
lie in the open interval (0,1), and the four second-period success probabilities
`p_{h,S}`, `p_{l,S}`, `p_{h,F}`, `p_{l,F}` lie in (0,1].
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, p.5 (PDF p.6); Appendix A, p.35 (PDF p.36).

**Formalization Note** The paper calls the six numbers probabilities, so each lies in [0,1]. Its
formulas divide by `p_h`, `p_l`, `1 − p_h`, `1 − p_l` (eq. (4); Appendix A) and by
`p_{h,S}`, `p_{l,S}`, `p_{h,F}`, `p_{l,F}` (eq. (4); Appendix A), but never by `1 − p_{q,S}` or
`1 − p_{q,F}`. The domain excludes exactly the values at which one of these denominators
vanishes. -/
def Params.Standing (P : Params) : Prop :=
  P.ph ∈ Set.Ioo (0 : ℝ) 1 ∧ P.pl ∈ Set.Ioo (0 : ℝ) 1 ∧
  P.phS ∈ Set.Ioc (0 : ℝ) 1 ∧ P.plS ∈ Set.Ioc (0 : ℝ) 1 ∧
  P.phF ∈ Set.Ioc (0 : ℝ) 1 ∧ P.plF ∈ Set.Ioc (0 : ℝ) 1

end Underdogs


