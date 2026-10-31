-- Prove2me | Definitions.Def_Underdogs_Params
-- name    : Underdogs_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:49:56.186069+00:00
-- url     : https://prove2.me/theorems/10390570-f64c-46a2-b0e2-a35529caef75
-- title:
--   Six success probabilities of the two-period model
-- statement:
--   The two-period model is described by six numbers:
--
--   1. $p_h$, $p_l$: the probability that a high-, respectively low-quality agent succeeds in the first period;
--   2. $p_{h,S}$, $p_{l,S}$: the probability of success in the second period after a first-period success;
--   3. $p_{h,F}$, $p_{l,F}$: the probability of success in the second period after a first-period failure.
--
--   The dependence of the second-period probability on the first outcome models resources that a success adds and a failure depletes.
--
--   **Formalization Note** The structure holds six reals; their range is the separate predicate `Params.Standing`. No ordering such as $p_l<p_h$ is imposed.
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, p.5 (PDF p.6); Appendix A, p.35 (PDF p.36)

import Mathlib

namespace Underdogs

/-- The six success probabilities of the two-period model.
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, p.5 (PDF p.6), and Appendix A, p.35 (PDF p.36).

* `ph`, `pl`: first-period success probability of a high-, low-quality agent;
* `phS`, `plS`: second-period success probability after an initial success;
* `phF`, `plF`: second-period success probability after an initial failure.

**Formalization Note** The fields are bare reals; their standing domain is the separate
predicate `Params.Standing`, which every theorem assumes. No ordering such as `pl < ph` is
imposed, since the paper does not impose one on this model. -/
structure Params where
  ph : ℝ
  pl : ℝ
  phS : ℝ
  plS : ℝ
  phF : ℝ
  plF : ℝ

end Underdogs


