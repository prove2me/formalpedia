-- Prove2me | Definitions.Def_FoundationsRL_DECLower_gap
-- name    : FoundationsRL_DECLower_gap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:08:43.025452+00:00
-- url     : https://prove2.me/theorems/e3bfb195-44f2-41db-97de-d8ef154b00b4
-- title:
--   Suboptimality gap $g^M(\pi)=f^M(\pi_M)-f^M(\pi)$
-- statement:
--   For a kernel $M$ and a decision $\pi$, the **suboptimality gap** is
--
--   $$
--   g^M(\pi)=f^M(\pi_M)-f^M(\pi).
--   $$
--
--   It is the per-round instantaneous regret in (6.3) and the objective inside the constrained Decision-Estimation Coefficient. For a model it lies in $[0,1]$.
--
--   **Formalization Note** $f^M(\pi_M)$ is the supremum of the mean reward (see the optimal mean reward definition).
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 28, p. 108 (g^M); (6.3), p. 94

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_meanReward
import Definitions.Def_FoundationsRL_DECLower_optValue

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.DECLower

/-- **Suboptimality gap** `g^M(π) = f^M(π_M) − f^M(π)`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, proof of Proposition 28, p. 108 ("let us abbreviate g^M(π) = f^M(π_M) − f^M(π)");
the same quantity is the integrand of the regret (6.3), p. 94, and of the constrained DEC, p. 104.

**Formalization Note.** `f^M(π_M)` is `optValue M` (a supremum; see there). For a model the gap
lies in `[0, 1]`. -/
noncomputable def gap {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (M : Kernel D (ℝ × O)) (d : D) : ℝ :=
  optValue M - meanReward M d

end FoundationsRL.DECLower


