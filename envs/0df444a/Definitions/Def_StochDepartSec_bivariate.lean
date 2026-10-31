-- Prove2me | Definitions.Def_StochDepartSec_bivariate
-- name    : StochDepartSec_bivariate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:55.159661+00:00
-- url     : https://prove2.me/theorems/cbe5368b-19bb-48cc-baaf-6bebc6d697d8
-- title:
--   Bivariate policy of $\Theta_n(t,K_t)$
-- statement:
--   Let $\Theta:\mathbb R\times\mathbb N\to\{0,1\}$. The **bivariate policy** of $\Theta$ acts as follows: whenever a candidate $x$ departs at time $t$, accept $x$ if $x$ is the best-so-far at $t$ and $\Theta(t,K_t)=1$; otherwise reject.
--
--   The decision depends on the history only through $t$, $K_t$ and the identity of the best-so-far candidate.
--
--   **Formalization Note** $\Theta$ is a function on $\mathbb R\times\mathbb N$ with values in `Bool` (`true` = 1); the paper's domain is $[0,1]\times[n]$, and other values are never read on almost every outcome.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, Definition 3, p.6

import Mathlib
import Definitions.Def_StochDepartSec_Outcome
import Definitions.Def_StochDepartSec_dep
import Definitions.Def_StochDepartSec_numArrived
import Definitions.Def_StochDepartSec_BestSoFar
import Definitions.Def_StochDepartSec_Policy
open Classical

namespace StochDepartSec

/-- The bivariate policy of `Θ`: when a candidate `x` departs at time `t`, accept `x` iff `x` is
the best-so-far at `t` and `Θ(t, K_t) = 1`; otherwise reject.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, Definition 3, p.6: "there exists a function Θ_n(t, K_t), Θ_n : [0,1] × [n] → {0,1}, such that
whenever a candidate x departs at time t and K_t candidates have arrived prior to t, accept if x is
the best candidate seen so far and Θ_n(t, K_t) = 1, otherwise reject."

**Formalization Note** `Θ` is a function `ℝ → ℕ → Bool` (`true` = 1); its values off
`[0,1] × [n]` are never read on almost every outcome. At most one candidate is the best-so-far at
`t`, so the chosen candidate is determined. -/
noncomputable def bivariate {n : ℕ} (Θ : ℝ → ℕ → Bool) : Policy n where
  decide ω t :=
    if h : ∃ i, dep ω i = t ∧ BestSoFar ω t i ∧ Θ t (numArrived ω t) = true then
      some (Classical.choose h)
    else none

end StochDepartSec


