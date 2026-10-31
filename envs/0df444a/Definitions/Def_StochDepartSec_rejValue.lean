-- Prove2me | Definitions.Def_StochDepartSec_rejValue
-- name    : StochDepartSec_rejValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:59:01.5843+00:00
-- url     : https://prove2.me/theorems/b473c696-3cb1-49e4-b981-c64b0c1a6961
-- title:
--   Value of rejecting, $\Pr[\mathrm{success}(\mathrm{rej}_t)\mid K_t=k,\mathcal E_t]$
-- statement:
--   For a time $t$ and a number $k$ of arrivals, the **value of rejecting** is
--
--   $$
--   V(t,k)=\sup\Bigl\{\Pr\bigl[\mathrm{success}(q)\bigm| K_t=k\bigr] : q\text{ admissible, never accepts a candidate arrived by }t\Bigr\}.
--   $$
--
--   It is the paper's $\Pr[\mathrm{success}(\mathrm{rej}_t)\mid K_t=k,\mathcal E_t]$, where $\mathrm{rej}_t$ rejects every candidate departing up to and including $t$ and then continues optimally, and $\mathcal E_t$ is the event that at time $t$ a candidate leaves and is best so far. On $\mathcal E_t$ the other arrived candidates are worse than the departing one, so $\mathrm{rej}_t$ and the best policy that rejects all candidates arrived by $t$ have the same success probability (p.11), and given $K_t=k$ this success is independent of $\mathcal E_t$.
--
--   **Formalization Note** $\mathcal E_t$ has probability $0$ when $\mathcal A$ or $\mathcal L$ is continuous, so the value conditions on $K_t=k$ only. When $\Pr[K_t=k]=0$ the conditional measure is the zero measure and $V(t,k)=0$; this happens only when $\mathcal A([0,t])\in\{0,1\}$ and $k$ is not $0$ resp. $n$.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, Lemma 10, p.8; §4, p.11

import Mathlib
import Definitions.Def_StochDepartSec_outcomeLaw
import Definitions.Def_StochDepartSec_numArrived
import Definitions.Def_StochDepartSec_Policy
import Definitions.Def_StochDepartSec_Policy_Admissible
import Definitions.Def_StochDepartSec_Policy_success
import Definitions.Def_StochDepartSec_Policy_NeverAcceptsBy
open MeasureTheory ProbabilityTheory

namespace StochDepartSec

/-- The value of rejecting at time `t` with `k` arrivals: the largest conditional success
probability, given `K_t = k`, of an admissible policy that accepts no candidate arrived by `t`.
This is the paper's `Pr[success(rej_t) | K_t = k, E_t]`.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §3.2, p.8: "Let E_t be the event that at time t a candidate leaves and is best so far";
Lemma 10, p.8; §4, p.11: "Note that pol_t and rej_t are different, but conditioned on E_t they
have the same probability of success, i.e., Pr[success(pol_t) | E_t] = Pr[success(rej_t) | E_t].
This is because if E_t occurs rej_t does not accept any candidate that arrived before t either."

**Formalization Note** `E_t` has probability 0 whenever `A` or `L` is continuous, so the paper's
conditioning on it is not a Lean conditional measure. Here the value is the supremum over the class
of `pol_t` (p.11) of the success probability conditioned on `K_t = k` only: after a rejection on
`E_t` no other arrived candidate can be the best overall, and given `K_t = k` the event `E_t` is
independent of the success of `pol_t` (the paper uses this on p.13). When `P(K_t = k) = 0` the
conditional measure `P[|K_t = k]` is the zero measure and the value is `0`; this happens only when
`A[0,t] ∈ {0,1}` and `k` is not `0` resp. `n`. The supremum is over a nonempty set (the reject-all
policy) of numbers in `[0, 1]`. -/
noncomputable def rejValue (n : ℕ) (A L : Measure ℝ) [IsProbabilityMeasure A]
    [IsProbabilityMeasure L] (t : ℝ) (k : ℕ) : ℝ :=
  ⨆ q : {q : Policy n // q.Admissible ∧ q.NeverAcceptsBy t},
    ((outcomeLaw n A L)[|{ω | numArrived ω t = k}] {ω | q.1.success ω}).toReal

end StochDepartSec


