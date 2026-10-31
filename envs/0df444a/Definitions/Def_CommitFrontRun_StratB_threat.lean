-- Prove2me | Definitions.Def_CommitFrontRun_StratB_threat
-- name    : CommitFrontRun_StratB_threat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:12.126011+00:00
-- url     : https://prove2.me/theorems/182c5a0c-ffe1-4961-811d-4afbac453d32
-- title:
--   Front-running threat $\sum_\sigma \mu(\sigma)\,\mathrm{fire}(\sigma,m)$ at a revealed message
-- statement:
--   For a strategy $(\mu,\mathrm{fire})$ of $B$ and a revealed message $m\in\Sigma$,
--   $$
--   \mathrm{threat}(m)=\sum_{\sigma\in\Sigma}\mu(\mathrm{guess}\ \sigma)\,\mathrm{fire}(\sigma,m)
--   $$
--   is the probability that $B$, having committed according to $\mu$, front-runs $A$'s reveal message $m$ with a fast message.
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3.1, p.15

import Mathlib
import Definitions.Def_CommitFrontRun_StratB

namespace CommitFrontRun

variable {Msg : Type} [Fintype Msg]

/-- **Front-running threat at a revealed message.**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3.1, p.15.

`B.threat m = ∑_σ μ(guess σ) · fire(σ, m)`: the probability that B, having committed under his
strategy, front-runs A's reveal message m with a fast message. -/
def StratB.threat (B : StratB Msg) (m : Msg) : ℝ :=
  ∑ σ, B.μ (BCommit.guess σ) * B.fire σ m

end CommitFrontRun


