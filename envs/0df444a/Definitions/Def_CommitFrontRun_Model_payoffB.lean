-- Prove2me | Definitions.Def_CommitFrontRun_Model_payoffB
-- name    : CommitFrontRun_Model_payoffB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:19.739926+00:00
-- url     : https://prove2.me/theorems/e25b84ba-85c5-4ec2-8420-9ea83485d898
-- title:
--   $B$'s ex-ante expected payoff
-- statement:
--   $B$'s ex-ante expected payoff under the strategy profile $(A,B)$ is
--   $$
--   u_B(A,B)=\sum_{s\in S}p(s)\,\mathrm{commit}(s)\Big(-c\,(1-\mu(\mathrm{none}))+\beta\,\mathrm{reveal}(s)\sum_{\sigma\in\Sigma}\mu(\mathrm{guess}\ \sigma)\,\mathrm{fire}(\sigma,\sigma_A(s))\,\big(q\,\tilde P_B(\sigma,\sigma_A(s),s)-f\big)\Big).
--   $$
--   $B$ moves only after $A$ commits. Any commit message (clone or guess) costs $c$; a clone never yields a prize. When $A$ reveals $\sigma_A(s)$, firing the committed guess $\sigma$ costs $f$ and wins $\tilde P_B(\sigma,\sigma_A(s),s)$ with probability $q$, one block later. This matches the paper's "$B$'s expected payoff from front-running is $q\cdot\tilde P_B(\sigma_B,\sigma^{**}_A(s),s)-f$" and the value $\beta\pi-c$ of a committed guess (p.15).
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3, pp.13–14; §3.1, p.15

import Mathlib
import Definitions.Def_CommitFrontRun_Model_PA
import Definitions.Def_CommitFrontRun_StratA
import Definitions.Def_CommitFrontRun_StratB

namespace CommitFrontRun

variable {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype Msg] [DecidableEq Msg] [Nonempty Msg]

/-- **B's ex-ante expected payoff** under the profile (A, B).
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3, pp.13–14; §3.1, p.15.

`∑_s p(s) · commit(s) · (−c · (1 − μ(none)) + β · reveal(s) · ∑_σ μ(guess σ) · fire(σ, σ_A(s)) ·
(q · P̃_B(σ, σ_A(s), s) − f))`.

B moves only after A commits. He pays c for any commit message (a clone or a guess); a clone
never yields a prize. If A reveals σ_A(s), B may fire his committed guess σ as a fast message
at cost f (discounted by β), winning P̃_B(σ, σ_A(s), s) with probability q (p.15: "B's expected
payoff from front-running is q · P̃_B(σ_B, σ**_A(s), s) − f"). If A does not reveal, B gets
nothing further.

**Formalization Note** Payoffs are ex ante, averaged over the prior. -/
def Model.payoffB (M : Model S Msg) (A : StratA S) (B : StratB Msg) : ℝ :=
  ∑ s, M.p s * A.commit s *
    (-M.c * (1 - B.μ BCommit.none) +
      M.β * A.reveal s * ∑ σ, B.μ (BCommit.guess σ) * B.fire σ (M.σA s) *
        (M.q * M.PtB σ (M.σA s) s - M.f))

end CommitFrontRun


