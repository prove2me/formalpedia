-- Prove2me | Definitions.Def_CommitteeVoting_ExpConv_VoteProb
-- name    : CommitteeVoting_ExpConv_VoteProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:41.265634+00:00
-- url     : https://prove2.me/theorems/f6b708ab-5124-4ca0-bafa-2626580ac92e
-- title:
--   Theorem 3, p. 22 — the vote probability p_{ij} that voter i approves producer j
-- statement:
--   Let $(\Omega,\mathcal F,\Pr)$ be a probability space and let the ballots be random: for each voter $i$, $\mathcal C_{v_i}(\omega)\subseteq\mathcal C$ is the random set of candidates voter $i$ approves. The **vote probability** of voter $i$ for producer $j$ is
--   $$p_{ij}=\Pr\bigl[\,j\in\mathcal C_{v_i}\,\bigr].$$
--
--   These are the parameters in terms of which Theorem 3 states its gap hypothesis and in terms of which the vote count of each producer is Poisson binomial (Theorem 1).
--
--   **Formalization Note** A random ballot is a map `Ω → (Fin m → Bool)`; the vote probability is the real-valued measure `P.real` of the event that the ballot's $j$-th entry is `true`. The statements using it assume each ballot is measurable, so this event is measurable.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 22, Theorem 3 ("p_{ij} denotes the probability that voter i votes for producer j")

import Mathlib

open MeasureTheory

namespace CommitteeVoting.ExpConv

/-- The vote probability `p_{ij}` (Theorem 3, p. 22): the probability that voter `i` approves
candidate `j`, for random ballots `ballot i : Ω → (Fin m → Bool)` on a probability space
`(Ω, P)`. -/
noncomputable def voteProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n m : ℕ}
    (ballot : Fin n → Ω → Fin m → Bool) (i : Fin n) (j : Fin m) : ℝ :=
  P.real {ω | ballot i ω j = true}

end CommitteeVoting.ExpConv


