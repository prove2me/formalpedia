-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_spmActive
-- name    : SeqPostedPricing_MatroidSPM_spmActive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:38:47.113064+00:00
-- url     : https://prove2.me/theorems/061855a7-345c-48b8-a23c-3060f9b13427
-- title:
--   Agents with $q_i^M>0$
-- statement:
--   For a mechanism $M$, the agents the mechanism $\mathcal S$ of §4 makes offers to are those with positive allocation probability:
--
--   $$
--   \{i\in[n]:\ q_i^M>0\}.
--   $$
--
--   **Formalization Note** In the paper an agent with $q_i=0$ is offered a price it accepts with probability exactly $0$; leaving it out changes the outcome only on a null event, and avoids the price $F_i^{-1}(1)$, which need not exist.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, unnumbered, p. 6

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_allocProb
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **Agents that the mechanism `S` makes offers to: those with `q_i^M > 0`.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §4, unnumbered, p. 6 (PDF p. 8): "If offered service, agent i accepts with probability
exactly qi."

`spmActive μ M` is the set of agents `i` with `q_i^M > 0`.

**Formalization Note.** In the paper an agent with `q_i = 0` is offered a price it accepts with
probability exactly `0`, so leaving it out changes the outcome of `S` only on a null event; it
also avoids pricing it at `F_i^{−1}(1)`, which need not exist. -/
noncomputable def spmActive {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (M : Mechanism n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0 < allocProb μ M i)

end SeqPostedPricing.MatroidSPM


