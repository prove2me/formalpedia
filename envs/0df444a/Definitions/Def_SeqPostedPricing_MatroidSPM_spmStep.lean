-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_spmStep
-- name    : SeqPostedPricing_MatroidSPM_spmStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:36:17.442885+00:00
-- url     : https://prove2.me/theorems/423c6582-4995-4e9a-aefa-ba3604e94ce7
-- title:
--   One step of a sequential posted-price mechanism
-- statement:
--   Let $A$ be the set of agents served so far. At a step where agent $i$ is considered, with price $p_i$ and value $v_i$:
--
--   - if $i$ is one of the agents the mechanism makes offers to and $A\cup\{i\}\in\mathcal J$, agent $i$ is offered service at price $p_i$;
--   - the agent accepts if and only if $p_i\le v_i$ (the price is no more than its value), and then $A\leftarrow A\cup\{i\}$.
--
--   **Formalization Note** The set of agents the mechanism makes offers to is a parameter `active`; the mechanism $\mathcal S$ of §4 uses the agents with $q_i>0$.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, unnumbered, p. 4; §1, p. 1

import Mathlib
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **One step of a sequential posted-price mechanism.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §2.2, unnumbered, p. 4 (PDF p. 6): "(a) If A ∪ {σ(i)} ∈ J, offer to serve agent σ(i) at
price pi. (b) If the agent accepts, A ← A ∪ {σ(i)}."; §1, p. 1 (PDF p. 3): "A rational agent
will accept if and only if the price is no more than their private value for service."

Given the set `A` of agents served so far, agent `i` is offered service when it is active and
`A ∪ {i}` is feasible; it accepts when `p i ≤ v i`, and is then added to `A`.

**Formalization Note.** `active` is the set of agents the mechanism makes offers to; the mission
uses the agents with `q_i > 0` (`spmActive`), since an agent with `q_i = 0` accepts its offer
with probability `0` in the paper. Acceptance is `p i ≤ v i` ("no more than their private
value"). -/
noncomputable def spmStep {n : ℕ} (Feas : Finset (Fin n) → Prop) (p : Fin n → ℝ) (active : Finset (Fin n))
    (v : Fin n → ℝ) (A : Finset (Fin n)) (i : Fin n) : Finset (Fin n) :=
  if i ∈ active ∧ Feas (insert i A) ∧ p i ≤ v i then insert i A else A

end SeqPostedPricing.MatroidSPM


