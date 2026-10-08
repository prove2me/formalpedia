-- Prove2me | Definitions.Def_CHMSPricing_SpmPartition_Spm
-- name    : CHMSPricing_SpmPartition_Spm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:23:47.723833+00:00
-- url     : https://prove2.me/theorems/5ed13dce-648b-48fd-9dd4-b961cd34ed18
-- title:
--   Sequential posted-price mechanisms (SPM): the run, the served set, the expected revenue R^σ_p, and single-unit offer probabilities
-- statement:
--   A **sequential posted-price mechanism** is given by an ordering $\sigma$ of the agents and a price $p_i$ for each agent $i$. It runs as follows on a value vector $\mathbf v$:
--   1. initialise $A\leftarrow\emptyset$;
--   2. for $k=0,\dots,n-1$, with $i=\sigma(k)$: if $A\cup\{i\}\in\mathcal J$, offer service to $i$ at price $p_i$; the agent accepts iff $p_i\le v_i$, and then $A\leftarrow A\cup\{i\}$;
--   3. serve the agents in $A$.
--
--   Its expected revenue is
--
--   $$
--   \mathcal R^\sigma_{\mathbf p}=\mathbb E_{\mathbf v}\Big[\sum_{i\in A(\mathbf v)}p_i\Big].
--   $$
--
--   For the single-unit analysis of Appendix C.2 the file also defines, for a vector $(q_0,\dots,q_{n-1})$ of acceptance probabilities indexed by position in the offer order,
--
--   $$
--   c_k=\prod_{j<k}(1-q_j),
--   $$
--
--   the probability that the $k$-th agent in line is offered the single unit.
--
--   **Formalization Note** The ordering is 0-based ($\sigma(0)$ is approached first). The price is attached to the agent: in the paper's step (a) the price offered to agent $\sigma(i)$ is that agent's price. An agent accepts iff the price is at most its value (p. 1).
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.2 (SPM and R^σ_p); p. 14, App. C.2 (c_i = Π_{j<i}(1 − q_j))

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem

namespace CHMSPricing.SpmPartition

open MeasureTheory

variable {n : ℕ}

open Classical in
/-- One round of a sequential posted-price mechanism (§2.2, p. 4): with current served set `A`,
agent `i` is offered service at price `pᵢ` iff `A ∪ {i} ∈ 𝒥`, and accepts iff `pᵢ ≤ vᵢ`. -/
noncomputable def spmStep (J : SetSystem (Fin n)) (p v : Fin n → ℝ) (A : Finset (Fin n))
    (i : Fin n) : Finset (Fin n) :=
  if J.Feasible (insert i A) ∧ p i ≤ v i then insert i A else A

/-- The set of agents served after the first `k` rounds of the SPM with ordering `σ`
(`σ 0` is approached first) and prices `p`, at value profile `v`. -/
noncomputable def spmServedBefore (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n))
    (p v : Fin n → ℝ) (k : ℕ) : Finset (Fin n) :=
  ((List.finRange n).take k).foldl (fun A k' => spmStep J p v A (σ k')) ∅

/-- The set `A` of agents served by the SPM at the end of the run. -/
noncomputable def spmServed (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n))
    (p v : Fin n → ℝ) : Finset (Fin n) :=
  spmServedBefore J σ p v n

/-- `ℛ^σ_p`: the expected revenue `𝔼_v[∑_{i ∈ A} pᵢ]` of the SPM. -/
noncomputable def spmRevenue (D : Fin n → ValueDist) (J : SetSystem (Fin n))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) : ℝ :=
  ∫ v, ∑ i ∈ spmServed J σ p v, p i ∂(prior D)

/-- App. C.2, p. 14: for positions `0, …, n − 1` in offer order with acceptance probabilities
`q`, `cₖ = ∏_{j < k} (1 − q_j)`, the probability that the `k`-th agent is offered service when
there is a single unit. -/
def oneUnitOfferProb (q : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∏ j ∈ Finset.univ.filter (· < k), (1 - q j)

end CHMSPricing.SpmPartition


