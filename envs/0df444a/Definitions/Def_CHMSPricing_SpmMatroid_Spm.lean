-- Prove2me | Definitions.Def_CHMSPricing_SpmMatroid_Spm
-- name    : CHMSPricing_SpmMatroid_Spm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:18:04.543632+00:00
-- url     : https://prove2.me/theorems/0b0d6d84-5bac-4958-bea6-1777177cf7fb
-- title:
--   Sequential posted-price mechanisms: the run, offered and blocked agents, expected revenue
-- statement:
--   A **sequential posted-price mechanism** (SPM) $\mathcal S$ over agents $[n]$ under a feasibility constraint $\mathcal J$ is given by an ordering $\sigma$ of the agents and a price $p_i$ for each agent $i$ (§2.2). On a value profile $\mathbf v$ it runs as follows:
--
--   1. Initialize $A \leftarrow \emptyset$.
--   2. For $k = 1, \dots, n$: let $i = \sigma(k)$. If $A \cup \{i\} \in \mathcal J$, agent $i$ is **offered** service at price $p_i$; it accepts if and only if $p_i \le v_i$, and then $A \leftarrow A \cup \{i\}$.
--   3. Serve the agents in $A$.
--
--   An agent that is not offered service at its turn is **blocked**. The expected revenue of the SPM is
--
--   $$\mathcal R^\sigma_{\mathbf p} = \mathbb E_{\mathbf v}\Big[\sum_{i \in A(\mathbf v)} p_i\Big].$$
--
--   **Formalization Note** Positions are $0$-based: $\sigma(0)$ is approached first. The price is attached to the agent, as in §4 ("sets a price of $p_i$ for agent $i$"), so the agent at position $k$ is offered $p_{\sigma(k)}$. An agent accepts iff the price is no more than its value (p. 1).
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.2

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_ValueDist
import Definitions.Def_CHMSPricing_SpmMatroid_SetSystem

namespace CHMSPricing.SpmMatroid

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

/-- Agent `i` is offered service at its turn (position `σ⁻¹ i`): adding it to the set served
so far is feasible. -/
def spmOffered (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ)
    (i : Fin n) : Prop :=
  J.Feasible (insert i (spmServedBefore J σ p v (σ.symm i : ℕ)))

open Classical in
/-- The agents that are blocked: not offered service at their turn, because adding them to the
set served so far would be infeasible. -/
noncomputable def spmBlocked (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => ¬ spmOffered J σ p v i)

/-- `ℛ^σ_p`: the expected revenue `𝔼_v[∑_{i ∈ A} pᵢ]` of the SPM. -/
noncomputable def spmRevenue (D : Fin n → ValueDist) (J : SetSystem (Fin n))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) : ℝ :=
  ∫ v, ∑ i ∈ spmServed J σ p v, p i ∂(prior D)

end CHMSPricing.SpmMatroid


