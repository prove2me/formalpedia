-- Prove2me | Definitions.Def_CHMSPricing_OpmUniform_Opm
-- name    : CHMSPricing_OpmUniform_Opm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:37:13.696235+00:00
-- url     : https://prove2.me/theorems/7b76f7e6-4439-43ba-8278-2c9bceaecc9c
-- title:
--   Order-oblivious posted prices: maximal feasible desiring sets and the revenue estimate $\mathcal R^{obl}_{\mathbf p}$
-- statement:
--   Fix prices $\mathbf p = (p_i)$ and a value profile $\mathbf v$. Agent $i$ **desires** service if $v_i \ge p_i$. Given a downward-closed set system $\mathcal J$, the class $\mathcal S_{\mathbf v}$ consists of the **maximal feasible subsets of desiring agents**: the sets $S$ with
--
--   1. $S \in \mathcal J$;
--   2. $v_i \ge p_i$ for all $i \in S$;
--   3. every feasible strict superset $S' \supsetneq S$ contains some agent $i$ with $v_i < p_i$.
--
--   The class $\mathcal S_{\mathbf v}$ is never empty: a largest feasible set of desiring agents belongs to it. In an order-oblivious posted-price mechanism the agents are approached in an adversarial order, and each buys at its price if it desires service and can still be feasibly served; the set of buyers is then a member of $\mathcal S_{\mathbf v}$. The paper estimates the revenue of such a mechanism pessimistically by
--   $$\mathcal R^{\mathrm{obl}}_{\mathbf p} = \mathbb E_{\mathbf v \sim \mathbf F}\ \min_{S \in \mathcal S_{\mathbf v}} \sum_{i \in S} p_i ,$$
--   the revenue guaranteed against an adversary who, knowing the values, chooses the least profitable maximal feasible set of buyers.
--
--   **Formalization Note** The minimum is a genuine minimum over a finite nonempty family (nonemptiness is proved in the file), not an infimum with a default value. Condition (3) is stated literally, with "superset" read as strict superset (otherwise $S$ itself would violate it).
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.2, Order-oblivious posted prices

import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_ValueDist
import Definitions.Def_CHMSPricing_OpmUniform_SetSystem

namespace CHMSPricing.OpmUniform

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The agents who "desire" service at prices `p` given values `v`: those with `vᵢ ≥ pᵢ`. -/
noncomputable def desiring (p v : ι → ℝ) : Finset ι :=
  open Classical in Finset.univ.filter (fun i => p i ≤ v i)

/-- §2.2, p. 4: `S ∈ 𝒮_v`, i.e. `S` is a maximal feasible subset of agents that desire service
given values `v` and prices `p`: (1) `S ∈ 𝒥`, (2) `vᵢ ≥ pᵢ` for all `i ∈ S`, and (3) every
feasible (strict) superset `S'` of `S` contains some agent `i` with `vᵢ < pᵢ`. -/
def IsMaxFeasDesiring (J : SetSystem ι) (p v : ι → ℝ) (S : Finset ι) : Prop :=
  J.Feasible S ∧ (∀ i ∈ S, p i ≤ v i) ∧
    ∀ S' : Finset ι, S ⊂ S' → J.Feasible S' → ∃ i ∈ S', v i < p i

open Classical in
/-- The finite class `𝒮_v` of maximal feasible desiring sets. -/
noncomputable def maxFeasDesiringSets (J : SetSystem ι) (p v : ι → ℝ) : Finset (Finset ι) :=
  Finset.univ.filter (IsMaxFeasDesiring J p v)

/-- `𝒮_v` is nonempty: a largest feasible subset of the desiring agents is maximal. -/
theorem maxFeasDesiringSets_nonempty (J : SetSystem ι) (p v : ι → ℝ) :
    (maxFeasDesiringSets J p v).Nonempty := by
  classical
  have hne : ((desiring p v).powerset.filter J.Feasible).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, J.feasible_empty⟩⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  refine ⟨S, ?_⟩
  unfold maxFeasDesiringSets
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hS.2, fun i hi => ?_, fun S' hSS' hS' => ?_⟩
  · have := hS.1 hi
    simpa [desiring] using this
  · by_contra h
    push Not at h
    have hsub : S' ⊆ desiring p v := fun i hi => by simpa [desiring] using h i hi
    have := hmax S' (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hsub, hS'⟩)
    exact absurd (Finset.card_lt_card hSS') (not_lt.2 this)

/-- §2.2, p. 4: the order-oblivious revenue estimate
`ℛ^obl_p = 𝔼_{v∼F} min_{S ∈ 𝒮_v} ∑_{i ∈ S} pᵢ`. -/
noncomputable def oblRevenue (D : ι → ValueDist) (J : SetSystem ι) (p : ι → ℝ) : ℝ :=
  ∫ v, (maxFeasDesiringSets J p v).inf' (maxFeasDesiringSets_nonempty J p v)
    (fun S => ∑ i ∈ S, p i) ∂(prior D)

end CHMSPricing.OpmUniform


