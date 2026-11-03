-- Prove2me | Definitions.Def_DRAllocCV_InspectedArgmaxAllocation
-- name    : DRAllocCV_InspectedArgmaxAllocation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:12.044195+00:00
-- url     : https://prove2.me/theorems/e26aeece-31cf-495e-9b66-a4c110621f46
-- title:
--   Case (ii) of a favored-agent mechanism
-- statement:
--   In scenario $t$, the mechanism $(p,q)$ **allocates with inspection to a maximizer of the net value** if there is $i'\in\arg\max_{i\in\mathcal I}(t_i-c_i)$ with
--
--   $$
--   p_{i'}(t)=q_{i'}(t)=1,\qquad p_i(t)=q_i(t)=0\ \ \text{for all } i\ne i' .
--   $$
--
--   This is case (ii) of Definition 3. The winner may be the favored agent.
--
--   **Formalization Note** The winner $i'$ may be any maximizer, chosen separately in each scenario. The paper fixes the lexicographic choice $i'=\min\arg\max_i(t_i-c_i)$ (p.8), which is one instance.
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.7, Definition 3 (ii); p.8, first tie-breaking rule

import Mathlib

namespace DRAllocCV

/-- **Case (ii) of a favored-agent mechanism** (Definition 3 (ii), Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, p.7): in scenario `t`
the good goes, with inspection, to some agent `i′ ∈ argmax_{i ∈ ℐ} (tᵢ − cᵢ)`:
`pᵢ′(t) = qᵢ′(t) = 1` and `pᵢ(t) = qᵢ(t) = 0` for all `i ≠ i′`.

**Formalization Note.** The winner `i′` may be any maximizer of the net value `tᵢ − cᵢ`, chosen
separately in each scenario. The paper fixes the lexicographic choice `i′ = min argmax` (p.8);
that choice is one instance of this definition. -/
def InspectedArgmaxAllocation {ι : Type*} (c : ι → ℝ) (p q : ι → (ι → ℝ) → ℝ)
    (t : ι → ℝ) : Prop :=
  ∃ i', (∀ j, t j - c j ≤ t i' - c i') ∧ p i' t = 1 ∧ q i' t = 1 ∧
    ∀ i, i ≠ i' → p i t = 0 ∧ q i t = 0

end DRAllocCV


