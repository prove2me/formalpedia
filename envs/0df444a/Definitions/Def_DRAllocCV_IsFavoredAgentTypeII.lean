-- Prove2me | Definitions.Def_DRAllocCV_IsFavoredAgentTypeII
-- name    : DRAllocCV_IsFavoredAgentTypeII
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:49.956005+00:00
-- url     : https://prove2.me/theorems/f6e7d763-6e92-4a1f-88d8-7d5b0faafb01
-- title:
--   Type (ii) favored-agent mechanism with favored agent $i^\star$ and threshold $\nu^\star$
-- statement:
--   Fix a favored agent $i^\star\in\mathcal I$ and a threshold value $\nu^\star\in\mathbb R$. A mechanism $(p,q)$ is a **type (ii) favored-agent mechanism** if for every scenario $t\in\mathcal T$:
--
--   1. if $\max_{i\ne i^\star}(t_i-c_i)<\nu^\star$, the good goes to $i^\star$ without inspection (case (i));
--   2. if $\max_{i\ne i^\star}(t_i-c_i)\ge\nu^\star$, the good goes, with inspection, to an agent $i'\in\arg\max_{i\in\mathcal I}(t_i-c_i)$ (case (ii)).
--
--   Ties $\max_{i\ne i^\star}(t_i-c_i)=\nu^\star$ are always resolved as in case (ii). The mechanism of the goal theorem is of this type.
--
--   **Formalization Note** "$\max_{i\ne i^\star}(t_i-c_i)<\nu^\star$" is written as a condition on every $i\ne i^\star$ and "$\ge\nu^\star$" as the existence of one such $i$; with $I\ge2$ these coincide with the paper's conditions. The case-(ii) winner is any maximizer (the paper's lexicographic choice is one).
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.7, Definition 3; p.8, tie-breaking rules and type (ii)

import Mathlib
import Definitions.Def_DRAllocCV_typeSpace
import Definitions.Def_DRAllocCV_FavoredAllocation
import Definitions.Def_DRAllocCV_InspectedArgmaxAllocation

namespace DRAllocCV

/-- A **type (ii) favored-agent mechanism** with favored agent `i⋆` and threshold value `ν⋆`
(Definition 3 and the tie-breaking rules, Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, pp.7–8): for every scenario `t ∈ 𝒯`,

* if `max_{i ≠ i⋆} (tᵢ − cᵢ) < ν⋆` (case (i)), the favored agent receives the good without
  inspection;
* if `max_{i ≠ i⋆} (tᵢ − cᵢ) ≥ ν⋆` (case (ii), with ties `= ν⋆` resolved as in (ii)), the good
  goes with inspection to an agent with the highest net value `tᵢ − cᵢ`.

**Formalization Note.** `max_{i ≠ i⋆} (tᵢ − cᵢ) < ν⋆` is written `∀ i ≠ i⋆, tᵢ − cᵢ < ν⋆` and
`≥ ν⋆` as `∃ i ≠ i⋆, tᵢ − cᵢ ≥ ν⋆`; with at least two agents these are the paper's conditions.
The winner in case (ii) is any maximizer (see `InspectedArgmaxAllocation`); the paper's
lexicographic rule is a special case. Only values on `𝒯` are constrained. -/
def IsFavoredAgentTypeII {ι : Type*} (tlo thi c : ι → ℝ) (istar : ι) (ν : ℝ)
    (p q : ι → (ι → ℝ) → ℝ) : Prop :=
  ∀ t ∈ typeSpace tlo thi,
    ((∀ i, i ≠ istar → t i - c i < ν) → FavoredAllocation istar p q t) ∧
    ((∃ i, i ≠ istar ∧ ν ≤ t i - c i) → InspectedArgmaxAllocation c p q t)

end DRAllocCV


