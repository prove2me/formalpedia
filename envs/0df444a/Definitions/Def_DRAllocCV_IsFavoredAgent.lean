-- Prove2me | Definitions.Def_DRAllocCV_IsFavoredAgent
-- name    : DRAllocCV_IsFavoredAgent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:14:00.391408+00:00
-- url     : https://prove2.me/theorems/f307e6f0-f7ec-46b6-b006-8d382672405c
-- title:
--   Favored-agent mechanism (Definition 3)
-- statement:
--   A mechanism $(p,q)$ is a **favored-agent mechanism** with favored agent $i^\star$ and threshold value $\nu^\star$ if it follows case (i) (the good goes to $i^\star$ without inspection) when $\max_{i\ne i^\star}(t_i-c_i)<\nu^\star$, follows case (ii) (the good goes, with inspection, to a maximizer of $t_i-c_i$) when $\max_{i\ne i^\star}(t_i-c_i)>\nu^\star$, and resolves the ties $\max_{i\ne i^\star}(t_i-c_i)=\nu^\star$ by a fixed tie-breaking rule: always as in (i) (type (i)) or always as in (ii) (type (ii)).
--
--   Intuitively, the favored agent gets the good unless some other agent's type exceeds his inspection cost plus the threshold; then the agent with the highest net value wins and is inspected.
--
--   **Formalization Note** Definition 3 lets each tie be resolved either way, and p.8 then makes the choice a tie-breaking rule of type (i) or type (ii). The definition is the disjunction of the two types. Resolving ties scenario by scenario, independently of the rule, can violate (IC), so it is not what the paper's results are about.
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.7, Definition 3; p.8, tie-breaking rules

import Mathlib
import Definitions.Def_DRAllocCV_IsFavoredAgentTypeI
import Definitions.Def_DRAllocCV_IsFavoredAgentTypeII

namespace DRAllocCV

/-- A **favored-agent mechanism** with favored agent `i⋆` and threshold value `ν⋆`
(Definition 3, Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, pp.7–8): a mechanism that follows case (i) when
`max_{i ≠ i⋆} (tᵢ − cᵢ) < ν⋆` and case (ii) when it is `> ν⋆`, and whose second tie-breaking rule
resolves the ties `max_{i ≠ i⋆} (tᵢ − cᵢ) = ν⋆` always as in (i) (type (i)) or always as in (ii)
(type (ii)), p.8.

**Formalization Note.** Definition 3 lets each tie be resolved either way; the paper then fixes a
tie-breaking rule, of type (i) or type (ii) (p.8), and every favored-agent mechanism it uses is of
one of these types. A scenario-by-scenario choice is not intended: it can violate (IC) (resolve
the tie as (i) at one type of `i⋆` and as (ii), with another winner, at another type of `i⋆` with
the same `t₋ᵢ⋆`), so "all favored-agent mechanisms are feasible" (p.8) holds only for the
rule-based reading encoded here. -/
def IsFavoredAgent {ι : Type*} (tlo thi c : ι → ℝ) (istar : ι) (ν : ℝ)
    (p q : ι → (ι → ℝ) → ℝ) : Prop :=
  IsFavoredAgentTypeI tlo thi c istar ν p q ∨ IsFavoredAgentTypeII tlo thi c istar ν p q

end DRAllocCV


