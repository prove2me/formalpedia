-- Prove2me | Definitions.Def_CompDesignBFM_Supplement_IsPNEOf
-- name    : CompDesignBFM_Supplement_IsPNEOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:03:06.866712+00:00
-- url     : https://prove2.me/theorems/45c6c071-f616-49d3-8198-a27ee805ffb3
-- title:
--   Pure Nash equilibrium of a compensation rule
-- statement:
--   Let $p$ be a deterministic payment rule, which assigns to every participating set $S\subseteq N$ a payment $p_i(S)$ to each agent $i$, and let $c\in\mathbb R^N_{\ge0}$ be the agents' private costs. A participating set $S$ is a **pure Nash equilibrium** of the participation game if no agent gains by switching between opting in and opting out:
--
--   $$p_i(S)\ge c_i\quad(i\in S),\qquad p_i(S\cup\{i\})\le c_i\quad(i\notin S).$$
--
--   The set of such equilibria is $E(p,c)$. This is the equilibrium notion behind the price of anarchy and the price of stability of compensation design.
--
--   **Formalization Note** A payment rule is a function of the participating set only, so it is cost oblivious by type. For the marginal-contribution rule this notion coincides by definition with the base mission's `IsPNE`.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1.2.1, p.5 (PDF 7)

import Mathlib

namespace CompDesignBFM

namespace Supplement

/-- A pure Nash equilibrium of the participation game induced by a general compensation rule `p`
(Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1.2.1, p.5, PDF 7): with costs `c`, the participating set `S` is a pure Nash equilibrium if
`pᵢ(S) ≥ cᵢ` for every `i ∈ S` and `pᵢ(S ∪ {i}) ≤ cᵢ` for every `i ∉ S`.
**Formalization Note.** A payment rule is a function `p : Finset (Fin n) → Fin n → ℝ` of the
participating set only, so it is cost-oblivious by type. For the marginal-contribution rule this is the
base mission's `IsPNE F B c S`, which equals `IsPNEOf (mcPay F B) c S` by definition. -/
def IsPNEOf {n : ℕ} (p : Finset (Fin n) → Fin n → ℝ) (c : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  (∀ i ∈ S, c i ≤ p S i) ∧ ∀ i, i ∉ S → p (insert i S) i ≤ c i

end Supplement

end CompDesignBFM


