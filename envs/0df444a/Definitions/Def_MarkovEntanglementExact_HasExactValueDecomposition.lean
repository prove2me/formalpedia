-- Prove2me | Definitions.Def_MarkovEntanglementExact_HasExactValueDecomposition
-- name    : MarkovEntanglementExact_HasExactValueDecomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:31.901538+00:00
-- url     : https://prove2.me/theorems/bc1fabcd-dc9f-4e8a-9512-ca7fd17d1106
-- title:
--   Exact value decomposition by reward-local maps
-- statement:
--   Let $P$ be a transition matrix on $S_A\times S_B$ and $\gamma$ a discount factor. $P$ has an **exact value decomposition** if there are maps $\hat Q_A:\mathbb R^{S_A}\to\mathbb R^{S_A}$ and $\hat Q_B:\mathbb R^{S_B}\to\mathbb R^{S_B}$ such that, for all local rewards $r_A,r_B$, the Q-value $Q$ of $P$ for the reward $r_A\otimes e+e\otimes r_B$ at discount $\gamma$ satisfies
--   $$Q=\hat Q_A(r_A)\otimes e+e\otimes\hat Q_B(r_B).$$
--
--   This is the hypothesis of Theorem 2 of the paper. Each map reads only its own agent's reward, and the maps are fixed before the rewards. Appendix E of the paper shows that if the maps may depend on both rewards, the decomposition no longer implies separability.
--
--   **Formalization Note** The Q-value is any solution of the Bellman equation `IsBellmanQ`, and such a solution exists and is unique for a transition matrix and $0\le\gamma<1$. By definition, this is the hypothesis `hdec` of the published `MarkovEntanglement.two_agent_value_decomposition_implies_separable`.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, hypothesis of Theorem 2, p.12

import Mathlib
import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

variable {SA SB : Type*} [Fintype SA] [Fintype SB]

/-- Exact value decomposition for every reward pair: there are local maps `Q̂_A`, `Q̂_B`, each
reading only its own agent's reward, such that the Q-value of `(P, r_A ⊗ e + e ⊗ r_B)` at
discount `γ` equals `Q̂_A(r_A) ⊗ e + e ⊗ Q̂_B(r_B)`, for every `r_A` and `r_B`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, hypothesis of
Theorem 2, p.12.

**Formalization Note.** The maps come before the rewards: `∃ Q̂_A Q̂_B, ∀ r_A r_B`. Appendix E,
p.36, shows the other order is too weak. Q-values are the solutions of `IsBellmanQ`, the Bellman
equation of p.7, which for a transition matrix and `0 ≤ γ < 1` has exactly one solution. -/
def HasExactValueDecomposition (P : Matrix (SA × SB) (SA × SB) ℝ) (γ : ℝ) : Prop :=
  ∃ (QA : (SA → ℝ) → (SA → ℝ)) (QB : (SB → ℝ) → (SB → ℝ)),
    ∀ (rA : SA → ℝ) (rB : SB → ℝ) (Q : SA × SB → ℝ),
      IsBellmanQ P (fun p => rA p.1 + rB p.2) γ Q →
        ∀ p : SA × SB, Q p = QA rA p.1 + QB rB p.2

end MarkovEntanglementExact


