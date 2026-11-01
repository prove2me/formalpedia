-- Prove2me | Definitions.Def_ShorAdditivityEquiv_tensorState
-- name    : ShorAdditivityEquiv_tensorState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:28:06.769877+00:00
-- url     : https://prove2.me/theorems/1df3aa07-f6c6-467c-afde-0af198280a3c
-- title:
--   Product $\sigma_1\otimes\sigma_2$ of two bipartite states, regrouped to the cut $A_1A_2\,|\,B_1B_2$
-- statement:
--   Let $\sigma_1$ be an operator on $\mathcal H_{A_1}\otimes\mathcal H_{B_1}$ and $\sigma_2$ an operator on $\mathcal H_{A_2}\otimes\mathcal H_{B_2}$. Their tensor product $\sigma_1\otimes\sigma_2$ is an operator on the four-party space, and Theorem 1 (iii) regards it as a **bipartite** state with Alice holding $A_1A_2$ and Bob holding $B_1B_2$:
--   $$
--   (\sigma_1\otimes\sigma_2)_{(a_1a_2,\,b_1b_2),\,(a_1'a_2',\,b_1'b_2')} = (\sigma_1)_{(a_1,b_1),(a_1',b_1')}\,(\sigma_2)_{(a_2,b_2),(a_2',b_2')}.
--   $$
--   This is the argument of $E_F(\sigma_1\otimes\sigma_2)$ in the additivity of the entanglement of formation: "the entanglement of formation is calculated over the bipartite A–B partition".
--
--   **Formalization Note** The result is indexed by $(A_1\times A_2)\times(B_1\times B_2)$, the Alice part first, so that the platform's `formation` (which traces the second factor) computes $E_F$ across $A_1A_2\,|\,B_1B_2$ and not across $\sigma_1\,|\,\sigma_2$. It is the Kronecker product on $(A_1\times B_1)\times(A_2\times B_2)$ reindexed by $((a_1,b_1),(a_2,b_2))\mapsto((a_1,a_2),(b_1,b_2))$.
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Theorem 1 (iii), p. 5

import Mathlib

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Theorem 1 (iii), p.5: the state `σ₁ ⊗ σ₂` of two bipartite states
`σ₁ ∈ H_{A1} ⊗ H_{B1}` and `σ₂ ∈ H_{A2} ⊗ H_{B2}`, regarded as a bipartite state across the cut
`A₁A₂ | B₁B₂` ("In particular, the entanglement of formation is calculated over the bipartite
A–B partition").

**Formalization Note.** The result is indexed by `(A₁ × A₂) × (B₁ × B₂)`: its entry at
`((a₁,a₂),(b₁,b₂)), ((a₁',a₂'),(b₁',b₂'))` is `σ₁ (a₁,b₁) (a₁',b₁') * σ₂ (a₂,b₂) (a₂',b₂')`. This
is the Kronecker product `σ₁ ⊗ₖ σ₂` on `(A₁ × B₁) × (A₂ × B₂)` reindexed by the regrouping
`((a₁,b₁),(a₂,b₂)) ↦ ((a₁,a₂),(b₁,b₂))`, so that `formation` (which traces the second factor)
computes `E_F` across `A₁A₂ | B₁B₂`, not across `σ₁ | σ₂`. -/
def tensorState {A₁ B₁ A₂ B₂ : Type} (σ₁ : Matrix (A₁ × B₁) (A₁ × B₁) ℂ)
    (σ₂ : Matrix (A₂ × B₂) (A₂ × B₂) ℂ) :
    Matrix ((A₁ × A₂) × (B₁ × B₂)) ((A₁ × A₂) × (B₁ × B₂)) ℂ :=
  Matrix.of fun p q => σ₁ (p.1.1, p.2.1) (q.1.1, q.2.1) * σ₂ (p.1.2, p.2.2) (q.1.2, q.2.2)

end ShorAdditivityEquiv


