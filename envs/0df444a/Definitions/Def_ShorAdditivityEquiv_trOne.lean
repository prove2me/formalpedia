-- Prove2me | Definitions.Def_ShorAdditivityEquiv_trOne
-- name    : ShorAdditivityEquiv_trOne
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:28:11.340984+00:00
-- url     : https://prove2.me/theorems/f6bdf736-ab71-48a0-8859-0cbebeb24d62
-- title:
--   Partial trace $\mathrm{Tr}_1$ over $\mathcal H_{A_1}\otimes\mathcal H_{B_1}$ of a four-party operator
-- statement:
--   Let $\sigma$ be an operator on the four-party space $\mathcal H_{A_1}\otimes\mathcal H_{A_2}\otimes\mathcal H_{B_1}\otimes\mathcal H_{B_2}$. The partial trace $\mathrm{Tr}_1\,\sigma$ "traces out the space $\mathcal H_{A_1}\otimes\mathcal H_{B_1}$" and is an operator on $\mathcal H_{A_2}\otimes\mathcal H_{B_2}$:
--   $$
--   (\mathrm{Tr}_1\,\sigma)_{(a_2,b_2),(a_2',b_2')} = \sum_{a_1,\,b_1}\sigma_{(a_1a_2,\,b_1b_2),\,(a_1a_2',\,b_1b_2')} .
--   $$
--   It is the second marginal in the strong superadditivity inequality $E_F(\sigma)\ge E_F(\mathrm{Tr}_2\sigma)+E_F(\mathrm{Tr}_1\sigma)$.
--
--   **Formalization Note** The four-party space is indexed by $(A_1\times A_2)\times(B_1\times B_2)$; the result is indexed by $A_2\times B_2$ with the $A$ part first, the convention of `formation`.
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Theorem 1 (iv), p. 6

import Mathlib

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Theorem 1 (iv), p.6: the partial trace `Tr₁` on the quadripartite space
`H_{A1} ⊗ H_{A2} ⊗ H_{B1} ⊗ H_{B2}`; "the operator Tr₁ traces out the space H_{A1} ⊗ H_{B1}".

**Formalization Note.** The quadripartite state is indexed by `(A₁ × A₂) × (B₁ × B₂)` (the
`A | B` cut first), and `Tr₁ σ` is indexed by `A₂ × B₂`:
`(Tr₁ σ) (a₂,b₂) (a₂',b₂') = Σ_{a₁,b₁} σ ((a₁,a₂),(b₁,b₂)) ((a₁,a₂'),(b₁,b₂'))`. The result is a
bipartite matrix on `H_{A2} ⊗ H_{B2}` with the `A` part first, the convention of `formation`. -/
def trOne {A₁ A₂ B₁ B₂ : Type} [Fintype A₁] [Fintype B₁]
    (σ : Matrix ((A₁ × A₂) × (B₁ × B₂)) ((A₁ × A₂) × (B₁ × B₂)) ℂ) :
    Matrix (A₂ × B₂) (A₂ × B₂) ℂ :=
  Matrix.of fun p q => ∑ a₁, ∑ b₁, σ ((a₁, p.1), (b₁, p.2)) ((a₁, q.1), (b₁, q.2))

end ShorAdditivityEquiv


