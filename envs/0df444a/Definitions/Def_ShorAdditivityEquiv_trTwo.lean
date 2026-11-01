-- Prove2me | Definitions.Def_ShorAdditivityEquiv_trTwo
-- name    : ShorAdditivityEquiv_trTwo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:28:13.065437+00:00
-- url     : https://prove2.me/theorems/47248931-b019-4608-bff7-0b79bbf9468b
-- title:
--   Partial trace $\mathrm{Tr}_2$ over $\mathcal H_{A_2}\otimes\mathcal H_{B_2}$ of a four-party operator
-- statement:
--   Let $\sigma$ be an operator on the four-party space $\mathcal H_{A_1}\otimes\mathcal H_{A_2}\otimes\mathcal H_{B_1}\otimes\mathcal H_{B_2}$. The partial trace $\mathrm{Tr}_2\,\sigma$ "traces out the space $\mathcal H_{A_2}\otimes\mathcal H_{B_2}$" and is an operator on $\mathcal H_{A_1}\otimes\mathcal H_{B_1}$:
--   $$
--   (\mathrm{Tr}_2\,\sigma)_{(a_1,b_1),(a_1',b_1')} = \sum_{a_2,\,b_2}\sigma_{(a_1a_2,\,b_1b_2),\,(a_1'a_2,\,b_1'b_2)} .
--   $$
--   It is one of the two marginals in the strong superadditivity inequality $E_F(\sigma)\ge E_F(\mathrm{Tr}_2\sigma)+E_F(\mathrm{Tr}_1\sigma)$.
--
--   **Formalization Note** The four-party space is indexed by $(A_1\times A_2)\times(B_1\times B_2)$, the $A\,|\,B$ cut first; the result is indexed by $A_1\times B_1$ with the $A$ part first, the convention of `formation`.
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Theorem 1 (iv), p. 6

import Mathlib

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Theorem 1 (iv), p.6: the partial trace `Tr₂` on the quadripartite space
`H_{A1} ⊗ H_{A2} ⊗ H_{B1} ⊗ H_{B2}`; "Tr₂ traces out the space H_{A2} ⊗ H_{B2}".

**Formalization Note.** The quadripartite state is indexed by `(A₁ × A₂) × (B₁ × B₂)` (the
`A | B` cut first), and `Tr₂ σ` is indexed by `A₁ × B₁`:
`(Tr₂ σ) (a₁,b₁) (a₁',b₁') = Σ_{a₂,b₂} σ ((a₁,a₂),(b₁,b₂)) ((a₁',a₂),(b₁',b₂))`. The result is a
bipartite matrix on `H_{A1} ⊗ H_{B1}` with the `A` part first, the convention of `formation`. -/
def trTwo {A₁ A₂ B₁ B₂ : Type} [Fintype A₂] [Fintype B₂]
    (σ : Matrix ((A₁ × A₂) × (B₁ × B₂)) ((A₁ × A₂) × (B₁ × B₂)) ℂ) :
    Matrix (A₁ × B₁) (A₁ × B₁) ℂ :=
  Matrix.of fun p q => ∑ a₂, ∑ b₂, σ ((p.1, a₂), (p.2, b₂)) ((q.1, a₂), (q.2, b₂))

end ShorAdditivityEquiv


