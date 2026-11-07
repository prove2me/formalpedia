-- Prove2me | Definitions.Def_CertRandQROM_queryNorm
-- name    : CertRandQROM_queryNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:51.288719+00:00
-- url     : https://prove2.me/theorems/af3a798f-e479-4e44-b06c-8499b5f08e74
-- title:
--   Query norm $\tilde w^j_u(h)$ and total query norm $\tilde w_u(h)$ (Definition 3.2)
-- statement:
--   For a query algorithm $\mathcal A$ with oracle $h$ and an input $u$ of the oracle, the **query norm** that $\mathcal A^h$ gives to $u$ on the $j$-th query ($j\in[Q]$) is
--
--   $$
--   \tilde w^j_u(h)=\big\|\Pi_u|\psi^h_{j-1}\rangle\big\|_2,\qquad \Pi_u=|u\rangle\langle u|_{R_Q}\otimes I_{R_A},
--   $$
--
--   that is, $\big(\sum_{a\in W}|\psi^h_{j-1}(u,a)|^2\big)^{1/2}$. The **total query norm** is $\tilde w_u(h)=\sum_{j\in[Q]}\tilde w^j_u(h)$.
--
--   The query norm is the square root of the usual query weight; the swapping lemma, local stability and the reprogramming lemma are all stated in terms of it.
--
--   **Formalization Note** The query index is 0-based: `queryNorm A h j u` is $\|\Pi_u|\psi^h_j\rangle\|_2$, i.e. the paper's $\tilde w^{j+1}_u(h)$, and `totalQueryNorm A h u` sums `queryNorm A h j u` over $j<Q$.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Definition 3.2 (Query Norm), p.15 (PDF p.17)

import Mathlib
import Definitions.Def_CertRandQROM_QueryAlg

namespace CertRandQROM

/-- **Query norm** (Definition 3.2, p.15, of Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal,
*Unconditional Certified Randomness without Structure*, arXiv:2608.31112, sha256 b75095a2…):
`queryNorm A h j u = ‖Π_u |ψ_j^h⟩‖₂ = (Σ_{a ∈ W} |ψ_j^h(u, a)|²)^{1/2}`, where
`Π_u = |u⟩⟨u|_{R_Q} ⊗ I_{R_A}`.

**Formalization Note** The query index is **0-based**: the paper's `w̃^{j}_{u}(H)`, the norm
given to `u` on the `j`-th query (`j ∈ [Q]`), uses `|ψ_{j−1}^H⟩`, so it is
`queryNorm A H (j − 1) u` here. This is the norm, not the squared query weight. -/
noncomputable def queryNorm {U W O : Type} [Fintype U] [DecidableEq U] [Fintype W]
    [DecidableEq W] [Fintype O] {Q : ℕ} (A : QueryAlg U W O Q) (h : U → Bool) (j : ℕ) (u : U) :
    ℝ :=
  Real.sqrt (∑ a : W, ‖A.state h j (u, a)‖ ^ 2)

/-- **Total query norm** (Definition 3.2, p.15): `w̃_u(H) = Σ_{j ∈ [Q]} w̃^j_u(H)`, i.e.
`Σ_{j < Q} queryNorm A h j u` with the 0-based index. -/
noncomputable def totalQueryNorm {U W O : Type} [Fintype U] [DecidableEq U] [Fintype W]
    [DecidableEq W] [Fintype O] {Q : ℕ} (A : QueryAlg U W O Q) (h : U → Bool) (u : U) : ℝ :=
  ∑ j ∈ Finset.range Q, queryNorm A h j u

end CertRandQROM


