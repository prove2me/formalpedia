-- Prove2me | Definitions.Def_OracleStateHSP_queryOp
-- name    : OracleStateHSP_queryOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:16.27475+00:00
-- url     : https://prove2.me/theorems/c2936592-425d-4b27-982b-96fa0051c4ab
-- title:
--   Query operator $\tilde O = I_S \oplus (k(O) \otimes I_W)$
-- statement:
--   Let $\mathcal H_S$ be the query register, $W$ a finite-dimensional workspace and $S$ a finite-dimensional space, and let $\mathcal H = S \oplus (\mathcal H_S \otimes W)$. A query of kind $k$ to the oracle $O$ acts on $\mathcal H$ as
--   $$
--   \tilde O = I_S \oplus \bigl(k(O) \otimes I_W\bigr),
--   $$
--   where $k(O)$ is $O$, $O^\dagger$, $O^*$ or $O^T$. For $k$ forward and inverse this is the forward query $I_S \oplus (O \otimes I_W)$ and the inverse query $I_S \oplus (O^\dagger \otimes I_W)$ of Definition 4.1.
--
--   The direct sum implicitly allows controlled queries: implementing $I \oplus O$ on $K \oplus K$ is controlled-$O$ on $\mathbb C^2 \otimes K$.
--
--   **Formalization Note** The direct sum is the disjoint-union basis $S \sqcup (Q \times W)$ and $\tilde O$ is a block-diagonal matrix.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 4.1, p.35

import Mathlib
import Definitions.Def_OracleStateHSP_QueryKind

namespace OracleStateHSP

/-- The query operator `Õ = I_S ⊕ (k(O) ⊗ I_W)` on `H = S ⊕ (H_S ⊗ W)` (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656,
Definition 4.1, p.35): the forward query is `I_S ⊕ (O ⊗ I_W)` and the inverse query
`I_S ⊕ (O† ⊗ I_W)`; the conjugate and transpose queries of Theorem 4.10 (p.40) are
`I_S ⊕ (O^* ⊗ I_W)` and `I_S ⊕ (O^T ⊗ I_W)`.

**Formalization Note.** The direct sum `S ⊕ (H_S ⊗ W)` is the index type `S ⊕ (Q × W)` and the
operator is the block-diagonal matrix `fromBlocks 1 0 0 (k(O) ⊗ₖ 1)`. As the page says, this direct
sum "implicitly allows the implementation of controlled-O" (`I ⊕ O` on `K ⊕ K` is controlled-`O`
on `ℂ² ⊗ K`): controlled queries need no separate constructor. -/
def queryOp {Q S W : Type*} [DecidableEq S] [DecidableEq W] (k : QueryKind) (O : Matrix Q Q ℂ) :
    Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ :=
  Matrix.fromBlocks 1 0 0 (Matrix.kronecker (k.apply O) (1 : Matrix W W ℂ))

end OracleStateHSP


