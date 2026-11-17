-- Prove2me | Definitions.Def_LosslessCond_Supplement_multiCost
-- name    : LosslessCond_Supplement_multiCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:24:59.1932+00:00
-- url     : https://prove2.me/theorems/d035066c-a51f-4d39-a621-6f0653fb366c
-- title:
--   Multiparty communication complexity $D_p(F)$ and of a product restriction
-- statement:
--   Let $F:X_1\times\cdots\times X_p\to Z$ be a total function and let $X'_i\subseteq X_i$ be original subsets of the players' input sets. The **communication complexity of the product restriction** $F|_{X'_1\times\cdots\times X'_p}$ is
--
--   $$
--   D_p\bigl(F|_{X'_1\times\cdots\times X'_p}\bigr)=\min\{\operatorname{depth}(P) : P(x)=F(x)\text{ for every } x \text{ with } x_i\in X'_i \text{ for all } i\},
--   $$
--
--   the minimum over deterministic number-in-hand protocols $P$ with outputs in $Z$. The **deterministic $p$-party communication complexity** $D_p(F)$ is the same quantity with $X'_i=X_i$ for all $i$.
--
--   A restriction selects an original subset of each player's input set: it neither combines players nor changes the required output.
--
--   **Formalization Note** The restriction is encoded as correctness on the product $\prod_i X'_i$ of a protocol defined on all inputs; this is the cost of the restricted function, since a protocol for the restriction extends to all inputs. An empty factor gives cost $0$. For finite nonempty input sets the minimum exists (the players can write their inputs in turn), so the infimum over $\mathbb N$ is never the junk value of an empty set.
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Appendix B, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_LosslessCond_Supplement_MultiProtocol

namespace LosslessCond

namespace Supplement

/-- The **communication complexity of a product restriction** `D_p(F|_{X′_1×⋯×X′_p})` (Mackenzie,
arXiv:2609.28691, held version sha256 ce75e6d4…, Appendix B, p.26, PDF p.27): the least depth of a
`p`-party number-in-hand protocol whose output equals `F x` on every input tuple `x` with
`x i ∈ S i` for all `i`.

**Formalization Note** The restriction `F|_{S_1×⋯×S_p}` is encoded as correctness on the product of
the `S i` of a protocol over all inputs, exactly as `DetCCHard.commCost` does for two parties. This
equals the cost of the restricted function: a protocol for the restriction extends to all inputs
(each player's message functions take arbitrary values off `S i`), and a protocol correct on the
product restricts to one for the restriction. An empty `S i` gives cost `0`. When every `X i` is
finite and nonempty the set of admissible depths is nonempty (the players write their inputs in
turn and the leaf outputs `F x`), so the infimum is a minimum, never the junk value of `sInf ∅`. -/
noncomputable def multiCost {p : ℕ} {X : Fin p → Type} {Z : Type} (F : (∀ i, X i) → Z)
    (S : ∀ i, Set (X i)) : ℕ :=
  sInf {n : ℕ | ∃ P : MultiProtocol X Z, P.depth ≤ n ∧
    ∀ x : (∀ i, X i), (∀ i, x i ∈ S i) → P.eval x = F x}

/-- The **deterministic `p`-party number-in-hand communication complexity** `D_p(F)` (Appendix B,
p.26): the minimum worst-case number of communicated bits of a protocol computing `F` on every
input tuple. -/
noncomputable def Dp {p : ℕ} {X : Fin p → Type} {Z : Type} (F : (∀ i, X i) → Z) : ℕ :=
  multiCost F (fun _ => Set.univ)

end Supplement

end LosslessCond


