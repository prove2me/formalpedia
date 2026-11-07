-- Prove2me | Definitions.Def_SplayDynOpt_extRank
-- name    : SplayDynOpt_extRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:56:41.506602+00:00
-- url     : https://prove2.me/theorems/e3ba62d8-26ef-4da7-8f1f-999b5998e6dc
-- title:
--   Ranks of the external nodes: depths in $T^*$ with null nodes
-- statement:
--   Add to a tree $T$ on $[n]$ the **null nodes** $\bot_0,\dots,\bot_n$, where $\bot_i$ lies between the keys $i$ and $i+1$ in symmetric order, $\bot_0$ left of $1$ and $\bot_n$ right of $n$. The keys and the null nodes together are the **external nodes** of the splay tree; they alternate in symmetric order,
--   $$
--   \bot_0,\ 1,\ \bot_1,\ 2,\ \dots,\ n,\ \bot_n ,
--   $$
--   and are numbered by positions $0,\dots,2n$, with $\bot_i$ at position $2i$ and the key $v$ at position $2v-1$. The **rank** of an external node is its depth in $T$ with the null nodes added: a key has the depth of its node, and $\bot_i$ has the depth of the nil leaf at its place, which is one more than the depth of its parent.
--
--   The ranks with respect to the normal-form tree $T^*$ drive the whole analysis: they define heavy edges, heavy paths and bends of the splay tree.
--
--   **Formalization Note** `extRanks` lists the ranks in symmetric order, and `extRank T e` reads position $e$. A position outside $0,\dots,2n$ gets the value $0$; such positions never occur in the statements.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), §5, p.14 (null nodes); §5.2.1, p.15 (rank)

import Mathlib

set_option autoImplicit false

namespace SplayDynOpt

open BinaryTree

/-- The depths of the **external nodes** of `t` in symmetric order: null nodes and keys
alternate, `⊥₀, key₁, ⊥₁, key₂, …, key_N, ⊥_N`, where `⊥ᵢ` is the nil leaf between the `i`-th and
`(i+1)`-st key. A key has the depth of its node; a null node `⊥ᵢ` has the depth of the nil leaf,
one more than its parent's depth (`0` for the empty tree). -/
def extRanks : BinaryTree ℕ → List ℕ
  | nil => [0]
  | node _ l r => (extRanks l).map (· + 1) ++ [0] ++ (extRanks r).map (· + 1)

/-- The **rank** of external position `e` with respect to the tree `T`: its depth in `T` with null
nodes added. For a BST `T` on `[n]` the positions are `e = 0, …, 2n`, with `e = 2i` the null node
`⊥ᵢ` (between keys `i` and `i+1`) and `e = 2v − 1` the key `v`.

Chmel et al., *Splay trees are almost dynamically optimal*, arXiv:2607.18498 (version of
2026-11-02, sha256 6881e83c…), §5, p.14: "we add n + 1 null nodes ⊥0, ⊥1, · · · ⊥n, where ⊥i falls in
between i and i + 1 in the symmetric order […] Similarly as for T, we add the null nodes ⊥i to the
optimal tree T OPT"; §5.2.1, p.15: "For every external node v of T, we define its rank as its
depth in the nearly optimal tree T∗, i.e., rank(v) = depthT∗(v)."

**Formalization Note.** Positions outside `0, …, 2n` get the junk value `0`; they never occur. -/
def extRank (T : BinaryTree ℕ) (e : ℕ) : ℕ :=
  (extRanks T).getD e 0

end SplayDynOpt


