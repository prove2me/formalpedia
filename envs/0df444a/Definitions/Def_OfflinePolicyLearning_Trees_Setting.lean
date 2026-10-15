-- Prove2me | Definitions.Def_OfflinePolicyLearning_Trees_Setting
-- name    : OfflinePolicyLearning_Trees_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:36:36.951634+00:00
-- url     : https://prove2.me/theorems/035174ba-2839-4aee-bb53-bd5f271681ab
-- title:
--   §6.1, pp. 27–28 — depth-L decision trees on ℝ^p with d actions and the policy class Π_L
-- statement:
--   Features are points $x\in\mathbb R^p$ with components $x(1),\dots,x(p)$, and there are $d$ actions. A **depth-$L$ decision tree** ($L\ge1$) has $L$ layers in total: the first $L-1$ layers consist of branch nodes and the $L$-th layer of leaf nodes, so it has $2^{L-1}-1$ branch nodes and $2^{L-1}$ leaves; a depth-1 tree is a single leaf. Each branch node carries a split variable $i\in\{1,\dots,p\}$ and a threshold $b\in\mathbb R$; each leaf carries an action label (different leaves may carry the same action).
--
--   A tree maps $x$ to an action by walking from the root: at a branch node splitting on $x(i)$ with threshold $b$,
--   $$\text{go to the left child if } x(i)<b,\qquad\text{to the right child if } x(i)\ge b,$$
--   and output the label of the leaf reached. $\Pi_L$ denotes the set of policies $\mathbb R^p\to\{1,\dots,d\}$ computed by depth-$L$ trees.
--
--   This is the policy class whose Hamming covering numbers are bounded in Lemma 4 of the paper.
--
--   **Formalization Note** Trees are an inductive type `DTree p d L` indexed by depth: `leaf a : DTree p d 1` and `node j b l r : DTree p d (L+1)` for subtrees `l r : DTree p d L`; `DTree p d 0` is empty. Split variables are `Fin p`, actions `Fin d` (0-based). The feature space is all of $\mathbb R^p$; the paper's $\mathcal X$ is a bounded subset of $\mathbb R^p$, and a covering bound over $\mathbb R^p$ implies the same bound over any $\mathcal X\subseteq\mathbb R^p$, since the supremum in $N_H$ then ranges over fewer point sets.
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, pp. 27–28, §6 and §6.1 (Decision Trees), Figure 1; §6.2 p. 28 (T_B = 2^{L−1} − 1, T_L = 2^{L−1}); App. G item 1, p. 69

import Mathlib

namespace OfflinePolicyLearning.Trees

/-- Section 6.1: a depth-`L` decision tree on features in `ℝ^p` with actions `Fin d`. A depth-`L`
tree has `L` layers: `L - 1` layers of branch nodes and one layer of leaves; depth 1 is a single
leaf (App. G). A branch node carries a split variable `j : Fin p` and a threshold `b : ℝ`. -/
inductive DTree (p d : ℕ) : ℕ → Type
  | leaf (a : Fin d) : DTree p d 1
  | node {L : ℕ} (j : Fin p) (b : ℝ) (l r : DTree p d L) : DTree p d (L + 1)

/-- Section 6.1: the action a tree assigns to a feature `x`; at a branch node splitting on
`x(j)` with threshold `b`, the left child is followed if `x(j) < b`, the right one otherwise. -/
noncomputable def DTree.eval {p d : ℕ} : {L : ℕ} → DTree p d L → (Fin p → ℝ) → Fin d
  | _, .leaf a, _ => a
  | _, .node j b l r, x => if x j < b then l.eval x else r.eval x

/-- Section 6.1: `Π_L`, the class of policies computed by depth-`L` trees. -/
def treePolicies (p d L : ℕ) : Set ((Fin p → ℝ) → Fin d) :=
  {π | ∃ T : DTree p d L, T.eval = π}

end OfflinePolicyLearning.Trees


