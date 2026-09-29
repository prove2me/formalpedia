-- Prove2me | Definitions.Def_MegiddoLP_FixedDim_QueryTree
-- name    : MegiddoLP_FixedDim_QueryTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:07:22.591974+00:00
-- url     : https://prove2.me/theorems/03763665-973d-4c9d-97dd-0d15aba0aa1e
-- title:
--   Adaptive hyperplane-query strategies in $\mathbb{R}^d$
-- statement:
--   Megiddo's multidimensional search problem concerns an unknown point $x^*\in\mathbb{R}^d$ and an **oracle** that, for any $a\in\mathbb{R}^d$ and any real $b$, tells whether $a^Tx^*<b$, $a^Tx^*=b$ or $a^Tx^*>b$, that is, the position of $x^*$ relative to the hyperplane $\{x: a^Tx=b\}$.
--
--   A **query strategy** with outputs in a set $\alpha$ is a finite ternary tree. Each leaf carries a fixed output in $\alpha$. Each inner node carries a hyperplane $(a,b)$ and three subtrees, one for each answer $<$, $=$, $>$. For a point $x$, the strategy is evaluated by starting at the root, asking at each inner node for the position of $x$ relative to its hyperplane and following the subtree of the answer, until a leaf is reached. The output $T(x)$ is the value at that leaf, and the **number of queries** $q_T(x)$ is the number of inner nodes on the path:
--
--   $$T(x)=\text{value at the leaf reached by }x,\qquad q_T(x)=\#\{\text{inner nodes on the path of }x\}.$$
--
--   The tree is built from the given data only, and the unknown point enters only through the oracle's answers. This models the paper's "$x^*$ which is not known to us" and "how many queries we need to address the oracle". Later queries may depend on earlier answers.
--
--   **Formalization Note** The oracle's answer is Lean's `compare (a ⬝ᵥ x) b : Ordering`, with `lt`, `eq`, `gt` for $<$, $=$, $>$. Points are `Fin d → ℝ`.
-- source:
--   Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, J. ACM 31(1) (1984) 114–127, §3.1, p. 117 and §3.2, p. 118 (the oracle and the counting of queries)

import Mathlib

/-!
Hyperplane-query decision trees (Megiddo, J. ACM 31 (1984), §3.1–§3.2, pp. 117–118).

There is an unknown point `x* ∈ ℝ^d` and an oracle that, for any `a ∈ ℝ^d` and `b ∈ ℝ`,
tells whether `aᵀx* < b`, `aᵀx* = b` or `aᵀx* > b`. A search strategy that addresses the
oracle adaptively is a ternary decision tree: each inner node is a hyperplane query
`(a, b)` with one subtree per answer, and each leaf carries a fixed output value. The tree
is built from the data only; the unknown point enters only through `eval`.
-/

namespace MegiddoLP.FixedDim

/-- An adaptive strategy of hyperplane queries in `ℝ^d` with outputs in `α`.
`query a b onLt onEq onGt` asks the oracle for the position of the unknown point `x`
relative to the hyperplane `{y | a ⬝ᵥ y = b}` and continues with `onLt`, `onEq` or `onGt`
according as `a ⬝ᵥ x < b`, `a ⬝ᵥ x = b` or `a ⬝ᵥ x > b`. -/
inductive QTree (d : ℕ) (α : Type) : Type
  | leaf (out : α)
  | query (a : Fin d → ℝ) (b : ℝ) (onLt onEq onGt : QTree d α)

namespace QTree

variable {d : ℕ} {α : Type}

/-- The output of the strategy when the unknown point is `x`: follow the oracle's answers
`compare (a ⬝ᵥ x) b` from the root to a leaf. -/
noncomputable def eval : QTree d α → (Fin d → ℝ) → α
  | leaf out, _ => out
  | query a b onLt onEq onGt, x =>
    match compare (a ⬝ᵥ x) b with
    | .lt => onLt.eval x
    | .eq => onEq.eval x
    | .gt => onGt.eval x

/-- The number of oracle queries the strategy makes when the unknown point is `x`: the
number of query nodes on the root-to-leaf path followed by `x`. -/
noncomputable def numQueries : QTree d α → (Fin d → ℝ) → ℕ
  | leaf _, _ => 0
  | query a b onLt onEq onGt, x =>
    match compare (a ⬝ᵥ x) b with
    | .lt => onLt.numQueries x + 1
    | .eq => onEq.numQueries x + 1
    | .gt => onGt.numQueries x + 1

end QTree

end MegiddoLP.FixedDim


