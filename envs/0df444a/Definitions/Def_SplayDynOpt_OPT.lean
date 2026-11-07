-- Prove2me | Definitions.Def_SplayDynOpt_OPT
-- name    : SplayDynOpt_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:23.169602+00:00
-- url     : https://prove2.me/theorems/66ba4186-2616-4f97-bead-e15327b753c8
-- title:
--   Executions in the root BST model and the optimal cost $\mathrm{OPT}(n,X)$
-- statement:
--   Fix $n$ and an access sequence $X=x_1,\dots,x_m$. An **execution** in the root BST model consists of trees $T_0,T_1,\dots,T_\ell$ and access times $t_1\le\dots\le t_m\le\ell$ such that:
--
--   1. every $T_i$ with $0\le i\le\ell$ is a binary search tree on $[n]$;
--   2. every $T_i$ with $1\le i\le\ell$ is obtained from $T_{i-1}$ by one rotation, at any depth;
--   3. the root of $T_{t_j}$ is $x_j$ for every $j$.
--
--   Its cost is $m+\ell$: one for each access and one for each rotation. The **optimal cost** is
--   $$
--   \mathrm{OPT}(n,X)=\min\{\,m+\ell : (T_0,\dots,T_\ell;\,t_1,\dots,t_m)\text{ is an execution of }X\,\},
--   $$
--   which is the paper's $\operatorname{cost}(T^{\mathrm{OPT}}_X,X)$. The initial tree $T_0$ is free, since the paper takes the initial configuration of the optimal tree to be the optimal one.
--
--   This is the benchmark in the main theorem.
--
--   **Formalization Note** Access times are non-decreasing rather than strictly increasing, so a repeated access to the root costs $1$ and no rotation, as in the model. `tree` and `time` are functions on $\mathbb N$ whose values beyond $\ell$ and $m$ are ignored. The minimum is `sInf` of a set of natural numbers. For $X$ over $[n]$ that set is non-empty, because any key can be rotated to the root, so the minimum is attained; this is proved in the mission's verification file.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), §2.1, pp.3–4; App. B, p.59 (Root BST)

import Mathlib
import Definitions.Def_SplayDynOpt_rotateAt

set_option autoImplicit false

namespace SplayDynOpt

open BinaryTree

/-- An **execution of a dynamic BST in the root BST model**: trees `T₀, T₁, …, T_ℓ` (`len = ℓ`,
`tree i = Tᵢ`; values at `i > ℓ` are ignored) and access times `time j` for the accesses
`j = 0, …, m − 1` (values at `j ≥ m` are ignored). -/
structure Execution where
  /-- The number `ℓ` of rotations. -/
  len : ℕ
  /-- `tree i` is the tree `Tᵢ` after `i` rotations, `0 ≤ i ≤ ℓ`. -/
  tree : ℕ → BinaryTree ℕ
  /-- `time j` is the index `i` of the tree at which access `j` (0-based) is served. -/
  time : ℕ → ℕ

/-- `E` is a valid execution of the access sequence `X = x₁, …, x_m` on keys `[n]` in the
**root BST model**:
1. every `Tᵢ` (`0 ≤ i ≤ ℓ`) is a BST on `[n]`;
2. every `Tᵢ` (`1 ≤ i ≤ ℓ`) is obtained from `Tᵢ₋₁` by one rotation (at any depth);
3. the access times are non-decreasing and at most `ℓ`;
4. the key accessed at step `j` is the root of the tree at its access time.

Chmel et al., *Splay trees are almost dynamically optimal*, arXiv:2607.18498 (version of
2026-11-02, sha256 6881e83c…), §2.1, p.3: "Upon each access, we can repeatedly perform the
following operation on the nodes of the tree: rotate(x). […] After each access, the node being
accessed must be in the root. The cost of an access is 1 plus the number of rotations performed";
App. B, p.59: "Root BST (used in this work). For every access, the accessed element must be the
root of T, and the cost of the access is 1. In addition, before each access, the tree can perform
any number of rotations, and each rotation costs 1."

**Formalization Note.** Times are non-decreasing (not strictly increasing), so a repeated access
to the root costs `1` and no rotation, as in the model. The initial tree `T₀` is free (p.4: "the
initial configuration for T^OPT is assumed to be the optimal one"). The cost of `E` is
`m + ℓ` (one per access plus one per rotation). -/
def IsExecution (n : ℕ) (X : List ℕ) (E : Execution) : Prop :=
  (∀ i ≤ E.len, IsBSTOn n (E.tree i)) ∧
  (∀ i, 1 ≤ i → i ≤ E.len → IsRotation (E.tree (i - 1)) (E.tree i)) ∧
  (∀ j < X.length, E.time j ≤ E.len) ∧
  (∀ j j', j ≤ j' → j' < X.length → E.time j ≤ E.time j') ∧
  (∀ j < X.length, root (E.tree (E.time j)) = X[j]?)

/-- **The optimal offline cost** `cost(T^OPT_X, X)`: the least cost `m + ℓ` of an execution of `X`
in the root BST model, minimizing over the initial tree and all rotations.

Chmel et al., §2.1, p.4: "For a fixed access sequence X = x1, . . . , xm, the optimal tree T^OPT_X
is a dynamic BST that, among all possible BSTs, incurs the smallest cost on the given access
sequence while knowing the whole sequence in advance."

**Formalization Note.** The minimum is `sInf` of a set of natural numbers; for `n ≥ 1` and
`X` over `[n]` the set is nonempty (any key can be rotated to the root), so the minimum is
attained. -/
noncomputable def OPT (n : ℕ) (X : List ℕ) : ℕ :=
  sInf {c | ∃ E : Execution, IsExecution n X E ∧ c = X.length + E.len}

end SplayDynOpt


