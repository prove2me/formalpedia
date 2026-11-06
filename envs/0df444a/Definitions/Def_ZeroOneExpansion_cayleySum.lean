-- Prove2me | Definitions.Def_ZeroOneExpansion_cayleySum
-- name    : ZeroOneExpansion_cayleySum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:27.418659+00:00
-- url     : https://prove2.me/theorems/c3416fd6-e8c6-467e-9fce-0ba31072be2c
-- title:
--   Cayley sum $A*B=\operatorname{conv}((A\times\{0\})\cup(B\times\{1\}))$
-- statement:
--   For point sets $A,B\subseteq\mathbb R^d$, the **Cayley sum** is
--   $$A*B=\operatorname{conv}\big((A\times\{0\})\cup(B\times\{1\})\big)\subseteq\mathbb R^{d+1}.$$
--   The sets $A\times\{0\}$ and $B\times\{1\}$ are its **lower** and **upper layers**.
--
--   **Formalization Note** $\mathbb R^d\times\mathbb R$ is $\mathbb R^{d+1}$ with the layer coordinate last. The paper takes $A,B$ finite and nonempty; the theorems that use the Cayley sum assume this.
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), §2.3, p.4, "Cayley sum"

import Mathlib

set_option autoImplicit false

namespace ZeroOneExpansion

/-- The point `(x, t) ∈ ℝ^d × ℝ = ℝ^{d+1}`: the coordinates of `x` followed by `t` as the last
coordinate. -/
def withLast {d : ℕ} (x : Fin d → ℝ) (t : ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) x t

/-- The **Cayley sum** `A ∗ B := conv((A × {0}) ∪ (B × {1}))` (arXiv:2608.01870, §2.3, p.4); the
sets `A × {0}` and `B × {1}` are its lower and upper layers.

**Formalization Note** `ℝ^d × ℝ` is `Fin (d + 1) → ℝ`, with the layer coordinate last
(`withLast`). The paper defines `A ∗ B` for finite nonempty `A, B`; the definition is written for
all sets and the statements that use it assume finiteness and nonemptiness. -/
def cayleySum {d : ℕ} (A B : Set (Fin d → ℝ)) : Set (Fin (d + 1) → ℝ) :=
  convexHull ℝ ((fun a => withLast a 0) '' A ∪ (fun b => withLast b 1) '' B)

end ZeroOneExpansion


