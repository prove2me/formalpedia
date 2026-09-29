-- Prove2me | Definitions.Def_LovaszSchrijver_OddHole_DeletionContraction
-- name    : LovaszSchrijver_OddHole_DeletionContraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:46:07.792122+00:00
-- url     : https://prove2.me/theorems/6dcc1eb3-5a29-4e65-9e08-ba56a542a116
-- title:
--   Deletion and contraction of a node in an inequality aᵀx ≤ b (Section 2.b)
-- statement:
--   Let $a^{\mathsf T} x \le b$ be an inequality on $\mathbb{R}^V$ and $v \in V$. Lovász and Schrijver (p. 177) call the inequalities $a_{V-v}^{\mathsf T} x \le b$ and $a_{V-\Gamma(v)-v}^{\mathsf T} x \le b - a_v$ the **deletion** and **contraction** of node $v$, where $a_W$ is the restriction of $a$ to $W \subseteq V$ and $\Gamma(v)$ is the set of neighbours of $v$.
--
--   Here both are coefficient vectors on the whole node set $V$:
--
--   1. the deletion of $v$ is $a$ with the coefficient $a_v$ replaced by $0$; the right-hand side stays $b$;
--   2. the contraction of $v$ is $a$ with the coefficients of $v$ and of every neighbour of $v$ replaced by $0$; the right-hand side is $b - a_v$.
--
--   **Formalization Note** The paper states the deleted and contracted inequalities on the subgraphs $G - v$ and $G - \Gamma(v) - v$. A zero coefficient makes the variable irrelevant, so the zeroed vector on $G$ carries the same inequality; the definition works on the same graph $G$, which avoids subgraphs that have isolated nodes. The right-hand side of the contraction ($b - a_v$) is written out in each statement that uses it.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 177, Section 2.b

import Mathlib

namespace LovaszSchrijver.OddHole

/-- Deletion of the node `v` (p. 177): the coefficient vector `a` with `a_v` set to `0`.
The right-hand side `b` is unchanged. -/
def deletion {V : Type} [DecidableEq V] (a : V → ℝ) (v : V) : V → ℝ :=
  Function.update a v 0

/-- Contraction of the node `v` (p. 177): the coefficient vector `a` with the coefficients
of `v` and of every neighbour of `v` set to `0`. The right-hand side becomes `b - a_v`. -/
def contraction {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V → ℝ) (v : V) : V → ℝ :=
  fun w => if w = v ∨ G.Adj v w then 0 else a w

end LovaszSchrijver.OddHole


