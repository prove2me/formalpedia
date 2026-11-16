-- Prove2me | Definitions.Def_NondualStable_Optimization_Supplement_LocalOracle
-- name    : NondualStable_Optimization_Supplement_LocalOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:34:54.027188+00:00
-- url     : https://prove2.me/theorems/6867702f-0ef8-4078-9c4a-b1415db138c8
-- title:
--   Arbitrary local oracle and causal adaptive query trees
-- statement:
--   Let $X\subseteq\mathbb R^d$ be the feasible set and $\mathcal C$ a class of real objectives. A local oracle has an arbitrary reply set $Y$ and replies $\mathcal O_f(x)\in Y$. Its sole information restriction is
--   $$
--   f=g\text{ on }B(x,r)\text{ for some }r>0\quad\Longrightarrow\quad\mathcal O_f(x)=\mathcal O_g(x),\qquad f,g\in\mathcal C.
--   $$
--   The neighborhood is an ambient open ball, including when $x$ is on the boundary of $X$. The coordinate sup metric defines the usual ambient topology. Replies need not be first-order pairs, finite strings, or computable objects.
--
--   A deterministic algorithm with budget $t$ is a decision tree: a leaf outputs any point of $X$; an internal node queries a point of $X$ and chooses its continuation as an arbitrary function of the reply. Each query reduces the remaining budget by one. Thus every path uses at most $t$ actual queries, and a leaf may occur earlier. The final point need not have been queried. Unrolling causal transcript rules yields precisely this representation; branches not reachable by any instance can be completed by a feasible immediate output. The execution function accesses the unknown objective only through the fixed oracle. These objects express the full information model used in Section 7 without a computational restriction.
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 12 / PDF p. 13, Section 7

import Mathlib
import Definitions.Def_NondualStable_Optimization_Geometry

namespace NondualStable.Optimization.Supplement

/-- Arbitrary local information, with an unrestricted reply type. The ball is ambient,
including at boundary queries; the sup metric on coordinates gives the usual topology. -/
structure LocalOracle {d : ℕ} (C : Set (Vec d → ℝ)) (Reply : Type*) where
  reply : C → Vec d → Reply
  locality : ∀ f g : C, ∀ x, (∃ r : ℝ, 0 < r ∧
    ∀ y ∈ Metric.ball x r, f.val y = g.val y) → reply f x = reply g x

/-- A causal decision tree with at most t queries, with no computation restrictions.
Unrolling history-dependent rules gives exactly these trees. Outputs need not be queried.
All nodes are feasible, including nodes not reached for a particular objective. -/
inductive QueryTree {d : ℕ} (X : Set (Vec d)) (Reply : Type*) : ℕ → Type _
  | stop {t : ℕ} (output : X) : QueryTree X Reply t
  | query {t : ℕ} (point : X) (next : Reply → QueryTree X Reply t) :
      QueryTree X Reply (t + 1)

/-- Execute only by applying the fixed oracle to the next query; the tree has no f input. -/
def QueryTree.run {d : ℕ} {X : Set (Vec d)} {Reply : Type*}
    {C : Set (Vec d → ℝ)} (O : LocalOracle C Reply) (f : C) :
    {t : ℕ} → QueryTree X Reply t → X
  | _, .stop x => x
  | _, .query x next => QueryTree.run O f (next (O.reply f x.val))

end NondualStable.Optimization.Supplement


