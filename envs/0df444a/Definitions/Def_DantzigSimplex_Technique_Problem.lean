-- Prove2me | Definitions.Def_DantzigSimplex_Technique_Problem
-- name    : DantzigSimplex_Technique_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:40:53.795369+00:00
-- url     : https://prove2.me/theorems/b2228f77-6cc9-40ac-8d8a-acb7a5c93f64
-- title:
--   The equality-form maximization problem (4)–(6)
-- statement:
--   Let $P_0\in\mathbb R^m$ be a right-hand side, $P_j\in\mathbb R^m$ the columns indexed by $j=1,\ldots,n$, and $c_j\in\mathbb R$ their objective coefficients. For weights $\lambda\in\mathbb R^n$, define
--
--   $$
--   P(\lambda)=\sum_{j=1}^n\lambda_jP_j,\qquad z(\lambda)=\sum_{j=1}^n\lambda_jc_j.
--   $$
--
--   A feasible solution has every $\lambda_j\ge0$ and $P(\lambda)=P_0$. It is maximum feasible if its objective is at least the objective of every feasible solution. The problem is unbounded above when, for every real $M$, some feasible solution has objective greater than $M$.
--
--   These definitions state the common linear program independently of the simplex procedure and use pointwise optimality rather than an extended-real supremum. Indices in Lean start at zero, corresponding to the paper's $P_1,\ldots,P_n$.
-- source:
--   Dantzig, Maximization of a Linear Function of Variables Subject to Linear Inequalities, in Koopmans (ed.), Activity Analysis of Production and Allocation, Wiley 1951, Ch. XXI, p. 340, Eqs. (4)–(6)

import Mathlib

namespace DantzigSimplex.Technique

/-- Dantzig's equality-form maximization problem (4)--(6). -/
structure Problem (m n : ℕ) where
  col : Fin n → Fin m → ℝ
  rhs : Fin m → ℝ
  cost : Fin n → ℝ

def Problem.combine {m n : ℕ} (p : Problem m n) (w : Fin n → ℝ) : Fin m → ℝ :=
  fun a => ∑ j, w j * p.col j a

def Problem.objective {m n : ℕ} (p : Problem m n) (w : Fin n → ℝ) : ℝ :=
  ∑ j, w j * p.cost j

def Problem.Feasible {m n : ℕ} (p : Problem m n) (w : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ w j) ∧ p.combine w = p.rhs

def Problem.MaximumFeasible {m n : ℕ} (p : Problem m n) (w : Fin n → ℝ) : Prop :=
  p.Feasible w ∧ ∀ v, p.Feasible v → p.objective v ≤ p.objective w

def Problem.Unbounded {m n : ℕ} (p : Problem m n) : Prop :=
  ∀ M : ℝ, ∃ w, p.Feasible w ∧ M < p.objective w

end DantzigSimplex.Technique


