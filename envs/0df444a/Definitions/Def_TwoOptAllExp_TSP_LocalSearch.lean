-- Prove2me | Definitions.Def_TwoOptAllExp_TSP_LocalSearch
-- name    : TwoOptAllExp_TSP_LocalSearch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:55:56.564196+00:00
-- url     : https://prove2.me/theorems/d1ef3f9d-de3a-4aff-98ca-0b6c91076893
-- title:
--   Local-search problems, improving sequences and the all-exp property
-- statement:
--   A **local-search problem** consists of a set of instances, an encoding size for each instance and, for every instance $I$, a finite set $F(I)$ of feasible solutions, an integer objective $f(\cdot,I)$ and a neighborhood $N(s,I)\subseteq F(I)$ of every solution $s$. The problem is one of minimization or of maximization.
--
--   The **gain** of a move from $s$ to $s'$ is $f(s)-f(s')$ for a minimization problem and $f(s')-f(s)$ for a maximization problem. A move to a neighbor is **improving** if its gain is positive. A sequence $s_0,s_1,\dots,s_\ell$ is an **improving sequence of length $\ell$** if every move $s_{j-1}\to s_j$ is an improving move to a neighbor. A solution is a **local optimum** if no move to a neighbor has positive gain, and an improving sequence is **maximal** if $s_\ell$ is a local optimum.
--
--   The problem has the **all-exp property** if there are constants $\varepsilon>0$ and $C>0$ such that for every $m$ there are an instance $I$ of size at least $m$ and a solution $s$ of $I$ from which a maximal improving sequence exists and every maximal improving sequence has length at least
--   $$C\cdot 2^{\mathrm{size}(I)^{\varepsilon}}.$$
--
--   These notions are shared by every problem of the paper, the TSP with $k$-opt as well as Maximum Constraint Assignment.
--
--   **Formalization Note** A run of the standard local-search algorithm under a pivot rule is a maximal improving sequence, and every maximal improving sequence is the run of some pivot rule, so "for all pivot rules" is the quantifier over maximal improving sequences. For a given size there are finitely many pairs, so "infinitely many pairs" says that the sizes are unbounded. A sequence is a function on $\mathbb N$ of which only the values at $0,\dots,\ell$ matter. The requirement of the paper that solutions have polynomial size plays no role in Definition 4 and is not recorded.
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, §2.1 and Definition 4, pp. 6–7

import Mathlib

namespace TwoOptAllExp.TSP

/-- The data of a local-search problem at one fixed instance (§2.1, pp. 6–7): a finite set of
feasible solutions, an integer objective, a neighborhood of each solution, and the direction of
optimization. -/
structure SearchSpace where
  /-- The feasible solutions `F_P(I)`. -/
  Sol : Type
  /-- `F_P(I)` is finite. -/
  sol_finite : Finite Sol
  /-- The objective `f_P(·, I)`, an integer. -/
  obj : Sol → ℤ
  /-- The neighborhood `N_P(s, I) ⊆ F_P(I)`. -/
  Nbr : Sol → Set Sol
  /-- `true` for a minimization problem, `false` for a maximization problem. -/
  minimize : Bool

namespace SearchSpace

variable (S : SearchSpace)

/-- The gain of a move from `s` to `s'` (p. 7): `f(s) - f(s')` for a minimization problem and
`f(s') - f(s)` for a maximization problem. -/
def gain (s s' : S.Sol) : ℤ :=
  if S.minimize then S.obj s - S.obj s' else S.obj s' - S.obj s

/-- A move from `s` to a neighbor `s'` with positive gain (p. 7). -/
def IsImprovingMove (s s' : S.Sol) : Prop :=
  s' ∈ S.Nbr s ∧ 0 < S.gain s s'

/-- `t 0, t 1, …, t ℓ` is an improving sequence of length `ℓ` (p. 7). The values `t j`, `j > ℓ`,
play no role. -/
def IsImprovingSeq (ℓ : ℕ) (t : ℕ → S.Sol) : Prop :=
  ∀ j < ℓ, S.IsImprovingMove (t j) (t (j + 1))

/-- `s` is a local optimum (pp. 6–7): no neighbor has a strictly better objective value. -/
def IsLocalOpt (s : S.Sol) : Prop :=
  ∀ s' ∈ S.Nbr s, S.gain s s' ≤ 0

/-- An improving sequence of length `ℓ` is maximal if `t ℓ` is a local optimum (p. 7). -/
def IsMaximalSeq (ℓ : ℕ) (t : ℕ → S.Sol) : Prop :=
  S.IsImprovingSeq ℓ t ∧ S.IsLocalOpt (t ℓ)

end SearchSpace

/-- A local-search problem (§2.1, p. 6): a set of instances `D_P`, an encoding size of every
instance, and the search space `(F_P(I), f_P, N_P)` of every instance. -/
structure LocalSearchProblem where
  /-- The instances `D_P`. -/
  Inst : Type
  /-- The size of an instance. -/
  size : Inst → ℕ
  /-- The search space of an instance. -/
  space : Inst → SearchSpace

/-- **Definition 4 (all-exp property)**, p. 7. There are `ε > 0` and `C > 0` such that instances
of unbounded size carry an initial solution from which every run of the standard local-search
algorithm, i.e. every maximal improving sequence, has length at least `C · 2^(size^ε)`. A run of
the algorithm under a pivot rule is a maximal improving sequence, and every maximal improving
sequence is the run of some pivot rule (p. 7, the transition-graph paragraph). There are finitely
many pairs of each size, so "infinitely many pairs" says that the sizes are unbounded. The clause
`∃ ℓ t, …` records that the algorithm terminates, so that the universal clause is not vacuous. -/
def HasAllExpProperty (P : LocalSearchProblem) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
    ∃ (I : P.Inst) (s : (P.space I).Sol), m ≤ P.size I ∧
      (∃ (ℓ : ℕ) (t : ℕ → (P.space I).Sol), t 0 = s ∧ (P.space I).IsMaximalSeq ℓ t) ∧
      ∀ (ℓ : ℕ) (t : ℕ → (P.space I).Sol), t 0 = s → (P.space I).IsMaximalSeq ℓ t →
        C * (2 : ℝ) ^ ((P.size I : ℝ) ^ ε) ≤ (ℓ : ℝ)

end TwoOptAllExp.TSP


