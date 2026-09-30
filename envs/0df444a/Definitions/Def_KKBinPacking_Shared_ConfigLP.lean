-- Prove2me | Definitions.Def_KKBinPacking_Shared_ConfigLP
-- name    : KKBinPacking_Shared_ConfigLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:17:18.225279+00:00
-- url     : https://prove2.me/theorems/11db9da0-e403-4d69-9bd6-67ac060ce89d
-- title:
--   Configurations, the fractional bin-packing LP (I), $LIN(I)$ and basic feasible solutions
-- statement:
--   Let $I$ be an instance. A **piece type** is a size occurring in $I$; $b_t$ denotes the number of pieces of type $t$. A **configuration** is a nonempty multiset $c$ of piece types whose total size is at most $1$ (a type may occur in $c$ any number of times); $a_{tc}$ denotes the number of occurrences of type $t$ in $c$.
--
--   The **fractional bin-packing problem** is the linear program
--
--   $$
--   \text{(I)}\qquad \min\ \mathbf 1\cdot x \quad\text{subject to}\quad x \ge 0,\qquad \sum_{c} a_{tc}\,x_c \ \ge\ b_t\ \text{ for every type } t,
--   $$
--
--   with one variable $x_c$ per configuration. $LIN(I)$ denotes its optimal value. A **basic (extreme point) feasible solution** is a feasible $x$ that is not the midpoint of two distinct feasible solutions: if $x+y$ and $x-y$ are both feasible then $y = 0$.
--
--   This linear program is the Gilmore–Gomory relaxation that all algorithms of the paper round.
--
--   **Formalization Note** A solution is a finitely supported function `x : Multiset ℝ →₀ ℝ` whose support consists of configurations. $LIN(I)$ is the real infimum of the costs of feasible solutions. For an instance this set is nonempty (put weight $b_t$ on the singleton configuration $\{t\}$, which fits because every size is $< 1$) and bounded below by $0$, so the infimum is the LP value and never the junk value of an empty or unbounded set. "Basic" is the extreme-point property stated by the paper ("basic (extreme point) feasible solution", p. 313). That $x$ then has at most $m(I)$ nonzero components is a consequence, not part of the definition.
--
--   It serves both missions of the series: `01-linear-grouping` (p. 313, §3 and the proof of Lemma 2; LIN(I) and basic solutions are rounded by ALGORITHM 1, p. 316) and `02-geometric-grouping` (p. 313, §3; LIN(I) is rounded in every iteration of ALGORITHM 2, p. 316). It is reviewed once for both.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 313, §3 (configuration, linear program (I), LIN(I)); p. 313, proof of Lemma 2 (basic (extreme point) feasible solution)

import Mathlib

namespace KKBinPacking.Shared

/-- A configuration of `I` (p. 313): a nonempty multiset of piece types (sizes occurring in
`I`) that fits in one bin. A type may occur in a configuration more often than in `I`. -/
def IsConfiguration (I : Multiset ℝ) (c : Multiset ℝ) : Prop :=
  c ≠ 0 ∧ (∀ t ∈ c, t ∈ I) ∧ c.sum ≤ 1

/-- Feasibility for the fractional bin-packing linear program (I) of p. 313: `x` assigns a
nonnegative weight to finitely many configurations, and for every piece type `t` of `I` the
number `b_t` of pieces of type `t` is at most `∑_c x_c · a_{t c}`, where `a_{t c}` is the
number of pieces of type `t` in configuration `c` (`Ax ≥ b`, `x ≥ 0`). -/
def IsLPFeasible (I : Multiset ℝ) (x : Multiset ℝ →₀ ℝ) : Prop :=
  (∀ c ∈ x.support, IsConfiguration I c) ∧ (∀ c, 0 ≤ x c) ∧
    ∀ t ∈ I.toFinset, (I.count t : ℝ) ≤ ∑ c ∈ x.support, x c * (c.count t : ℝ)

/-- The objective `1·x` of the linear program (I). -/
def lpCost (x : Multiset ℝ →₀ ℝ) : ℝ := ∑ c ∈ x.support, x c

/-- `LIN(I)`, the optimal value of the fractional bin-packing problem (p. 313). For an instance
the set is nonempty (one copy of the singleton configuration `{t}` per piece of type `t` is
feasible, since every size is `< 1`) and bounded below by `0`, so this infimum is the LP's
optimal value and never the junk value `sInf ∅`. -/
noncomputable def LIN (I : Multiset ℝ) : ℝ :=
  sInf {z : ℝ | ∃ x : Multiset ℝ →₀ ℝ, IsLPFeasible I x ∧ lpCost x = z}

/-- A basic (extreme point) feasible solution of (I) (p. 313): a feasible `x` that is not the
midpoint of two distinct feasible solutions, i.e. `x + y` and `x - y` feasible force `y = 0`. -/
def IsBasicFeasible (I : Multiset ℝ) (x : Multiset ℝ →₀ ℝ) : Prop :=
  IsLPFeasible I x ∧
    ∀ y : Multiset ℝ →₀ ℝ, IsLPFeasible I (x + y) → IsLPFeasible I (x - y) → y = 0

end KKBinPacking.Shared


