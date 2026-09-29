-- Prove2me | Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt
-- name    : LocalSearchFL_CFL_IsCFLLocalOpt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:21:14.616671+00:00
-- url     : https://prove2.me/theorems/49d9ef28-f736-41ab-a4e3-f1bb95043717
-- title:
--   The add and drop-add neighbourhood (9) and local optimality for capacitated facility location
-- statement:
--   Fix a metric instance, capacities $u$ and facility costs $f$. Let $X$ be a CFL solution with multiset of facilities $S$ and client neighbourhoods $N_X(\cdot)$. The paper's neighbourhood of $S$ is
--
--   $$\mathcal B(S) = \{S + s' \mid s' \in F\} \cup \{S - T + l\cdot\{s'\} \mid s' \in F,\ T \subseteq S,\ l\cdot u_{s'} \ge |N_S(T)|\},$$
--
--   where $l \cdot \{s'\}$ denotes $l \ge 1$ new copies of $s'$.
--
--   1. A CFL solution $Y$ is an **add neighbour** of $X$ if the multiset of facilities of $Y$ is $S$ plus one new copy of some facility $s'$.
--   2. $Y$ is a **drop-add neighbour** of $X$ if there are a set $T$ of copies of $X$, a facility $s'$ and an integer $l \ge 1$ with $l\cdot u_{s'} \ge |N_X(T)|$ such that the multiset of facilities of $Y$ consists of the copies of $X$ outside $T$ together with $l$ copies of $s'$.
--   3. $X$ is **locally optimum** if $\mathrm{cost}(X) \le \mathrm{cost}(Y)$ for every CFL solution $Y$ that is an add neighbour or a drop-add neighbour of $X$.
--
--   In both kinds of neighbour the assignment of $Y$ is an arbitrary capacity-feasible one. Comparing with all of them is the same as comparing with the cost of the neighbouring multiset under its best assignment.
--
--   **Formalization Note** Every facility $s'$, every set $T$ of copies (including $T = \emptyset$ and all copies) and every $l \ge 1$ with $l u_{s'} \ge |N_X(T)|$ is allowed, as in (9); the algorithm's search procedure T-hunt is not part of the definition. Taking $T = \{s\}$, $s' = \mathrm{loc}(s)$, $l = 1$ makes every reassignment of the clients among the copies of $X$ a neighbour, so the assignment of a locally optimum $X$ is automatically a minimum-cost one.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 558, §5.1, eq. (9); p. 547, definition of locally optimum

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_CFLSol

namespace LocalSearchFL.CFL

variable {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ}

/-- `Y` is an **add neighbour** of `X` (first part of (9), §5.1 p. 558): the multiset of
facilities of `Y` is that of `X` plus a single new copy of some facility `s'`, i.e.
`Y = S + s'`. The assignment of `Y` is any capacity-feasible one. -/
def IsAddNbr (X Y : CFLSol Cl Fa u) : Prop :=
  ∃ s' : Fa, Y.facMultiset = X.facMultiset + {s'}

/-- `Y` is a **drop-add neighbour** of `X` (second part of (9), §5.1 p. 558): for some set
`T` of copies of `X`, some facility `s'` and some `l ≥ 1` with `l · u_{s'} ≥ |N_X(T)|`, the
multiset of facilities of `Y` is `S − T + l · {s'}`: the copies of `X` outside `T`, plus `l`
new copies of `s'`. The assignment of `Y` is any capacity-feasible one. -/
def IsDropAddNbr (X Y : CFLSol Cl Fa u) : Prop :=
  ∃ (T : Finset (Fin X.n)) (s' : Fa) (l : ℕ), 1 ≤ l ∧ (X.nbhdSet T).card ≤ l * u s' ∧
    Y.facMultiset = Multiset.map X.loc (Finset.univ \ T).val + Multiset.replicate l s'

/-- **Local optimality for the neighbourhood (9)** of §5.1, p. 558:
`B(S) = {S + s' | s' ∈ F} ∪ {S − T + l·{s'} | s' ∈ F, T ⊆ S, l·u_{s'} ≥ |N_S(T)|}`.
`X` is locally optimum if `cost X ≤ cost Y` for every solution `Y` (with any feasible
assignment) whose multiset of facilities is a neighbour of that of `X`. -/
def IsCFLLocalOpt (I : MetricInstance Cl Fa) (f : Fa → ℝ) (X : CFLSol Cl Fa u) : Prop :=
  ∀ Y : CFLSol Cl Fa u, (IsAddNbr X Y ∨ IsDropAddNbr X Y) → cost I f X ≤ cost I f Y

end LocalSearchFL.CFL


