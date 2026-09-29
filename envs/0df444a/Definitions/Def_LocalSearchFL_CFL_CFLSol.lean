-- Prove2me | Definitions.Def_LocalSearchFL_CFL_CFLSol
-- name    : LocalSearchFL_CFL_CFLSol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:20:28.488155+00:00
-- url     : https://prove2.me/theorems/041feac8-f0e4-42f8-b458-161ff1861ebb
-- title:
--   Capacitated facility location solutions with multiple copies, their facility, service and total costs
-- statement:
--   Fix a metric instance with clients $C$ (a finite set), facilities $F$ and service costs $c_{ji}$, and integer capacities $u_i$ for $i \in F$. In the capacitated facility location problem (CFL) several **copies** of the same facility may be opened; each copy of facility $i$ costs $f_i$ and serves at most $u_i$ clients.
--
--   1. **Solution.** A CFL solution $X$ consists of $n$ open copies, indexed by $s \in \{0, \dots, n-1\}$, where copy $s$ is a copy of the facility $\mathrm{loc}(s) \in F$, together with an assignment $\sigma : C \to \{0,\dots,n-1\}$ of every client to a copy, subject to the capacity constraints
--   $$|\{ j \in C : \sigma(j) = s\}| \le u_{\mathrm{loc}(s)} \quad \text{for every copy } s.$$
--   The **multiset of facilities** of $X$ is $\{\!\{\mathrm{loc}(s) : s = 0, \dots, n-1\}\!\}$.
--   2. **Neighbourhoods.** For a copy $s$, $N_X(s) = \{ j \in C : \sigma(j) = s\}$ is the set of clients it serves; for a set $T$ of copies, $N_X(T) = \{ j \in C : \sigma(j) \in T\}$.
--   3. **Costs.** For facility costs $f : F \to \mathbb R$,
--   $$\mathrm{cost}_f(X) = \sum_{s} f_{\mathrm{loc}(s)}, \qquad \mathrm{cost}_s(X) = \sum_{j \in C} c_{j\,\mathrm{loc}(\sigma(j))}, \qquad \mathrm{cost}(X) = \mathrm{cost}_f(X) + \mathrm{cost}_s(X).$$
--
--   This is the problem of §5 of the paper: a multiset $S$ of facilities and an assignment of clients satisfying the capacity constraints, with cost $\sum_{i\in S} f_i + \sum_{j\in C} c_{j\sigma(j)}$.
--
--   **Formalization Note** Each open copy is a separate index in `Fin n`, because the sets $N_S(s)$ of the paper are per copy. A solution carries its own assignment and its cost is the cost under that assignment; the paper's cost of a multiset is the minimum over feasible assignments. Statements that bound a locally optimum solution against "every solution $O$" quantify over every assignment of $O$, which is equivalent to comparing with the minimum-cost assignment. Capacities are natural numbers `u : Fa → ℕ`; their positivity and the nonnegativity of $f$ are hypotheses of the theorems.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 547, §2 (problem 3, the metric ∞-CFL problem), and p. 558, §5

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_MetricInstance

namespace LocalSearchFL.CFL

/-- A **solution of the capacitated facility location problem** (∞-CFL, §2 p. 547 and §5
p. 558) for capacities `u : Fa → ℕ`: a multiset of facility copies together with an assignment
of clients to copies respecting the capacities. There are `n` open copies, indexed by `Fin n`;
copy `s` is a copy of facility `loc s`; client `j` is served by copy `σ j`; and each copy `s`
serves at most `u (loc s)` clients. Several copies of the same facility may be open. -/
structure CFLSol (Cl Fa : Type) [Fintype Cl] (u : Fa → ℕ) where
  /-- The number of open copies. -/
  n : ℕ
  /-- The facility of which copy `s` is a copy. -/
  loc : Fin n → Fa
  /-- The copy serving client `j`. -/
  σ : Cl → Fin n
  /-- Capacity: copy `s` serves at most `u (loc s)` clients. -/
  cap : ∀ s, (Finset.univ.filter (fun j => σ j = s)).card ≤ u (loc s)

variable {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ}

/-- The multiset of facilities opened by `X` (each facility with its number of copies). -/
def CFLSol.facMultiset (X : CFLSol Cl Fa u) : Multiset Fa :=
  Multiset.map X.loc Finset.univ.val

/-- `N_X(s)`: the set of clients served by the copy `s` of `X`. -/
def CFLSol.nbhd (X : CFLSol Cl Fa u) (s : Fin X.n) : Finset Cl :=
  Finset.univ.filter (fun j => X.σ j = s)

/-- `N_X(T) = ⋃_{s ∈ T} N_X(s)`: the set of clients served by the copies in `T`. -/
def CFLSol.nbhdSet (X : CFLSol Cl Fa u) (T : Finset (Fin X.n)) : Finset Cl :=
  Finset.univ.filter (fun j => X.σ j ∈ T)

/-- The **facility cost** `cost_f(X) = ∑_{s ∈ X} f_s`, one term per open copy. -/
def costF (f : Fa → ℝ) (X : CFLSol Cl Fa u) : ℝ :=
  ∑ s : Fin X.n, f (X.loc s)

/-- The **service cost** `cost_s(X) = ∑_{j ∈ C} c_{j σ(j)}` of `X` under its assignment `σ`. -/
def costS (I : MetricInstance Cl Fa) (X : CFLSol Cl Fa u) : ℝ :=
  ∑ j : Cl, I.c j (X.loc (X.σ j))

/-- The **cost** `cost(X) = ∑_{i ∈ S} f_i + ∑_{j ∈ C} c_{j σ(j)}` (§5, p. 558). -/
def cost (I : MetricInstance Cl Fa) (f : Fa → ℝ) (X : CFLSol Cl Fa u) : ℝ :=
  costF f X + costS I X

end LocalSearchFL.CFL


