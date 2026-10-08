-- Prove2me | Definitions.Def_VRPTWColGen92_Bound_CoveringLP
-- name    : VRPTWColGen92_Bound_CoveringLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:23:05.630155+00:00
-- url     : https://prove2.me/theorems/f987dc6d-a356-4b80-a50a-ede6090327e2
-- title:
--   Secs. 4–4.1, pp. 346–347 — the LP relaxation of the set covering type model (1)–(6), its restricted dual, and the marginal costs of columns and arcs
-- statement:
--   This module defines the linear programs of the column generation scheme of Desrochers, Desrosiers and Solomon (1992) on top of the network of the mission.
--
--   **The set covering type model (Sec. 4, p. 346).** For a path $r$ and a customer $i$, $\gamma_{ir}$ is the number of visits of $r$ to $i$. Given a set $\mathcal R$ of admissible columns (paths), a point of the LP relaxation of (1)–(6) is a triple $(x, X_d, X_c)$ where $x = (x_r)$ is a nonnegative real vector with finitely many nonzero entries, all on columns of $\mathcal R$, and
--   $$\sum_{r} \gamma_{ir} x_r \ge 1\ \ (i \in N\setminus\{d\}),\qquad \sum_{r} x_r - X_d = 0,\qquad \sum_r c_r x_r - X_c = 0,\qquad X_d,\ X_c \ge 0.$$
--   These are the rows (2), (3), (4) and the relaxations of (5), (6). The objective is (1), $\sum_r c_r x_r$; a feasible point is **optimal over $\mathcal R$** when no feasible point has a smaller objective.
--
--   **The restricted dual.** For a finite column set $R_0$, the dual of the LP relaxation over $R_0$ has variables $\pi_i$ (one per customer, for (2)), $\pi_d$ (for (3)) and $\pi_c$ (for (4)), and reads
--   $$\max \sum_{i \in N\setminus\{d\}} \pi_i \quad\text{s.t.}\quad \sum_{i\in N\setminus\{d\}} \pi_i \gamma_{ir} + \pi_d + \pi_c c_r \le c_r\ (r \in R_0),\qquad \pi_i \ge 0,\ \pi_d \ge 0,\ \pi_c \ge 0.$$
--   The signs of $\pi_d$ and $\pi_c$ come from the columns of $X_d$ and $X_c$ (coefficient $-1$, cost $0$, $X \ge 0$).
--
--   **Marginal costs (Sec. 4.1, p. 347).** For dual values $(\pi, \pi_d, \pi_c)$ the marginal cost of a column and of an arc are
--   $$\bar c_r = c_r - \sum_{i\in N\setminus\{d\}} \pi_i\gamma_{ir} - \pi_d - \pi_c c_r,\qquad \bar c_{ij} = (1-\pi_c)\,c_{ij} - \pi_i,$$
--   where $\pi_i$ in $\bar c_{ij}$ is read as $\pi_d$ when $i = d$ (the page's "as $i_0 = d$"). The marginal cost of a path is the sum $\sum_{k=0}^{K}\bar c_{i_k i_{k+1}}$ of the marginal costs of its arcs; this is what the pricing subproblem minimizes.
--
--   **Formalization Note.** The LP relaxation keeps $X_d, X_c \ge 0$ and relaxes $x_r \in \{0,1\}$ to $x_r \ge 0$ with no upper bound (the page's marginal cost has no dual variable for $x_r \le 1$). This is the root LP: the branching rows of Sec. 5 are not part of it. The vector $x$ is a finitely supported function on lists of nodes, so the column set need not be finite. The customer duals are a function on all nodes whose value at the depot is never used; the depot's dual in $\bar c_{ij}$ is $\pi_d$.
-- source:
--   Desrochers, Desrosiers & Solomon, A new optimization algorithm for the vehicle routing problem with time windows, Oper. Res. 40 (1992), pp. 346–347, Sec. 4, (1)–(6), and Sec. 4.1

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network

namespace VRPTWColGen92.Bound

variable {n : ℕ}

/-- A point `(x, X_d, X_c)` of the LP relaxation of the set covering type model (1)–(6); `x` has finite
support (finitely many columns used). -/
structure LPPoint (n : ℕ) where
  x : List (Fin (n + 1)) →₀ ℝ
  Xd : ℝ
  Xc : ℝ

/-- The objective (1), `∑_r c_r x_r`. -/
def objective (I : Instance n) (z : LPPoint n) : ℝ :=
  ∑ p ∈ z.x.support, cost I p * z.x p

/-- Feasibility for the LP relaxation of (1)–(6) over the column set `𝓡`: columns in `𝓡`, `x_r ≥ 0`,
covering rows (2) `∑_r γ_ir x_r ≥ 1` for every customer, (3) `∑_r x_r = X_d`, (4) `∑_r c_r x_r = X_c`,
and `X_d, X_c ≥ 0`. Here `γ_ir` is the number of visits of `r` to `i`. -/
def LPFeasible (I : Instance n) (𝓡 : Set (List (Fin (n + 1)))) (z : LPPoint n) : Prop :=
  (∀ p ∈ z.x.support, p ∈ 𝓡) ∧
  (∀ p, 0 ≤ z.x p) ∧
  (∀ i : Fin (n + 1), i ≠ 0 → 1 ≤ ∑ p ∈ z.x.support, (p.count i : ℝ) * z.x p) ∧
  ∑ p ∈ z.x.support, z.x p = z.Xd ∧
  ∑ p ∈ z.x.support, cost I p * z.x p = z.Xc ∧
  0 ≤ z.Xd ∧ 0 ≤ z.Xc

/-- Optimality for the LP relaxation over `𝓡`. -/
def LPOptimal (I : Instance n) (𝓡 : Set (List (Fin (n + 1)))) (z : LPPoint n) : Prop :=
  LPFeasible I 𝓡 z ∧ ∀ z' : LPPoint n, LPFeasible I 𝓡 z' → objective I z ≤ objective I z'

/-- Dual variables: `π i` for the covering row (2) of customer `i` (the value at the depot index is
unused), `πd` for (3) and `πc` for (4). -/
structure DualPoint (n : ℕ) where
  π : Fin (n + 1) → ℝ
  πd : ℝ
  πc : ℝ

/-- Feasibility for the dual of the LP relaxation restricted to the finite column set `R₀`:
`π_i ≥ 0` for customers, `π_d ≥ 0`, `π_c ≥ 0` (the columns of `X_d`, `X_c`), and for every column
`r ∈ R₀`, `∑_{i ≠ d} π_i γ_ir + π_d + π_c c_r ≤ c_r`. -/
def DualFeasible (I : Instance n) (R₀ : Finset (List (Fin (n + 1)))) (y : DualPoint n) : Prop :=
  (∀ i : Fin (n + 1), i ≠ 0 → 0 ≤ y.π i) ∧ 0 ≤ y.πd ∧ 0 ≤ y.πc ∧
  ∀ p ∈ R₀,
    ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), y.π i * (p.count i : ℝ) + y.πd + y.πc * cost I p
      ≤ cost I p

/-- The dual objective `∑_{i ≠ d} π_i`. -/
def dualObjective (y : DualPoint n) : ℝ :=
  ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), y.π i

/-- Optimality for the dual of the restricted LP. -/
def DualOptimal (I : Instance n) (R₀ : Finset (List (Fin (n + 1)))) (y : DualPoint n) : Prop :=
  DualFeasible I R₀ y ∧
    ∀ y' : DualPoint n, DualFeasible I R₀ y' → dualObjective y' ≤ dualObjective y

/-- The marginal cost of a column, `c̄_r = c_r − ∑_{i ≠ d} π_i γ_ir − π_d − π_c c_r` (Sec. 4.1). -/
def columnMarginal (I : Instance n) (y : DualPoint n) (p : List (Fin (n + 1))) : ℝ :=
  cost I p - ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), y.π i * (p.count i : ℝ) - y.πd
    - y.πc * cost I p

/-- The dual value attached to a node in the arc marginal cost: `π_d` at the depot, `π_i` at a
customer. -/
def nodeDual (y : DualPoint n) (i : Fin (n + 1)) : ℝ :=
  if i = 0 then y.πd else y.π i

/-- The marginal cost of an arc, `c̄_ij = (1 − π_c) c_ij − π_i` (Sec. 4.1), with `π_d` at `i = d`. -/
def arcMarginal (I : Instance n) (y : DualPoint n) (i j : Fin (n + 1)) : ℝ :=
  (1 - y.πc) * I.c i j - nodeDual y i

/-- The marginal cost of a path, the sum of the arc marginal costs of its arcs. -/
def pathMarginal (I : Instance n) (y : DualPoint n) (p : List (Fin (n + 1))) : ℝ :=
  arcSum (arcMarginal I y) p

end VRPTWColGen92.Bound


