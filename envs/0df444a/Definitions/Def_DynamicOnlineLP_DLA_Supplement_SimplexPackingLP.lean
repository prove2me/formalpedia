-- Prove2me | Definitions.Def_DynamicOnlineLP_DLA_Supplement_SimplexPackingLP
-- name    : DynamicOnlineLP_DLA_Supplement_SimplexPackingLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:05:55.6988+00:00
-- url     : https://prove2.me/theorems/fe3140cf-f0c8-436c-8912-008941c48a83
-- title:
--   Packing LP with simplex decisions (15): feasibility, optimal value, dual and optimal resource prices
-- statement:
--   Fix a finite set $S$ of arrivals, $k$ options per arrival and $m$ resources. Choosing option $j$ at arrival $t$ earns $f_{tj}$ and consumes $g_{itj}$ of resource $i$. For a right-hand side $d\in\mathbb R^m$, the **packing linear program with simplex decisions** chooses one vector $x_t\in\mathbb R^k$ per arrival:
--
--   $$\max\ \sum_{t\in S}f_t^{\top}x_t\quad\text{s.t.}\quad\sum_{t\in S}g_{it}^{\top}x_t\le d_i\ (i=1,\dots,m),\qquad x_t\ge0,\quad e^{\top}x_t\le1\ (t\in S),$$
--
--   where $e$ is the all-ones vector. Its **dual** is
--
--   $$\min\ \sum_{i=1}^m d_ip_i+\sum_{t\in S}y_t\quad\text{s.t.}\quad\sum_{i=1}^m p_ig_{itj}+y_t\ge f_{tj}\ (t\in S,\ j=1,\dots,k),\qquad p\ge0,\ y\ge0.$$
--
--   The definitions are: feasibility and optimality of a primal solution; the optimal value $\mathrm{OPT}_S(d)$; feasibility and optimality of a dual solution $(p,y)$; and an **optimal dual resource price**, which is the $p$-part of some optimal dual solution.
--
--   With $S=\{1,\dots,n\}$ and $d=b$ this is program (15), the offline program of the general online LP (3). With $S=\{1,\dots,\ell\}$ it is the program from which the multidimensional dynamic learning algorithm learns its prices. The constraint $e^{\top}x_t\le1$ couples the $k$ coordinates of an arrival, so this is not the box-constrained program of the scalar model on $nk$ columns.
--
--   **Formalization Note** The consumption array is written `g t i j` for $g_{itj}$. Values of $x$ and $y$ outside $S$ are ignored. The optimal value is a real supremum over all fractional feasible solutions. For $d\ge0$ the feasible set contains $0$ and the objective is bounded by $\sum_{t,j}|f_{tj}|$, so it is the true optimum. On an infeasible $d$ the supremum of the empty set would be $0$; the competitive theorem uses it only with $d=b\ge0$.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 886, Eq. (15); p. 877, offline problem of Eq. (3)

import Mathlib

namespace DynamicOnlineLP.DLA.Supplement

/-- Feasibility for the packing LP with simplex decisions on the arrivals in `S`:
`x_t ≥ 0`, `∑_j x_{tj} ≤ 1` for every `t ∈ S`, and `∑_{t ∈ S} ∑_j g_{tij} x_{tj} ≤ d_i` for
every `i`. Values of `x` outside `S` are ignored. -/
def IsBlockFeasible {ι : Type} {m k : ℕ} (S : Finset ι) (g : ι → Fin m → Fin k → ℝ)
    (d : Fin m → ℝ) (x : ι → Fin k → ℝ) : Prop :=
  (∀ i : Fin m, ∑ t ∈ S, ∑ j : Fin k, g t i j * x t j ≤ d i) ∧
    ∀ t ∈ S, (∀ j : Fin k, 0 ≤ x t j) ∧ ∑ j : Fin k, x t j ≤ 1

/-- Primal objective `∑_{t ∈ S} ∑_j f_{tj} x_{tj}`. -/
def blockPrimalObj {ι : Type} {k : ℕ} (S : Finset ι) (f : ι → Fin k → ℝ)
    (x : ι → Fin k → ℝ) : ℝ :=
  ∑ t ∈ S, ∑ j : Fin k, f t j * x t j

/-- `x` is an optimal primal solution: feasible, with objective at least that of every feasible
point. -/
def IsBlockPrimalOptimal {ι : Type} {m k : ℕ} (S : Finset ι) (f : ι → Fin k → ℝ)
    (g : ι → Fin m → Fin k → ℝ) (d : Fin m → ℝ) (x : ι → Fin k → ℝ) : Prop :=
  IsBlockFeasible S g d x ∧
    ∀ x' : ι → Fin k → ℝ, IsBlockFeasible S g d x' → blockPrimalObj S f x' ≤ blockPrimalObj S f x

/-- Optimal value over all fractional simplex decisions, as the supremum of the objective over the
feasible set. For `0 ≤ d` this set contains `x = 0` and the objective is bounded by
`∑_t ∑_j |f_{tj}|`. -/
noncomputable def blockOptValue {ι : Type} {m k : ℕ} (S : Finset ι) (f : ι → Fin k → ℝ)
    (g : ι → Fin m → Fin k → ℝ) (d : Fin m → ℝ) : ℝ :=
  sSup (blockPrimalObj S f '' {x : ι → Fin k → ℝ | IsBlockFeasible S g d x})

/-- Dual feasibility: `p ≥ 0`, `y_t ≥ 0`, and `f_{tj} ≤ ∑_i p_i g_{tij} + y_t` for every
`t ∈ S` and every option `j`. -/
def IsBlockDualFeasible {ι : Type} {m k : ℕ} (S : Finset ι) (f : ι → Fin k → ℝ)
    (g : ι → Fin m → Fin k → ℝ) (p : Fin m → ℝ) (y : ι → ℝ) : Prop :=
  (∀ i : Fin m, 0 ≤ p i) ∧
    ∀ t ∈ S, 0 ≤ y t ∧ ∀ j : Fin k, f t j ≤ ∑ i : Fin m, p i * g t i j + y t

/-- Dual objective `∑_i d_i p_i + ∑_{t ∈ S} y_t`. -/
def blockDualObj {ι : Type} {m : ℕ} (S : Finset ι) (d : Fin m → ℝ) (p : Fin m → ℝ)
    (y : ι → ℝ) : ℝ :=
  ∑ i : Fin m, d i * p i + ∑ t ∈ S, y t

/-- `(p, y)` is an optimal dual solution. -/
def IsBlockDualOptimal {ι : Type} {m k : ℕ} (S : Finset ι) (f : ι → Fin k → ℝ)
    (g : ι → Fin m → Fin k → ℝ) (d : Fin m → ℝ) (p : Fin m → ℝ) (y : ι → ℝ) : Prop :=
  IsBlockDualFeasible S f g p y ∧
    ∀ (p' : Fin m → ℝ) (y' : ι → ℝ),
      IsBlockDualFeasible S f g p' y' → blockDualObj S d p y ≤ blockDualObj S d p' y'

/-- `p` is an optimal dual resource price: the `p`-part of some optimal dual solution `(p, y)`. -/
def IsBlockOptimalPrice {ι : Type} {m k : ℕ} (S : Finset ι) (f : ι → Fin k → ℝ)
    (g : ι → Fin m → Fin k → ℝ) (d : Fin m → ℝ) (p : Fin m → ℝ) : Prop :=
  ∃ y : ι → ℝ, IsBlockDualOptimal S f g d p y

end DynamicOnlineLP.DLA.Supplement


