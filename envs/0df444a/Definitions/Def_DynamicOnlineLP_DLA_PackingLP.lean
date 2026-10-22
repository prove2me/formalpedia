-- Prove2me | Definitions.Def_DynamicOnlineLP_DLA_PackingLP
-- name    : DynamicOnlineLP_DLA_PackingLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T19:16:04.611917+00:00
-- url     : https://prove2.me/theorems/fc636764-13bc-4276-af3b-f40c0331873b
-- title:
--   Packing LP with box constraints: feasibility, optimal value, dual, threshold rule (9), general position
-- statement:
--   Fix a finite set $S$ of column indices, objective coefficients $\pi_t$ and constraint columns $a_t=(a_{1t},\dots,a_{mt})\in\mathbb R^m$ for $t\in S$, and a right-hand side $d\in\mathbb R^m$. The **packing linear program with box constraints** is
--
--   $$\max \sum_{t\in S}\pi_t x_t \quad\text{s.t.}\quad \sum_{t\in S} a_{it}x_t\le d_i\ (i=1,\dots,m),\qquad 0\le x_t\le 1\ (t\in S),$$
--
--   and its **dual** is
--
--   $$\min \sum_{i=1}^m d_i p_i+\sum_{t\in S}y_t \quad\text{s.t.}\quad \sum_{i=1}^m a_{it}p_i+y_t\ge \pi_t\ (t\in S),\qquad p_i,\ y_t\ge 0.$$
--
--   This file defines: feasibility of $x$; optimality of a primal solution $x^*$ (feasible and maximal among feasible points); the optimal value $\mathrm{OPT}_S(d)$ as the supremum of the objective over the feasible set; dual feasibility, the dual objective and dual optimality of $(p,y)$; an **optimal dual price** $p$ (the $p$-part of some optimal dual solution); the **threshold allocation rule**
--
--   $$x_t(p)=\begin{cases}0 & \text{if } \pi_t\le p^{\top}a_t,\\ 1 & \text{if } \pi_t>p^{\top}a_t;\end{cases}$$
--
--   and **general position** (Assumption 3): for any price vector $p\in\mathbb R^m$ at most $m$ columns $t\in S$ satisfy $p^{\top}a_t=\pi_t$.
--
--   These are the objects of the offline LP (1), the sample LP (7), the partial LP (13) and $\mathrm{LP}_s(d)$ of Agrawal, Wang and Ye; the threshold rule is how their online algorithms turn a learned dual price into decisions.
--
--   **Formalization Note** Columns are indexed by an arbitrary type and a `Finset` $S$; coordinates of $x$ outside $S$ are ignored. $\mathrm{OPT}_S(d)$ is a real `sSup`; it is the true optimum whenever $d\ge 0$ ($x=0$ is feasible and the objective is bounded by $\sum_t|\pi_t|$), and every theorem of the mission uses it only at such $d$. General position is required, as on the page, for any price vector $p\in\mathbb R^m$.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 876, Eq. (1); p. 881, Eqs. (7)–(10) and Assumption 3; p. 884, LP_s(d)

import Mathlib

namespace DynamicOnlineLP.DLA

/-- Feasibility for the packing LP with box constraints on the columns in `S` (the shape of
(1), (7), (13) and `LP_s(d)` in Agrawal–Wang–Ye 2014):
`∑_{t ∈ S} a_{it} x_t ≤ d_i` for every `i`, and `0 ≤ x_t ≤ 1` for every `t ∈ S`.
Coordinates of `x` outside `S` are ignored. -/
def IsFeasible {ι : Type} {m : ℕ} (S : Finset ι) (a : ι → Fin m → ℝ) (d : Fin m → ℝ)
    (x : ι → ℝ) : Prop :=
  (∀ i : Fin m, ∑ t ∈ S, a t i * x t ≤ d i) ∧ ∀ t ∈ S, 0 ≤ x t ∧ x t ≤ 1

/-- Primal objective `∑_{t ∈ S} π_t x_t`. -/
def primalObj {ι : Type} (S : Finset ι) (π : ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ t ∈ S, π t * x t

/-- `x` is an optimal solution of the packing LP: feasible, and no feasible point has a larger
objective. -/
def IsPrimalOptimal {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ) (a : ι → Fin m → ℝ)
    (d : Fin m → ℝ) (x : ι → ℝ) : Prop :=
  IsFeasible S a d x ∧ ∀ x' : ι → ℝ, IsFeasible S a d x' → primalObj S π x' ≤ primalObj S π x

/-- Optimal value `OPT_S(d)` of the packing LP, as the supremum of the objective over the feasible
set. For `0 ≤ d` the feasible set contains `x = 0` and the objective is bounded by `∑ |π_t|`, so
this is the true optimum; it is only ever used at such `d`. -/
noncomputable def optValue {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ) (a : ι → Fin m → ℝ)
    (d : Fin m → ℝ) : ℝ :=
  sSup (primalObj S π '' {x : ι → ℝ | IsFeasible S a d x})

/-- Feasibility for the dual (8)/(10): `p ≥ 0`, `y_t ≥ 0` and
`∑_i a_{it} p_i + y_t ≥ π_t` for every `t ∈ S`. -/
def IsDualFeasible {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ) (a : ι → Fin m → ℝ)
    (p : Fin m → ℝ) (y : ι → ℝ) : Prop :=
  (∀ i : Fin m, 0 ≤ p i) ∧ ∀ t ∈ S, 0 ≤ y t ∧ π t ≤ ∑ i : Fin m, a t i * p i + y t

/-- Dual objective `∑_i d_i p_i + ∑_{t ∈ S} y_t`. -/
def dualObj {ι : Type} {m : ℕ} (S : Finset ι) (d : Fin m → ℝ) (p : Fin m → ℝ) (y : ι → ℝ) : ℝ :=
  ∑ i : Fin m, d i * p i + ∑ t ∈ S, y t

/-- `(p, y)` is an optimal solution of the dual: dual feasible and minimal among dual feasible
pairs. -/
def IsDualOptimal {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ) (a : ι → Fin m → ℝ)
    (d : Fin m → ℝ) (p : Fin m → ℝ) (y : ι → ℝ) : Prop :=
  IsDualFeasible S π a p y ∧
    ∀ (p' : Fin m → ℝ) (y' : ι → ℝ), IsDualFeasible S π a p' y' → dualObj S d p y ≤ dualObj S d p' y'

/-- `p` is an optimal dual price: the `p`-part of some optimal dual solution `(p, y)`. -/
def IsOptimalDualPrice {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ) (a : ι → Fin m → ℝ)
    (d : Fin m → ℝ) (p : Fin m → ℝ) : Prop :=
  ∃ y : ι → ℝ, IsDualOptimal S π a d p y

/-- The threshold allocation rule (9): `x_t(p) = 0` if `π_t ≤ pᵀ a_t`, and `1` if `π_t > pᵀ a_t`. -/
noncomputable def threshold {ι : Type} {m : ℕ} (π : ι → ℝ) (a : ι → Fin m → ℝ) (p : Fin m → ℝ)
    (t : ι) : ℝ :=
  if π t ≤ ∑ i : Fin m, p i * a t i then 0 else 1

/-- Assumption 3 (general position) for the columns in `S`: for any price vector `p ∈ ℝ^m` at most
`m` columns `t ∈ S` satisfy `pᵀ a_t = π_t`. -/
def GeneralPositionOn {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ) (a : ι → Fin m → ℝ) : Prop :=
  ∀ p : Fin m → ℝ, (S.filter (fun t => ∑ i : Fin m, p i * a t i = π t)).card ≤ m

end DynamicOnlineLP.DLA


