-- Prove2me | Definitions.Def_ConsHalving_Additive_Setting
-- name    : ConsHalving_Additive_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:03.767663+00:00
-- url     : https://prove2.me/theorems/00eaef73-c23a-472e-9182-5ccb26edeaa2
-- title:
--   §2, pp. 4–5 — fractional sets of items, additive utilities, consensus halving and cuts (Definition 2.1), the system S ∪ T and the step of the algorithm
-- statement:
--   This file fixes the model of §2 of Goldberg, Hollender, Igarashi, Manurangsi and Suksompong.
--
--   There are $n$ agents and $m$ items. Agent $i$ has a value $u_i(j)\in\mathbb R$ for item $j$.
--
--   1. A **fractional set of items** holds a fraction $x_j\in[0,1]$ of each item $j$; it is described by the vector $x=(x_1,\dots,x_m)$.
--   2. Utilities are **additive**: agent $i$ values the fractional set $x$ at
--   $$u_i(x)=\sum_{j=1}^m x_j\,u_i(j).$$
--   3. A **consensus halving** (Definition 2.1) is a partition of the items into two fractional sets $M_1$, $M_2$ that every agent values equally. Since the fractions of each item in the two parts sum to exactly $1$, the partition is determined by $M_1=x$, with $M_2$ holding the fraction $1-x_j$ of item $j$. Thus $x$ is a consensus halving iff $x\in[0,1]^m$ and
--   $$\sum_j x_j\,u_i(j)=\sum_j (1-x_j)\,u_i(j)\qquad\text{for every agent } i.$$
--   4. Item $j$ is **cut** if a positive fraction of it lies in both parts, i.e. $0<x_j<1$. The number of cut items is $\#\{j: 0<x_j<1\}$.
--   5. The algorithm of the proof of Theorem 2.2 works with the linear system $S$: $\sum_j (y_j-\tfrac12)\,u_i(j)=0$ for every agent $i$, together with a set $T$ of equations $y_j=x_j$ ($j\in T$) that freeze coordinates of the current point $x$.
--   6. Given the current point $x$ and another solution $y$, Step 3(a) sets, for $y_j\ne x_j$,
--   $$\gamma_j=\begin{cases}\dfrac{1-x_j}{y_j-x_j}&\text{if } y_j>x_j,\\[2mm] \dfrac{x_j}{x_j-y_j}&\text{if } y_j<x_j,\end{cases}$$
--   and Step 3(c) moves to the point $s_j=(1-\gamma)\,x_j+\gamma\,y_j$.
--
--   These are the objects about which the goal theorem and all milestones of the mission are stated.
--
--   **Formalization Note** Agents are `Fin n` and items `Fin m` (the paper's $[n]$, $[m]$, shifted to start at $0$); $n,m\ge1$ is not assumed. The partition $(M_1,M_2)$ is encoded by $x$ alone, so the fractions of each item sum to $1$ by construction. Utilities are arbitrary reals here; the nonnegativity of §2 is imposed in the goal theorem only. `gamma x y j` is only meaningful where $y_j\ne x_j$: at $y_j=x_j$ Lean's convention $a/0=0$ gives the value $0$, and every statement using `gamma` restricts to coordinates with $y_j\ne x_j$.
-- source:
--   Goldberg et al., Consensus Halving for Sets of Items, arXiv:2007.06754v1, pp. 4–5, §2, Definition 2.1, (1), proof of Theorem 2.2 (Steps 2, 3(a), 3(c))

import Mathlib

namespace ConsHalving.Additive

/-- Additive utility of agent `i` for the fractional set that holds the fraction `x j` of item `j`:
`u_i(M′) = ∑_j x_j · u_i(j)` (§2, p. 4). Agents are `Fin n`, items `Fin m`, `u i j = u_i(j)`. -/
def util {n m : ℕ} (u : Fin n → Fin m → ℝ) (i : Fin n) (x : Fin m → ℝ) : ℝ :=
  ∑ j, x j * u i j

/-- A fractional set of items: a fraction `x j ∈ [0, 1]` of each item `j` (§2, p. 4). -/
def IsFractional {m : ℕ} (x : Fin m → ℝ) : Prop :=
  ∀ j, 0 ≤ x j ∧ x j ≤ 1

/-- Definition 2.1 (p. 4) for additive utilities: the partition `(M₁, M₂)` in which `M₁` holds the
fraction `x j` and `M₂` the fraction `1 - x j` of item `j` (so the fractions of each item sum to
exactly `1`) is a consensus halving: both parts are fractional sets and `u_i(M₁) = u_i(M₂)` for
every agent `i`. -/
def IsConsensusHalving {n m : ℕ} (u : Fin n → Fin m → ℝ) (x : Fin m → ℝ) : Prop :=
  IsFractional x ∧ ∀ i, util u i x = util u i (fun j => 1 - x j)

/-- Item `j` is cut (Definition 2.1): a positive fraction of it lies in both parts. -/
def IsCut {m : ℕ} (x : Fin m → ℝ) (j : Fin m) : Prop :=
  0 < x j ∧ 0 < 1 - x j

open Classical in
/-- The number of cut items. -/
noncomputable def numCuts {m : ℕ} (x : Fin m → ℝ) : ℕ :=
  (Finset.univ.filter (fun j => IsCut x j)).card

/-- `y` solves the system `S` of Step 2 (p. 5): `∑_{j∈M} (y_j - 1/2) · u_i(j) = 0` for every
agent `i`. -/
def SolvesS {n m : ℕ} (u : Fin n → Fin m → ℝ) (y : Fin m → ℝ) : Prop :=
  ∀ i, ∑ j, (y j - 1 / 2) * u i j = 0

/-- `y` solves `S ∪ T` (Step 3, p. 5), where `T` holds the equations `y_j = x_j` for `j ∈ T`. -/
def SolvesST {n m : ℕ} (u : Fin n → Fin m → ℝ) (T : Finset (Fin m)) (x y : Fin m → ℝ) : Prop :=
  SolvesS u y ∧ ∀ j ∈ T, y j = x j

/-- `γ_j` of Step 3(a) (p. 5): `(1 - x_j)/(y_j - x_j)` if `y_j > x_j`, and `x_j/(x_j - y_j)` if
`y_j < x_j`. Only meaningful where `y j ≠ x j`; at `y j = x j` it is the junk value `0`. -/
noncomputable def gamma {m : ℕ} (x y : Fin m → ℝ) (j : Fin m) : ℝ :=
  if x j < y j then (1 - x j) / (y j - x j) else x j / (x j - y j)

/-- The point `s` of Step 3(c) (p. 5): `s_j = (1 - γ) · x_j + γ · y_j`. -/
def stepPoint {m : ℕ} (x y : Fin m → ℝ) (γ : ℝ) : Fin m → ℝ :=
  fun j => (1 - γ) * x j + γ * y j

end ConsHalving.Additive


