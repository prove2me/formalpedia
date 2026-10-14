-- Prove2me | Definitions.Def_BudgetedAffine_NetworkGap_LotSizing
-- name    : BudgetedAffine_NetworkGap_LotSizing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:25:21.382564+00:00
-- url     : https://prove2.me/theorems/4f520b99-c015-4f2c-a858-bfb26ffdf3a4
-- title:
--   (7.1) — the two-stage robust lot-sizing problem, its adjustable and affine objective values
-- statement:
--   **The two-stage robust lot-sizing problem (7.1).** A finite set $N$ of nodes is given. Node $i$ holds inventory at cost $c_i$ per unit and has capacity $K_i$; it faces a demand $h_i$ that is revealed only in the second stage, as an adversarial choice of a demand vector $h$ from an uncertainty set $\mathcal U\subseteq\mathbb R^N$. A finite set $E$ of arcs is given along which inventory may be shipped in the second stage; arc $a\in E$ goes from node $\mathrm{src}(a)$ to node $\mathrm{tgt}(a)$ and has distance $d_a$ (the per-unit transportation cost).
--
--   In the first stage the decision maker fixes inventory levels $x\in\mathbb R^N$; in the second stage, after observing $h$, it ships $y(h)\in\mathbb R^E$. A pair $(x,y)$, with $y$ a rule $h\mapsto y(h)$, is **feasible** when
--   $$0\le x_i\le K_i\ \ (i\in N),\qquad y(h)\ge 0,\qquad x_i+\sum_{a:\,\mathrm{tgt}(a)=i}y_a(h)-\sum_{a:\,\mathrm{src}(a)=i}y_a(h)\ \ge\ h_i\ \ (i\in N)\quad\text{for every } h\in\mathcal U .$$
--   The cost of $(x,y)$ in scenario $h$ is $\sum_{i}c_ix_i+\sum_{a}d_a\,y_a(h)$. Following the epigraph formulation (7.1), the **adjustable objective values** are the numbers $t$ for which some feasible $(x,y)$ satisfies
--   $$\sum_{i\in N}c_ix_i+\sum_{a\in E}d_a\,y_a(h)\ \le\ t\qquad\text{for every } h\in\mathcal U,$$
--   and $z_{AR}(\mathcal U)$ is the least such $t$. An **affine policy** is a rule $y(h)=Ph+q$ with $P\in\mathbb R^{E\times N}$ (one row per arc, one column per node) and $q\in\mathbb R^E$; the **affine objective values** are defined in the same way with $y$ restricted to affine policies (feasibility still includes $Ph+q\ge 0$ for every $h\in\mathcal U$), and $z_{Aff}(\mathcal U)$ is the least of them.
--
--   This is the model of Section 7 in which the recourse matrix is a network matrix with entries in $\{-1,0,1\}$; the mission's family of instances (7.2) is a special case.
--
--   **Formalization Note** The paper allows shipment between every ordered pair of nodes, with distances $d_{ij}$ that may be $+\infty$. Here only the arcs of finite distance are kept, as the set $E$: a solution of finite cost ships nothing along an arc of infinite distance, so removing those arcs changes no optimal value (App. D does the same: "flow can be sent only from $J_1$ to $J_2$"; "the number of rows of $P$ is the number of edges in the graph"). With $E=N\times N$ and finite distances the definition is (7.1) verbatim. The optimal values are not real infima: the theorems state them as `IsLeast` of the sets of objective values, so a claim "$z=v$" includes attainment and can never hold vacuously on an empty feasible set. The second stage is a rule $y(\cdot)$, which gives the same values as choosing $y(h)$ separately for each $h$.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Sec. 7.1, eq. (7.1), pp. 27–28; affine policies (2.1), p. 5; App. D, pp. 35–36

import Mathlib

namespace BudgetedAffine.NetworkGap

open Matrix

/-- Data of the two-stage robust lot-sizing problem (7.1) on a finite node set `N`.
`E` is the set of arcs along which inventory may be shipped in the second stage (the arcs of
finite distance); arc `a` goes from node `src a` to node `tgt a` and has distance `d a`.
Node `v` has inventory cost `c v` per unit and capacity `K v`; `U` is the uncertainty set of
demand vectors `h : N → ℝ`. -/
structure LotSizing (N E : Type*) where
  /-- tail (sending node) of an arc -/
  src : E → N
  /-- head (receiving node) of an arc -/
  tgt : E → N
  /-- inventory cost `c_i` per unit at node `i` -/
  c : N → ℝ
  /-- capacity `K_i` of node `i` -/
  K : N → ℝ
  /-- distance `d_ij` of an arc -/
  d : E → ℝ
  /-- uncertainty set of demands -/
  U : Set (N → ℝ)

namespace LotSizing

variable {N E : Type*} [Fintype N] [Fintype E] [DecidableEq N]

/-- Total shipment `∑_j y_{jv}` arriving at node `v` under the shipment vector `y`. -/
def inflow (I : LotSizing N E) (y : E → ℝ) (v : N) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => I.tgt a = v), y a

/-- Total shipment `∑_j y_{vj}` leaving node `v` under the shipment vector `y`. -/
def outflow (I : LotSizing N E) (y : E → ℝ) (v : N) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => I.src a = v), y a

/-- `(x, y)` is feasible for (7.1): `0 ≤ x_i ≤ K_i` for every node, and for every demand
`h ∈ U` the shipments are non-negative, `y(h) ≥ 0`, and every node's demand is covered:
`x_i + ∑_j y_{ji}(h) − ∑_j y_{ij}(h) ≥ h_i`. -/
def Feasible (I : LotSizing N E) (x : N → ℝ) (y : (N → ℝ) → E → ℝ) : Prop :=
  (∀ v, 0 ≤ x v ∧ x v ≤ I.K v) ∧
    ∀ h ∈ I.U, 0 ≤ y h ∧ ∀ v, h v ≤ x v + I.inflow (y h) v - I.outflow (y h) v

/-- Cost `∑_i c_i x_i + ∑_{ij} d_ij y_ij` of first-stage inventory `x` and shipments `yh`. -/
def cost (I : LotSizing N E) (x : N → ℝ) (yh : E → ℝ) : ℝ :=
  ∑ v, I.c v * x v + ∑ a, I.d a * yh a

/-- Objective values of the epigraph formulation (7.1) over adjustable solutions: the numbers
`t` such that some feasible `(x, y)` has `∑_i c_i x_i + ∑_{ij} d_ij y_ij(h) ≤ t` for every
`h ∈ U`. `z_AR(U)` is the least element of this set. -/
def adjustableValues (I : LotSizing N E) : Set ℝ :=
  {t | ∃ (x : N → ℝ) (y : (N → ℝ) → E → ℝ), I.Feasible x y ∧ ∀ h ∈ I.U, I.cost x (y h) ≤ t}

/-- The affine second-stage policy `h ↦ P h + q` (one row of `P` per arc, one column per
node). -/
def affinePolicy (P : Matrix E N ℝ) (q : E → ℝ) : (N → ℝ) → E → ℝ :=
  fun h => P *ᵥ h + q

/-- The same objective values restricted to affine policies `y(h) = P h + q`; feasibility
includes `P h + q ≥ 0` for every `h ∈ U`. `z_Aff(U)` is the least element of this set. -/
def affineValues (I : LotSizing N E) : Set ℝ :=
  {t | ∃ (x : N → ℝ) (P : Matrix E N ℝ) (q : E → ℝ),
    I.Feasible x (affinePolicy P q) ∧ ∀ h ∈ I.U, I.cost x (affinePolicy P q h) ≤ t}

end LotSizing

end BudgetedAffine.NetworkGap


