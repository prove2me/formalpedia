-- Prove2me | Definitions.Def_WorstCaseCVaR_Box_DualPair
-- name    : WorstCaseCVaR_Box_DualPair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:12.114526+00:00
-- url     : https://prove2.me/theorems/ef7030e7-ca7d-4298-99f3-3b281a2ea4da
-- title:
--   Box uncertainty set (21) and the linear programs (22)–(23) with optimal value $\gamma^*(u)$
-- statement:
--   This file fixes the finite-dimensional objects of §2.2.1 of Zhu and Fukushima (2009). Throughout, $S \ge 0$ is the number of scenarios. Vectors in $\mathbb R^S$ are compared componentwise, $e$ is the vector of ones, and $a^\top b$ is the dot product.
--
--   1. **Box uncertainty set (21).** Given a nominal distribution $\pi^0 \in \mathbb R^S$ and constant vectors $\underline\eta, \overline\eta \in \mathbb R^S$,
--   $$\mathcal P_\pi^B = \{\pi : \pi = \pi^0 + \eta,\ e^\top\eta = 0,\ \underline\eta \le \eta \le \overline\eta\}.$$
--   2. **The linear program (22)** in the variable $\eta \in \mathbb R^S$, for a given $u \in \mathbb R^S$:
--   $$\max_{\eta \in \mathbb R^S}\{u^\top\eta : e^\top\eta = 0,\ \underline\eta \le \eta \le \overline\eta\}.$$
--   Its optimal value is denoted $\gamma^*(u)$ and is defined as the supremum of $u^\top\eta$ over the feasible set of (22).
--   3. **The dual program (23)** in the variables $(z, \xi, \omega) \in \mathbb R \times \mathbb R^S \times \mathbb R^S$:
--   $$\min_{(z,\xi,\omega)}\{\overline\eta^\top\xi + \underline\eta^\top\omega : e z + \xi + \omega = u,\ \xi \ge 0,\ \omega \le 0\}.$$
--   A point is an **optimal solution of (23)** if it is feasible and its objective value is no larger than that of every feasible point.
--
--   The upper bound $\overline\eta$ pairs with the nonnegative multiplier $\xi$ and the lower bound $\underline\eta$ with the nonpositive multiplier $\omega$. These objects enter the reformulation of worst-case CVaR minimization under box uncertainty as a linear program (Proposition 2).
--
--   **Formalization Note** Indices are `Fin S` (zero-based). A point of (23) is the structure `Dual23 S` with fields `z`, `ξ`, `ω`. When (22) is infeasible, the real `sSup ∅ = 0` is a junk value of $\gamma^*(u)$; every theorem using $\gamma^*$ assumes (22) feasible. No hypothesis such as $\pi^0 \ge 0$, $e^\top\pi^0 = 1$ or $\underline\eta \le \overline\eta$ is built into these definitions: the paper treats $\pi^0, \underline\eta, \overline\eta$ as given data.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1159, Eq. (21), (22), (23)

import Mathlib

open Matrix

namespace WorstCaseCVaR.Box

/-- The box uncertainty set (21), p. 1159:
`𝒫_π^B = {π : π = π⁰ + η, eᵀη = 0, η̲ ≤ η ≤ η̄}` (vector inequalities are pointwise). -/
def boxSet {S : ℕ} (π0 ηlo ηhi : Fin S → ℝ) : Set (Fin S → ℝ) :=
  {π | ∃ η : Fin S → ℝ, π = π0 + η ∧ ∑ k, η k = 0 ∧ ηlo ≤ η ∧ η ≤ ηhi}

/-- The feasible set of the linear program (22): `{η ∈ ℝ^S : eᵀη = 0, η̲ ≤ η ≤ η̄}`. -/
def lp22Feasible {S : ℕ} (ηlo ηhi : Fin S → ℝ) : Set (Fin S → ℝ) :=
  {η | ∑ k, η k = 0 ∧ ηlo ≤ η ∧ η ≤ ηhi}

/-- `γ*(u)`, the optimal value of (22): the supremum of `uᵀη` over the feasible set of (22).
It is the true optimal value whenever (22) is feasible (the feasible set is bounded by the box);
on an infeasible (22) the real `sSup ∅ = 0` is a junk value, and every statement using
`gammaStar` assumes `(lp22Feasible ηlo ηhi).Nonempty`. -/
noncomputable def gammaStar {S : ℕ} (ηlo ηhi u : Fin S → ℝ) : ℝ :=
  sSup ((fun η => u ⬝ᵥ η) '' lp22Feasible ηlo ηhi)

/-- A point `(z, ξ, ω) ∈ ℝ × ℝ^S × ℝ^S` of the dual program (23). -/
structure Dual23 (S : ℕ) where
  z : ℝ
  ξ : Fin S → ℝ
  ω : Fin S → ℝ

/-- The feasible set of (23) for a given `u`: `e z + ξ + ω = u`, `ξ ≥ 0`, `ω ≤ 0`. -/
def lp23Feasible {S : ℕ} (u : Fin S → ℝ) : Set (Dual23 S) :=
  {d | (fun _ => d.z) + d.ξ + d.ω = u ∧ 0 ≤ d.ξ ∧ d.ω ≤ 0}

/-- The objective of (23): `η̄ᵀξ + η̲ᵀω`. -/
def lp23Obj {S : ℕ} (ηlo ηhi : Fin S → ℝ) (d : Dual23 S) : ℝ :=
  ηhi ⬝ᵥ d.ξ + ηlo ⬝ᵥ d.ω

/-- `d` is an optimal solution of the minimization (23) with right-hand side `u`. -/
def IsOptimal23 {S : ℕ} (ηlo ηhi u : Fin S → ℝ) (d : Dual23 S) : Prop :=
  d ∈ lp23Feasible u ∧ IsMinOn (lp23Obj ηlo ηhi) (lp23Feasible u) d

end WorstCaseCVaR.Box


