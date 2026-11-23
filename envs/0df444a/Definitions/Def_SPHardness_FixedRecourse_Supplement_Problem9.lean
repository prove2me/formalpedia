-- Prove2me | Definitions.Def_SPHardness_FixedRecourse_Supplement_Problem9
-- name    : SPHardness_FixedRecourse_Supplement_Problem9
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:56:18.363636+00:00
-- url     : https://prove2.me/theorems/880d8726-27cf-4003-b0af-b70309d2cf8c
-- title:
--   Problem (9), pp. 8–9 — the fixed-recourse program with first-stage decision $x\in[0,1]$, its optimal value $f^\star$, and $\epsilon$-optimal decisions
-- statement:
--   Fix a dimension $k$, weights $\alpha\in\mathbb R^k_+$, a budget $\beta\in\mathbb R_+$ and a cost coefficient $c\in\mathbb R$. For a first-stage decision $x$ and a realization $\xi\in[0,1]^k$, the **recourse function** $Q(x,\xi;\alpha,\beta)$ is the optimal value of the second-stage linear program
--
--   $$
--   Q(x,\xi;\alpha,\beta)=\max\Bigl\{\xi^\top y-\beta z:\ y\le\alpha z,\ y\in\mathbb R^k_+,\ 0\le z\le x\Bigr\}.
--   $$
--
--   With $\tilde\xi$ uniformly distributed on $[0,1]^k$, **problem (9)** is
--
--   $$
--   f^\star=\max\Bigl\{-cx+\mathbb E\bigl[Q(x,\tilde\xi;\alpha,\beta)\bigr]:\ x\in[0,1]\Bigr\}.
--   $$
--
--   A decision $x$ is **$\epsilon$-optimal** if it is feasible, $x\in[0,1]$, and
--
--   $$
--   \frac{\bigl|f^\star-\bigl(-cx+\mathbb E[Q(x,\tilde\xi;\alpha,\beta)]\bigr)\bigr|}{\max\{|f^\star|,1\}}\le\epsilon .
--   $$
--
--   Problem (9) is the instance of the general two-stage program (1) whose recourse is fixed and whose expected recourse is a multiple of the expected recourse value $\mathcal Q(\alpha,\beta)$ of problem (2); Theorem 2 concerns the difficulty of finding its $\epsilon$-optimal decisions.
--
--   **Formalization Note** The uniform law is Lebesgue measure on the unit cube $[0,1]^k$ (the published base definition `cube`), which has volume one, so $\mathbb E[\cdot]$ is the integral over the cube. Both optimal values are real suprema. For $x\in[0,1]$ and $\xi\in[0,1]^k$ the second-stage feasible set contains $y=0,z=0$ and its objective is bounded above, and the first-stage objective is bounded on $[0,1]$, so the suprema are the optimal values; $\epsilon$-optimality requires $x\in[0,1]$, so the value of $Q$ at an infeasible $x$ is never used.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 8, definition of an ϵ-optimal solution and problem (9); p. 9, the second-stage problem of (9)

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

namespace SPHardness.FixedRecourse.Supplement

noncomputable section
open MeasureTheory

/-- The optimal value `Q(x, ξ; α, β)` of the second-stage problem of (9) (Hanasusanto–Kuhn–Wiesemann,
p. 9): maximize `ξᵀy − βz` subject to `y ≤ αz`, `y ∈ ℝᵏ₊`, `0 ≤ z ≤ x`. For `x ∈ [0, 1]` and
`ξ ∈ [0, 1]ᵏ` the feasible set is nonempty (`y = 0`, `z = 0`) and the objective is bounded above,
so the real `sSup` is the optimal value. -/
def secondStageValue9 {k : ℕ} (α : Fin k → ℝ) (β x : ℝ) (ξ : Fin k → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (y : Fin k → ℝ) (z : ℝ),
    (∀ j, 0 ≤ y j) ∧ (∀ j, y j ≤ α j * z) ∧
    0 ≤ z ∧ z ≤ x ∧ v = (∑ j, ξ j * y j) - β * z}

/-- The expected recourse `E[Q(x, ξ̃; α, β)]` with `ξ̃` uniform on `[0, 1]ᵏ` (Lebesgue measure on the
published unit cube, which has volume one). -/
def expRecourse9 {k : ℕ} (α : Fin k → ℝ) (β x : ℝ) : ℝ :=
  ∫ ξ in cube k, secondStageValue9 α β x ξ

/-- The first-stage objective of (9): `−c x + E[Q(x, ξ̃; α, β)]`. -/
def objective9 {k : ℕ} (α : Fin k → ℝ) (β c x : ℝ) : ℝ :=
  -c * x + expRecourse9 α β x

/-- The optimal value `f⋆` of (9): the supremum of the objective over the feasible set `x ∈ [0, 1]`
(nonempty and compact; the objective is bounded on it). -/
def optValue9 {k : ℕ} (α : Fin k → ℝ) (β c : ℝ) : ℝ :=
  sSup (objective9 α β c '' Set.Icc (0 : ℝ) 1)

/-- `x` is an **ε-optimal decision** of (9) (p. 8): `x` is feasible, `x ∈ [0, 1]`, and
`|f⋆ − (−c x + E[Q(x, ξ̃)])| / max{|f⋆|, 1} ≤ ε`. -/
def IsEpsOptimal9 {k : ℕ} (α : Fin k → ℝ) (β c ε x : ℝ) : Prop :=
  x ∈ Set.Icc (0 : ℝ) 1 ∧
    |optValue9 α β c - objective9 α β c x| / max (|optValue9 α β c|) 1 ≤ ε

end

end SPHardness.FixedRecourse.Supplement


