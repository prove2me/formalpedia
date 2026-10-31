-- Prove2me | Definitions.Def_StengelZeroSum_Feasible53
-- name    : StengelZeroSum_Feasible53
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:50.182011+00:00
-- url     : https://prove2.me/theorems/b8cf3d9e-a29e-47ec-8cc7-34940dda9f8a
-- title:
--   Feasibility of the relaxed LPs (53) at slack $w$
-- statement:
--   For a real $m\times n$ matrix $A$, $b\in\mathbb R^m$, $c\in\mathbb R^n$ and $w\in\mathbb R$, the system (53) **has feasible solutions at $w$** if there are $\bar x\in\mathbb R^n$ and $\bar y\in\mathbb R^m$ with
--
--   $$
--   A\bar x\le b+\mathbf 1w,\qquad \bar x\ge\mathbf 0,\qquad -A^\top\bar y\le -c+\mathbf 1w,\qquad \bar y\ge\mathbf 0 .
--   $$
--
--   At $w=0$ this says that the primal LP (1) and the dual LP (2) are both feasible; $w$ is the constant added as extra slack to all right-hand sides.
--
--   **Formalization Note** $w$ ranges over all real numbers; the source puts no sign condition on it.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 7(b), eq. (53), p.18

import Mathlib

open Matrix

namespace StengelZeroSum

/-- The relaxed system (53) **has feasible solutions at `w`**,
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 7(b),
eq. (53), p.18: there are `x̄ ∈ ℝ^n`, `ȳ ∈ ℝ^m` with
`Ax̄ ≤ b + 1w,  x̄ ≥ 0,  −A⊤ȳ ≤ −c + 1w,  ȳ ≥ 0`.

**Formalization Note** `w` ranges over all of `ℝ` (the page puts no sign condition on it);
`1w` is the constant vector `fun _ => w`, and vector inequalities are componentwise. -/
def Feasible53 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (w : ℝ) : Prop :=
  ∃ (x : Fin n → ℝ) (y : Fin m → ℝ),
    A *ᵥ x ≤ b + (fun _ => w) ∧ 0 ≤ x ∧ -(Aᵀ *ᵥ y) ≤ -c + (fun _ => w) ∧ 0 ≤ y

end StengelZeroSum


