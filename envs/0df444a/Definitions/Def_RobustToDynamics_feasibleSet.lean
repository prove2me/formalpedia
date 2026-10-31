-- Prove2me | Definitions.Def_RobustToDynamics_feasibleSet
-- name    : RobustToDynamics_feasibleSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:18.350433+00:00
-- url     : https://prove2.me/theorems/b686a803-0054-4ebf-94b2-8589008759c8
-- title:
--   The feasible set $\mathcal S=\bigcap_{k\ge0}\{x : AG^kx\le b\}$ of an R-LD-LP
-- statement:
--   For $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $G\in\mathbb R^{n\times n}$, the feasible set of the robust-to-dynamics linear program is
--   $$
--   \mathcal S=\bigcap_{k=0}^{\infty}\{x\in\mathbb R^n : AG^kx\le b\},
--   $$
--   the set of initial states $x_0$ whose whole trajectory $x_{k+1}=Gx_k$ stays in $P=\{x: Ax\le b\}$. This is display (2.3), the feasible set of (2.1)–(2.2).
--
--   **Formalization Note** $k$ ranges over all natural numbers; $\mathbb R^n$ is `Fin n → ℝ`.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, §2, (2.3), p.6

import Mathlib

open Matrix

namespace RobustToDynamics

/-- **The feasible set `S` of an R-LD-LP.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, §2, (2.3), p.6:
"S := ⋂_{k=0}^{∞} {x ∈ Rn| AGk x ≤ b}".

`feasibleSet A b G` is the set of initial points `x` whose whole trajectory `x, Gx, G²x, …` stays in
`P = {x | Ax ≤ b}`, i.e. the feasible set of (2.1)/(2.2).

**Formalization Note.** `ℝⁿ` is `Fin n → ℝ`, `k` ranges over all of `ℕ` (k = 0, 1, 2, …), and
`A Gᵏ x ≤ b` is componentwise. -/
def feasibleSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ k : ℕ, (A * G ^ k) *ᵥ x ≤ b}

end RobustToDynamics


