-- Prove2me | Definitions.Def_RobustToDynamics_IsMinimizer
-- name    : RobustToDynamics_IsMinimizer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:17.757556+00:00
-- url     : https://prove2.me/theorems/aa5f2d9b-221f-4d93-a5b3-92e6084e9892
-- title:
--   Optimal solution of $\min\{c^Tx : x\in K\}$
-- statement:
--   For $c\in\mathbb R^n$ and a set $K\subseteq\mathbb R^n$, a point $x$ is an **optimal solution** of
--   $$
--   \min\{c^Ty : y\in K\}
--   $$
--   if $x\in K$ and $c^Tx\le c^Ty$ for every $y\in K$. It is used with $K=\mathcal S$ (the R-LD-LP (2.2)) and with $K$ a polyhedron (a linear program).
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, §2, (2.1)–(2.2), p.5; p.13

import Mathlib

open Matrix

namespace RobustToDynamics

/-- **Optimal solution of a linear objective over a set.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, §2, (2.1)–(2.2), p.5
(`min {cᵀx : x ∈ S}`), and p.13 (optimal solutions of linear programs).

`IsMinimizer c K x` says that `x ∈ K` and `cᵀx ≤ cᵀy` for every `y ∈ K`, i.e. `x` is an optimal
solution of `min {cᵀy : y ∈ K}`.

**Formalization Note.** `ℝⁿ` is `Fin n → ℝ` and `cᵀx` is `c ⬝ᵥ x`. -/
def IsMinimizer {n : ℕ} (c : Fin n → ℝ) (K : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  x ∈ K ∧ ∀ y ∈ K, c ⬝ᵥ x ≤ c ⬝ᵥ y

end RobustToDynamics


