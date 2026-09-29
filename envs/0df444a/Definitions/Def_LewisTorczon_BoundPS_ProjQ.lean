-- Prove2me | Definitions.Def_LewisTorczon_BoundPS_ProjQ
-- name    : LewisTorczon_BoundPS_ProjQ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:41:40.073921+00:00
-- url     : https://prove2.me/theorems/9d2bf1a7-ac64-4208-94bd-dfde3fcfcfa9
-- title:
--   The stationarity measure $q(x)=P(x-g(x))-x$ and stationary points of the bound constrained problem
-- statement:
--   Let $\Omega$ be the box $\{\ell\le x\le u\}$ and $P$ the projection onto it, and write $g(x)=\nabla f(x)$ for the gradient of the objective $f:\mathbb R^n\to\mathbb R$.
--
--   1. **Stationarity measure.** For $x\in\mathbb R^n$,
--   $$q(x)=P\bigl(x-g(x)\bigr)-x .$$
--   2. **Stationary point.** A point $x$ is a stationary point of the problem $\min\{f(x):x\in\Omega\}$ if $x\in\Omega$ and
--   $$\langle g(x),\,z-x\rangle\ge 0\qquad\text{for all } z\in\Omega .$$
--
--   In the bound constrained theory, $\|q(x)\|$ plays the role that $\|g(x)\|$ plays in unconstrained minimization: it vanishes exactly at stationary points and is the quantity the convergence theorems drive to zero.
--
--   **Formalization Note** The gradient is Mathlib's `gradient f x`, which equals $0$ at points where $f$ is not differentiable. The theorems of the mission assume $f$ is continuously differentiable on an open set containing $\Omega$, so on $\Omega$ this is the true gradient. The paper defines $q$ only for feasible $x$; the Lean function is total, and every statement evaluates it at feasible points.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 1 (§1, stationary point) and p. 5 (§3, definition of q(x))

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box

namespace LewisTorczon.BoundPS

/-- The stationarity measure `q(x) = P(x − g(x)) − x` of §3, p. 5, where `g = ∇f` is Mathlib's
`gradient f` (which is `0` where `f` is not differentiable; the theorems assume `f` is `C¹` on an
open set containing `Ω`, so there it is the true gradient). -/
noncomputable def projQ {n : ℕ} (lo hi : Fin n → EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  boxProj lo hi (x - gradient f x) - x

/-- A stationary point of problem (1) (p. 1): a feasible `x` with `⟨∇f(x), z − x⟩ ≥ 0` for every
feasible `z`. -/
def IsStationary {n : ℕ} (lo hi : Fin n → EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ box lo hi ∧ ∀ z ∈ box lo hi, 0 ≤ inner ℝ (gradient f x) (z - x)

end LewisTorczon.BoundPS


