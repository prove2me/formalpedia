-- Prove2me | Definitions.Def_NieYangPareto_MOP
-- name    : NieYangPareto_MOP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:18.37538+00:00
-- url     : https://prove2.me/theorems/7c48b985-11c4-487c-8643-ae3d56152178
-- title:
--   The multi-objective polynomial optimization problem (1.1), its feasible set $K$ and objective vector $f$
-- statement:
--   A **multi-objective polynomial optimization problem** is the problem
--
--   $$
--   \min\ f(x):=(f_1(x),\dots,f_m(x))\quad\text{s.t.}\quad c_i(x)=0\ (i\in\mathcal E),\quad c_j(x)\ge 0\ (j\in\mathcal I),
--   $$
--
--   where all $f_i,c_i,c_j$ are polynomials in $x\in\mathbb R^n$ with real coefficients and $\mathcal E$, $\mathcal I$ are disjoint finite label sets. The **feasible set** is $K=\{x\in\mathbb R^n: c_i(x)=0\ (i\in\mathcal E),\ c_j(x)\ge0\ (j\in\mathcal I)\}$, and the image of $K$ under the objective vector is $f(K)=\{f(x):x\in K\}$.
--
--   This is the data of every statement in the mission.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`. The disjoint label sets are two separate types `E`, `I`, either of which may be empty; every theorem of the mission assumes both finite. The image $f(K)$ is `P.obj '' P.K`.
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, eq. (1.1), p.1; f(K) on p.6

import Mathlib

namespace NieYangPareto

open MvPolynomial

/-- **The multi-objective polynomial optimization problem (1.1).**
Nie–Yang, *The multi-objective polynomial optimization*, arXiv:2108.04336v2, eq. (1.1), p.1:
minimize `f(x) = (f₁(x), …, f_m(x))` subject to `c_i(x) = 0 (i ∈ ℰ)`, `c_j(x) ≥ 0 (j ∈ ℐ)`, where
all functions are polynomials in `x ∈ ℝⁿ` and `ℰ`, `ℐ` are disjoint finite label sets.

**Formalization Note** `ℝⁿ` is `Fin n → ℝ`. The disjoint label sets are two separate types `E`, `I`,
which encodes disjointness; every theorem of the mission assumes `[Finite E] [Finite I]`. Either may
be empty. -/
structure MOP (n m : ℕ) (E I : Type*) where
  /-- The objectives `f₁, …, f_m`. -/
  f : Fin m → MvPolynomial (Fin n) ℝ
  /-- The equality constraints `c_i`, `i ∈ ℰ`. -/
  cEq : E → MvPolynomial (Fin n) ℝ
  /-- The inequality constraints `c_j`, `j ∈ ℐ`. -/
  cIn : I → MvPolynomial (Fin n) ℝ

variable {n m : ℕ} {E I : Type*}

/-- The feasible set `K` of (1.1): Nie–Yang, arXiv:2108.04336v2, eq. (1.1), p.1. -/
def MOP.K (P : MOP n m E I) : Set (Fin n → ℝ) :=
  {x | (∀ i, eval x (P.cEq i) = 0) ∧ ∀ j, 0 ≤ eval x (P.cIn j)}

/-- The objective vector `f(x) = (f₁(x), …, f_m(x))`: Nie–Yang, arXiv:2108.04336v2, eq. (1.1), p.1.
The image `f(K)` of p.6 is `P.obj '' P.K`. -/
noncomputable def MOP.obj (P : MOP n m E I) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => eval x (P.f i)

end NieYangPareto


