-- Prove2me | Definitions.Def_GeomDRSub_cube
-- name    : GeomDRSub_cube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:08.007052+00:00
-- url     : https://prove2.me/theorems/82b7fddd-51c5-419e-89d5-60fe73c91057
-- title:
--   The cube $Q=[0,1]^d$
-- statement:
--   The **cube** is the set
--   $$
--   Q=[0,1]^d=\{y\in\mathbb R^d:\ 0\le y_i\le 1\ \text{for every } i\in[d]\}.
--   $$
--   It is the domain of every objective in the paper, and the feasible sets $K$ are subsets of it.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with the Euclidean inner product and norm; coordinates are indexed by `Fin d`, from $0$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 3.1, p.8

import Mathlib

namespace GeomDRSub

/-- **The cube `Q = [0,1]^d`.** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation
for Non-Monotone DR-Submodular Maximization*, arXiv:2610.00545, Section 3.1, p.8: "Let
`Q = [0, 1]^d` denote the cube".

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)` (Euclidean inner product and norm, as
on p.8). It carries no order instance, so the coordinatewise inequalities are written out.
Coordinates are indexed by `Fin d` (0-based). -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {y | ∀ i, 0 ≤ y i ∧ y i ≤ 1}

end GeomDRSub


