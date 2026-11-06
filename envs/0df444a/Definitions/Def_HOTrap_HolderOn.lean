-- Prove2me | Definitions.Def_HOTrap_HolderOn
-- name    : HOTrap_HolderOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:45:55.068671+00:00
-- url     : https://prove2.me/theorems/be6962e6-4a46-4f24-8a36-07dc376fd7b2
-- title:
--   $F\in C^{p,\beta}(L)$ on an open set $U$
-- statement:
--   For an integer $p\ge0$, $\beta\in(0,1]$ and $L\ge0$, a map $F$ from $\mathbb R^d$ to a normed space is in $C^{p,\beta}(L)$ on the open set $U$ if it is $p$ times continuously differentiable on $U$ and
--   $$
--   \|D^pF(x)-D^pF(y)\|\le L\|x-y\|_2^\beta\qquad\text{for all }x,y\in U.
--   $$
--
--   This is the local form of the Hölder class, used for scalar and vector maps in Appendix A.
--
--   **Formalization Note** $U$ is open, so `iteratedFDeriv` at points of $U$ is the true derivative.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Appendix A, Notation, p.53

import Mathlib

namespace HOTrap

/-- **`F ∈ C^{p,β}(L)` on an open set `U`.** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Appendix A, Notation, p.53: for an integer
`p ≥ 0`, `F` is `p` times continuously differentiable and `∥D^p F(x) − D^p F(y)∥ ≤ L ∥x − y∥₂^β`.

**Formalization Note** `F` takes values in a real normed space `G`, which covers the paper's "scalar- or
vector-valued" maps. `U` is open, so `iteratedFDeriv` at points of `U` is the true derivative. The
Hölder inequality is required on all of `U`, as in "All regularity assumptions hold on a neighborhood
of `S`". -/
def HolderOn {d : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (U : Set (EuclideanSpace ℝ (Fin d))) (p : ℕ) (β L : ℝ) (F : EuclideanSpace ℝ (Fin d) → G) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ p F U ∧
    ∀ x ∈ U, ∀ y ∈ U, ‖iteratedFDeriv ℝ p F x - iteratedFDeriv ℝ p F y‖ ≤ L * ‖x - y‖ ^ β

end HOTrap


