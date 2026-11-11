-- Prove2me | Definitions.Def_L1ResistanceCount_Counting_Obstacle
-- name    : L1ResistanceCount_Counting_Obstacle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:08:59.633369+00:00
-- url     : https://prove2.me/theorems/0815b501-dfa3-41a9-9f3f-4ee6c1d44e6a
-- title:
--   Obstacle objective, optimizer, residual, and threshold rounding
-- statement:
--   For a connected positive-weight graph with Laplacian $L$, source $s$ and regularization parameter $\lambda$, the constrained objective is
--
--   $$\Phi_s(z)=\tfrac12z^\top Lz-z_s+\lambda\sum_v z_v,\qquad z\ge0.$$
--
--   The minimizer predicate expresses global optimality over all nonnegative vectors. The mathematical potential $z_s^*$ is chosen only if there is exactly one minimizer; its total default is zero otherwise. Lemma 3.1 separately asserts existence and uniqueness for $1/n<\lambda<1/2$. This mathematical choice is absent from the RAM instruction set.
--
--   The residual is $q_s=e_s-Lz_s$, and $R^\lambda_{s,t}=(e_s-e_t)^\top(z_s^*-z_t^*)$. Support means nonzero coordinates. Weighted degree and maximum degree are defined from the edges. Threshold rounding keeps $x_v$ exactly when $x_v>2\xi$ and sets it to zero otherwise, including the equality case. These definitions are shared by the source statements rather than rebuilt separately for each theorem.
-- source:
--   Rong-Hua Li, Yichun Yang, STOC 2027 submission #881 (October 2026), Definition 1.3 p.2, §3 and Lemma 3.1 pp.4–5, Lemma 3.8 p.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/881.pdf

import Mathlib
import Definitions.Def_L1ResistanceCount_Counting_Graph

open scoped BigOperators

namespace L1ResistanceCount.Counting

abbrev Vector (n : ℕ) := Fin n → ℝ

def dot {n : ℕ} (x y : Vector n) : ℝ := ∑ v, x v * y v

def unitVector {n : ℕ} (s : Fin n) : Vector n := fun v => if v = s then 1 else 0

def differenceVector {n : ℕ} (s t : Fin n) : Vector n := unitVector s - unitVector t

def quadratic {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (x : Vector n) : ℝ :=
  dot x (L.mulVec x)

def nonnegative {n : ℕ} (x : Vector n) : Prop := ∀ v, 0 ≤ x v

noncomputable def support {n : ℕ} (x : Vector n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => x v ≠ 0)

/-- The source's constrained quadratic objective, including its linear term. -/
noncomputable def obstacleObjective {n m : ℕ} (G : WeightedGraph n m) (lam : ℝ)
    (s : Fin n) (z : Vector n) : ℝ :=
  quadratic G.laplacian z / 2 - z s + lam * ∑ v, z v

def IsObstacleMinimizer {n m : ℕ} (G : WeightedGraph n m) (lam : ℝ)
    (s : Fin n) (z : Vector n) : Prop :=
  nonnegative z ∧ ∀ y, nonnegative y → obstacleObjective G lam s z ≤ obstacleObjective G lam s y

/-- The mathematical optimizer, chosen only if it exists uniquely. Its total default
outside that domain is zero; Lemma 3.1 separately asserts existence and uniqueness.
This choice is not an instruction of the arithmetic RAM. -/
noncomputable def obstaclePotential {n m : ℕ} (G : WeightedGraph n m) (lam : ℝ)
    (s : Fin n) : Vector n := by
  classical
  exact if h : ∃! z, IsObstacleMinimizer G lam s z then h.exists.choose else 0

def residual {n m : ℕ} (G : WeightedGraph n m) (s : Fin n) (z : Vector n) : Vector n :=
  unitVector s - G.laplacian.mulVec z

noncomputable def exactResidual {n m : ℕ} (G : WeightedGraph n m) (lam : ℝ) (s : Fin n) : Vector n :=
  residual G s (obstaclePotential G lam s)

noncomputable def regularizedResistance {n m : ℕ} (G : WeightedGraph n m)
    (lam : ℝ) (s t : Fin n) : ℝ :=
  dot (differenceVector s t) (obstaclePotential G lam s - obstaclePotential G lam t)

def degree {n m : ℕ} (G : WeightedGraph n m) (v : Fin n) : ℝ :=
  ∑ e, if G.head e = v ∨ G.tail e = v then G.w e else 0

/-- Zero on an empty vertex type; all source uses assume connectedness. -/
noncomputable def maximumDegree {n m : ℕ} (G : WeightedGraph n m) : ℝ :=
  sSup (Set.range (degree G))

/-- Thresholding is a genuine coordinate formula, rather than a vector assumed to
satisfy the rounding theorem. The equality case is discarded. -/
noncomputable def roundedPotential {n : ℕ} (x : Vector n) (ξ : ℝ) : Vector n :=
  fun v => if 2 * ξ < x v then x v else 0

end L1ResistanceCount.Counting


