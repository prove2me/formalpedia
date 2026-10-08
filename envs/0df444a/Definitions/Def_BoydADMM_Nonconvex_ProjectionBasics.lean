-- Prove2me | Definitions.Def_BoydADMM_Nonconvex_ProjectionBasics
-- name    : BoydADMM_Nonconvex_ProjectionBasics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:58.247026+00:00
-- url     : https://prove2.me/theorems/1afe5f01-00ae-4929-b23c-f075a094d474
-- title:
--   Sparse and Boolean vector sets and squared Euclidean distance
-- statement:
--   For a finite vector $x\in\mathbb R^n$, $\operatorname{card}(x)$ counts its nonzero entries. The cardinality-constrained set and the Boolean cube are
--
--   $$S_c=\{x:\operatorname{card}(x)\le c\},\qquad B=\{x:x_i\in\{0,1\}\text{ for every }i\}.$$
--
--   For a chosen index set $I$, retaining the entries of $v$ in $I$ and setting all others to zero defines a sparse vector. Rounding each entry of $v$ to a closest element of $\{0,1\}$ defines a Boolean vector; at the tie $v_i=1/2$, the definition chooses zero. Squared Euclidean distance is $\sum_i(x_i-v_i)^2$.
--
--   These objects state the two exact projections listed in §9.1.
--
--   **Formalization Note** `Fin n` is the coordinate type; `cardinality` uses the finite support. Ties may give multiple nearest points, so the theorems claim that the specified choice is a nearest point.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 74, §9.1, Cardinality and Boolean constraints bullets

import Mathlib

namespace BoydADMM.Nonconvex

/-- Number of nonzero entries in a finite real vector (§9.1, p. 74). -/
noncomputable def cardinality {n : ℕ} (x : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- The cardinality-constrained set `{x | card(x) ≤ c}`. -/
noncomputable def sparseSet {n : ℕ} (c : ℕ) : Set (Fin n → ℝ) :=
  {x | cardinality x ≤ c}

/-- The vector obtained by retaining entries in `I` and zeroing the rest. -/
def restrictTo {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ I then v i else 0

/-- Squared Euclidean distance for finite real vectors. -/
def sqDist {n : ℕ} (x v : Fin n → ℝ) : ℝ :=
  ∑ i, (x i - v i) ^ 2

/-- The coordinatewise Boolean constraint set. -/
def booleanSet {n : ℕ} : Set (Fin n → ℝ) :=
  {x | ∀ i, x i = 0 ∨ x i = 1}

/-- Rounding to a nearest Boolean value, choosing zero at a tie. -/
noncomputable def roundBoolean {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if v i ≤ 1 / 2 then 0 else 1

end BoydADMM.Nonconvex


