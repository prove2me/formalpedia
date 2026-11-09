-- Prove2me | Definitions.Def_QMatVecLB_ConvexOpt_GridOracle
-- name    : QMatVecLB_ConvexOpt_GridOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:03:15.080421+00:00
-- url     : https://prove2.me/theorems/b2ec18ce-e2f4-4de4-b593-92b59121c123
-- title:
--   Discretized real grids and exact phase oracles
-- statement:
--   For $k\ge1$, the grid has integer numerators from $-2^{2k-1}+1$ through $2^{2k-1}-1$, divided by $2^k$. Matrix queries on a grid pair $(x,y)$ multiply the basis state by $e^{2\pi i y^TAx}$. Function queries use $e^{2\pi i y f(x)}$ in the supplied region and act as the identity outside. The module also distinguishes coordinate sup norms from Euclidean vectors and defines the matrix pairing and rank variety. No function or matrix value is rounded by these oracles.
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, definitions in Sections 2–3, 5–6; anchor PDF p. 5 (printed p. 4).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_QueryCircuit

noncomputable section

namespace QMatVecLB.ConvexOpt
open scoped BigOperators Matrix Matrix.Norms.Elementwise

abbrev RMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
instance rMatMeasurableSpace (n : ℕ) : MeasurableSpace (RMat n) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))

abbrev RVec (n : ℕ) := EuclideanSpace ℝ (Fin n)
/-- Section 2: integer numerators in increasing order, for k ≥ 1. -/
abbrev Grid (k : ℕ) := Fin (2 ^ (2 * k) - 1)
def gridValue {k : ℕ} (a : Grid k) : ℝ :=
  ((a.val : ℤ) - ((2 : ℤ) ^ (2 * k - 1) - 1) : ℤ) / (2 : ℝ) ^ k
abbrev GridVec (n k : ℕ) := Fin n → Grid k
def gridVec {n k : ℕ} (x : GridVec n k) : RVec n :=
  WithLp.toLp 2 (fun i => gridValue (x i))
abbrev MatQuery (n k : ℕ) := GridVec n k × GridVec n k
abbrev FunQuery (n k : ℕ) := GridVec n k × Grid k

def phaseExp (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)
/-- Exact real phase; no rounding of the value of A. -/
def matPhase {n k : ℕ} (A : RMat n) (q : MatQuery n k) : ℂ :=
  phaseExp (∑ i, ∑ j, gridValue (q.2 i) * A i j * gridValue (q.1 j))
def unitBall (n : ℕ) : Set (RVec n) := {x | ‖x‖ ≤ 1}
/-- Section 2 function oracle: identity outside the supplied query region. -/
def funPhase {n k : ℕ} (K : Set (RVec n)) (f : RVec n → ℝ) (q : FunQuery n k) : ℂ := by
  classical
  exact if gridVec q.1 ∈ K then phaseExp (gridValue q.2 * f (gridVec q.1)) else 1

def maxNorm {n : ℕ} (A : RMat n) : ℝ := ‖A‖
def supNorm {n : ℕ} (x : Fin n → ℝ) : ℝ := ‖x‖
def euclideanMul {n : ℕ} (A : RMat n) (x : RVec n) : RVec n :=
  WithLp.toLp 2 (A *ᵥ (fun i => x i))
def matrixPair {n : ℕ} (A M : RMat n) : ℝ := ∑ i, ∑ j, A i j * M i j

def rankVariety (n r : ℕ) : Set (RMat n) := {M | Matrix.rank M ≤ r}

end QMatVecLB.ConvexOpt
end


