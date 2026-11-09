-- Prove2me | Definitions.Def_QMatVecLB_ConvexOpt_Optimization
-- name    : QMatVecLB_ConvexOpt_Optimization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:08:27.925917+00:00
-- url     : https://prove2.me/theorems/4b4d047d-e1e3-4235-b79e-77d2869c3acc
-- title:
--   Quadratic function class and optimization success
-- statement:
--   A quadratic is one half of a symmetric quadratic form plus an arbitrary linear form and constant. On the Euclidean unit ball $K$, the function class requires Lipschitz constant 1, absolute value at most 1, and global strong-convexity modulus $1/(10n^{14})$. A successful point belongs to $K$ and has objective value within $1/(720n^{49})$ of every comparator in $K$. Continuity and compactness make this equivalent to the minimum-gap condition of Corollary 6.9. These predicates specify mathematical input and output properties; the probability of meeting them is computed separately by the query circuit.
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, definitions in Sections 2–3, 5–6; anchor PDF p. 27 (printed p. 26).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_GridOracle

noncomputable section

namespace QMatVecLB.ConvexOpt
open scoped BigOperators Matrix Matrix.Norms.Elementwise

/-- Degree at most two, with arbitrary symmetric quadratic, linear and constant terms. -/
def IsQuadratic {n : ℕ} (f : RVec n → ℝ) : Prop :=
  ∃ (Q : RMat n) (b : RVec n) (c : ℝ), Q.IsSymm ∧
    ∀ x, f x = (1 / 2 : ℝ) * (∑ i, ∑ j, x i * Q i j * x j) + (∑ i, b i * x i) + c

/-- Exactly the four properties of the function class in Corollary 6.9. -/
def FunctionClass (n : ℕ) (f : RVec n → ℝ) : Prop :=
  IsQuadratic f ∧ LipschitzOnWith 1 f (unitBall n) ∧
    StrongConvexOn Set.univ (1 / (10 * (n : ℝ)^14)) f ∧
    ∀ x ∈ unitBall n, |f x| ≤ 1

/-- All-point comparison equals the minimum-gap assertion on the compact ball. -/
def optimizerSuccess {n : ℕ} (f : RVec n → ℝ) (x : RVec n) : Prop :=
  x ∈ unitBall n ∧ ∀ z ∈ unitBall n, f x - f z ≤ 1 / (720 * (n : ℝ)^49)

end QMatVecLB.ConvexOpt
end


