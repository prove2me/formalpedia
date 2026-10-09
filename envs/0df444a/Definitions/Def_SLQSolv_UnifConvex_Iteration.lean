-- Prove2me | Definitions.Def_SLQSolv_UnifConvex_Iteration
-- name    : SLQSolv_UnifConvex_Iteration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:41.444982+00:00
-- url     : https://prove2.me/theorems/b9f51df2-e151-417a-8358-74564cadb5e7
-- title:
--   (4.19), p. 2288 — the feedback Θ = −(R + DᵀPD)⁻¹(BᵀP + DᵀPC + S) attached to P
-- statement:
--   For a matrix function $P:[0,T]\to\mathbb S^n$ define the feedback
--
--   $$\Theta_P=-(R+D^\top PD)^{-1}(B^\top P+D^\top PC+S).$$
--
--   With $P=P_i$ this is the gain $\Theta_i$ of the iteration (4.18)–(4.19) in the proof of Theorem 4.5; with the strongly regular solution $P$ of (4.6) it is the optimal feedback $\Theta$ of p. 2290.
--
--   **Formalization Note** The page prints the inverse. Lean's matrix inverse is $0$ on a singular matrix; that value is never reached where the paper uses $\Theta_P$, because there $R+D^\top PD\ge\lambda I$ with $\lambda>0$.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), (4.19) p. 2288 and p. 2290

import Mathlib
import Definitions.Def_SLQSolv_UnifConvex_Riccati

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.UnifConvex

variable {Ω : Type*} {n m : ℕ}

/-- The feedback `Θ = −(R + DᵀPD)⁻¹(BᵀP + DᵀPC + S)` attached to a matrix function `P`, as in
(4.19) (with `P = Pᵢ`, giving `Θᵢ`) and on p. 2290 (with the strongly regular solution `P`).
The page prints the inverse `⁻¹`; Lean's matrix inverse is `0` on a singular matrix, a value
never reached where the paper uses `Θ` (there `R + DᵀPD ≥ λI` with `λ > 0`). -/
noncomputable def thetaOf (d : Data Ω n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) :
    Matrix (Fin m) (Fin n) ℝ :=
  -((sigmaR d P s)⁻¹ * gainK d P s)

end SLQSolv.UnifConvex


