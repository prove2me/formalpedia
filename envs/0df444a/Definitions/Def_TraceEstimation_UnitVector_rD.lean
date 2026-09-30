-- Prove2me | Definitions.Def_TraceEstimation_UnitVector_rD
-- name    : TraceEstimation_UnitVector_rD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:35:05.068225+00:00
-- url     : https://prove2.me/theorems/042ce40d-83e4-47ba-b882-822cb9ab819a
-- title:
--   Theorem 8.2 — $r_D(A) = n\cdot\max_i A_{ii}/\mathrm{trace}(A)$
-- statement:
--   For a square matrix $A \in \mathbb{R}^{n\times n}$ with $n \ge 1$, let $\max_i A_{ii}$ be its largest diagonal entry and define
--
--   $$r_D(A) = \frac{n\cdot\max_i A_{ii}}{\mathrm{trace}(A)} .$$
--
--   For a positive semi-definite $A \ne 0$ one has $1 \le r_D(A) \le n$. Since a single sample of the unit vector estimator takes values in $[0, n\max_i A_{ii}]$, the ratio $r_D(A)$ measures the range of a sample relative to the quantity being estimated; the sample bound of Theorem 8.2 grows with $r_D^2(A)$.
--
--   **Formalization Note** `maxDiag A` is `Finset.sup'` of the diagonal over the nonempty index set, with the placeholder value $0$ when $n = 0$. `rD A` uses Lean's real division, which returns $0$ when $\mathrm{trace}(A) = 0$; for a positive semi-definite matrix this happens only for $A = 0$, where every statement of the mission holds trivially.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:12, Theorem 8.2 (definition of r_D)

import Mathlib

namespace TraceEstimation.UnitVector

/-- The largest diagonal entry `max_i A_ii` of a square real matrix. For `n = 0` (no diagonal
entries) the value is the placeholder `0`. -/
noncomputable def maxDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin n)).Nonempty then Finset.univ.sup' h (fun i => A i i) else 0

/-- `r_D(A) = n · max_i A_ii / trace(A)` (Avron–Toledo, Theorem 8.2, p. 8:12): the ratio of the
largest value a single unit vector sample can take to the trace. When `trace(A) = 0` Lean's
division returns `0`. -/
noncomputable def rD {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (n : ℝ) * maxDiag A / A.trace

end TraceEstimation.UnitVector


