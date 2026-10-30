-- Prove2me | Definitions.Def_LogRegretOCO_ONS_qform
-- name    : LogRegretOCO_ONS_qform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:56:45.765974+00:00
-- url     : https://prove2.me/theorems/ba1371e4-2ed6-4b26-976c-e564413b9911
-- title:
--   Quadratic form $v^\top A v$
-- statement:
--   For a real $n \times n$ matrix $A$ and a vector $v \in \mathbb R^n$, the **quadratic form** of $A$ at $v$ is
--   $$
--   v^\top A v = \sum_{i,j=1}^n v_i A_{ij} v_j .
--   $$
--   It is the expression $(y - x)^\top A (y - x)$ minimized by the generalized projection of Online Newton Step and the one compared in Lemma 8 and in the analysis of Theorem 2.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin n)`; the matrix acts on their coordinate vectors (`WithLp.ofLp`).
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, Fig. 2, p. 176 (PDF p. 8); eq. (6), p. 177; Lemma 8, p. 188

import Mathlib
open Matrix

namespace LogRegretOCO.ONS

/-- **The quadratic form `vᵀ A v`.**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, notation of Fig. 2, p. 176 (`(y − x)ᵀA_{t−1}(y − x)`), of (6), p. 177, and of
Lemma 8, p. 188 (`(y − a)ᵀA(y − a)`).

`qform A v` is `vᵀ A v = Σ_{i,j} v_i A_{ij} v_j` for a real `n × n` matrix `A` and a vector
`v ∈ ℝⁿ`.

**Formalization Note.** Points of `ℝⁿ` live in `EuclideanSpace ℝ (Fin n)` (Euclidean norm);
`WithLp.ofLp` gives the underlying coordinate vector, on which the matrix acts. -/
def qform {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp v)

end LogRegretOCO.ONS


