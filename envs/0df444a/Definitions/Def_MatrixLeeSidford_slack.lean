-- Prove2me | Definitions.Def_MatrixLeeSidford_slack
-- name    : MatrixLeeSidford_slack
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:13.582303+00:00
-- url     : https://prove2.me/theorems/13a3276a-b087-4864-be42-035735e58551
-- title:
--   Dual slack $S(y)=\sum_i y_iA_i-C$
-- statement:
--   Given real $n\times n$ matrices $A_1,\dots,A_m$ and $C$, the **dual slack** at $y\in\mathbb R^m$ is
--   $$
--   S(y)=\sum_{i=1}^m y_iA_i-C .
--   $$
--   The dual SDP (1.2) minimizes $b^\top y$ subject to $S(y)\succeq0$; Part I of the paper only uses the pencil $y\mapsto S(y)$.
--
--   **Formalization Note** $y$ lives in `EuclideanSpace ℝ (Fin m)`. Symmetry of the $A_i$ and of $C$ is a hypothesis of each theorem.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Eq. (1.2), p.4

import Mathlib

open Matrix

namespace MatrixLeeSidford

/-- The dual slack `S(y) := ∑ᵢ yᵢ Aᵢ − C` of the SDP pair (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Eq. (1.2), p.4).

**Formalization Note** The dual variable `y` lives in `EuclideanSpace ℝ (Fin m)` (so that `ℝᵐ`
carries its Euclidean norm), the coefficients `Aᵢ` and `C` are real `n × n` matrices; symmetry
of `Aᵢ` and `C` is a hypothesis of each theorem, not part of this definition. -/
noncomputable def slack {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin m)) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, y i • A i - C

end MatrixLeeSidford


