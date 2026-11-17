-- Prove2me | Definitions.Def_MatrixLeeSidford_Supplement_segLength
-- name    : MatrixLeeSidford_Supplement_segLength
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:16:42.944371+00:00
-- url     : https://prove2.me/theorems/90c77281-f093-4b91-b8d9-1bec05edb75f
-- title:
--   F-local length of a point-update segment
-- statement:
--   For points $y,y^+\in\mathbb R^m$, the segment $y(u)=y+u(y^+-y)$, $u\in[0,1]$, has **F-local length**
--   $$
--   d_F=\int_0^1\|y'(u)\|_{\nabla^2F(y(u))}\,du=\int_0^1\big\|y^+-y\big\|_{\nabla^2F(y+u(y^+-y))}\,du ,
--   $$
--   where $F$ is the matrix Lee–Sidford barrier. This length controls how much the weight gap of a fixed weight can change along the segment (Theorem 8.5(c)).
--
--   **Formalization Note** The integral is Lean's interval integral, which returns $0$ for a non-integrable integrand; statements that bound $d_F$ also assert integrability.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Theorem 8.5(c), p.57; Lemma 9.4(b), p.63; Theorem 9.6, p.65

import Mathlib
import Definitions.Def_MatrixLeeSidford_barrierF
import Definitions.Def_DoublyOptBandit_LocalNorm

open Matrix

namespace MatrixLeeSidford.Supplement

/-- The **F-local length** of the point-update segment from `y` to `y⁺`: for the path
`y(u) = y + u(y⁺ − y)`, `u ∈ [0, 1]`, it is `∫₀¹ ‖y'(u)‖_{∇²F(y(u))} du = ∫₀¹ ‖y⁺ − y‖_{∇²F(y + u(y⁺−y))} du`
(Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Theorem 8.5(c), p.57, "F-local length d_F := ∫₀¹ ‖y'(u)‖_{∇²F(y(u))} du", applied to a segment
as in Lemma 9.4(b), p.63, and Theorem 9.6, p.65).

**Formalization Note** `F` is the published `barrierF A C`; the local norm is the published
`DoublyOptBandit.localNorm`; the integral is Mathlib's interval integral, which is `0` for a
non-integrable integrand, so every statement bounding it also asserts integrability. -/
noncomputable def segLength {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (y y' : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ u in (0 : ℝ)..1, DoublyOptBandit.localNorm (barrierF A C) (y + u • (y' - y)) (y' - y)

end MatrixLeeSidford.Supplement


