-- Prove2me | Definitions.Def_GeomRescale_fR
-- name    : GeomRescale_fR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:12.069873+00:00
-- url     : https://prove2.me/theorems/bdad9589-b7cd-4324-86b8-668008995b8d
-- title:
--   Integer valued $f$ read as a real function
-- statement:
--   Section 3 of the paper assumes throughout that $f : 2^V \to \mathbb{Z}$ is integer valued. Every polytope of the paper lives in $\mathbb{R}^V$, so the mission reads such an $f$ as the real function $S \mapsto f(S)$ whenever a polytope is formed.
--
--   **Formalization Note** The ground set $V$ is `Fin n` and $2^V$ is `Finset (Fin n)`.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §3, p.6

import Mathlib

namespace GeomRescale

/-- The integer valued `f : 2^V → ℤ` of Section 3 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §3, p.6), read as a real function.

**Formalization Note.** The ground set `V` is `Fin n` and `2^V` is `Finset (Fin n)`. Every polytope
of the paper is a subset of `ℝ^V`, so the real statements of Section 2 apply to `fR f`. -/
def fR {n : ℕ} (f : Finset (Fin n) → ℤ) : Finset (Fin n) → ℝ :=
  fun S => (f S : ℝ)

end GeomRescale


