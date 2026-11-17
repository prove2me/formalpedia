-- Prove2me | Definitions.Def_NewtonLCP_Supplement_Cayley
-- name    : NewtonLCP_Supplement_Cayley
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:15:35.056274+00:00
-- url     : https://prove2.me/theorems/86e28a33-38bf-48ae-8b22-55dcc86290f9
-- title:
--   The Cayley transform $C(M)$ and the inverse Cayley transform $C^{-1}(M)$
-- statement:
--   For $M\in\mathbb R^{n\times n}$ such that $I_n-M$ is nonsingular, the **Cayley transform** of $M$ is
--
--   $$C(M)=(I_n-M)^{-1}(I_n+M).$$
--
--   For $M$ such that $I_n+M$ is nonsingular, the **inverse Cayley transform** is
--
--   $$C^{-1}(M)=(M-I_n)(M+I_n)^{-1}.$$
--
--   Note the order of the factors: the inverse stands on the left in $C$ and on the right in $C^{-1}$. These transforms connect the sign-real spectral radius with the matrix classes $P$, $P_\star$ and $P_0$ (Theorems 7.6 and 7.17).
--
--   **Formalization Note** The inverse is Mathlib's matrix inverse, which is $0$ for a singular matrix, so both maps are defined for every $M$; the theorems that use them assume the nonsingularity exactly where the paper does.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Definition 7.2, p.24; Proposition 7.3, p.25

import Mathlib

open Matrix

namespace NewtonLCP.Supplement

/-!
# The Cayley transform and the inverse Cayley transform

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8),
Definition 7.2, p.24, and Proposition 7.3, p.25.

* `C(M) := (Iₙ − M)⁻¹(Iₙ + M)` for `Iₙ − M` nonsingular (inverse on the **left**).
* `C⁻¹(M) := (M − Iₙ)(M + Iₙ)⁻¹` for `Iₙ + M` nonsingular (inverse on the **right**).

**Formalization Note.** The inverse is Mathlib's `Matrix.inv`, which is `0` for a singular
matrix, so both maps are total; every theorem that uses them carries the paper's nonsingularity
hypothesis (`det ≠ 0`) exactly where the paper has it.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Cayley transform `C(M) = (Iₙ − M)⁻¹(Iₙ + M)` (Definition 7.2). -/
noncomputable def cayley (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (1 - M)⁻¹ * (1 + M)

/-- The inverse Cayley transform `C⁻¹(M) = (M − Iₙ)(M + Iₙ)⁻¹` (Proposition 7.3). -/
noncomputable def invCayley (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (M - 1) * (M + 1)⁻¹

end NewtonLCP.Supplement


