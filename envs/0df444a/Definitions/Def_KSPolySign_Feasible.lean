-- Prove2me | Definitions.Def_KSPolySign_Feasible
-- name    : KSPolySign_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:33:49.209759+00:00
-- url     : https://prove2.me/theorems/e6bcfe43-e423-473d-8877-c31aedcaf637
-- title:
--   Feasible points of the matrix potential program
-- statement:
--   A triple $(b,U,V)$ with $b\in\mathbb R$ and $U,V\in\mathbb C^{n\times n}$ is **feasible** at $y$ when $U\succ0$, $V\succ0$ and
--   $$U^{-1} + M(y) + K_y(V) \preceq bI,\qquad V^{-1} - M(y) + K_y(U) \preceq bI.$$
--   These are the constraints of the matrix potential (Definition 3.3).
--
--   **Formalization Note** $X\preceq Y$ means $Y-X$ is positive semidefinite; $\succ0$ is positive definiteness, which includes being Hermitian.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.3, p.18 (PDF p.18)

import Mathlib
import Definitions.Def_KSPolySign_Msum
import Definitions.Def_KSPolySign_coupling
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Feasible points of the matrix potential program.** `(b, U, V)` is feasible at `y` when `U, V ≻ 0`
and
`U⁻¹ + M(y) + K_y(V) ⪯ bI`, `V⁻¹ − M(y) + K_y(U) ⪯ bI`.
Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.3, p.18 (PDF p.18).

**Formalization Note** `X ⪯ Y` is `(Y − X).PosSemidef` and `≻ 0` is `PosDef` (which includes
Hermitian). `U⁻¹` is Mathlib's matrix inverse; it is the true inverse because `U` is positive
definite. -/
def Feasible {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ)
    (y : Fin k → ℝ) (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  U.PosDef ∧ V.PosDef ∧
    (((b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (U⁻¹ + Msum C F y + coupling C y V)).PosSemidef ∧
    (((b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (V⁻¹ - Msum C F y + coupling C y U)).PosSemidef

end KSPolySign


