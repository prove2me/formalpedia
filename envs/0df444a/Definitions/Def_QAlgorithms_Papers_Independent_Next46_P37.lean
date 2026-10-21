-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P37
-- name    : QAlgorithms_Papers_Independent_Next46_P37
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:38:33.971152+00:00
-- url     : https://prove2.me/theorems/18e3be8f-e657-4019-8fda-e0a332d7003d
-- title:
--   Definitions for On the Weyl Representation of Metaplectic Operators
-- statement:
--   The objects the formalized statements of *On the Weyl Representation of Metaplectic Operators* (arXiv:math/0503708) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `cayley`: PDF p.6, (2): the source's symplectic Cayley transform. Every theorem using this expression requires det(S-I) nonzero.
--   - `inverseCayley`: PDF p.6, §3.1: the inverse Cayley expression, in the printed order. Its domain in the theorem is det(M-J/2) nonzero.
--   - `freeProjection`: PDF p.4, (8): free symplectic projection of the quadratic generating data. The source domain is P and Q symmetric and det L nonzero.
--   - `diagonalHessian`: PDF p.8, before Proposition 6: Hessian of x ↦ W(x,x). This is the diagonal Hessian, not the partial Hessian of W(x,xprime).
-- source:
--   On the Weyl Representation of Metaplectic Operators, arXiv:math/0503708v1, https://arxiv.org/abs/math/0503708v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

/-!
# On the Weyl Representation of Metaplectic Operators

Maurice A. de Gosson, arXiv:math/0503708v1.
The finite matrix results are stated here. The analytic operator and classical
path-index results, and the inconsistent printed equation (27), are individually
accounted for in the unit's HARD.md and GAPS.json. No abstract implementer is
substituted for the concrete metaplectic representation.

The accepted Phase and sigma definitions use grouped position/momentum order
and J = [[0,I],[-I,0]]. Mathlib's Matrix.J has the opposite sign; its symplectic
GROUP is the same, but it must not replace sigma in the Cayley formula.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Next46.P37

/-- PDF p.6, (2): the source's symplectic Cayley transform.
Every theorem using this expression requires det(S-I) nonzero. -/
def cayley {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ) :
    Matrix (Phase n) (Phase n) ℝ :=
  (1 / 2 : ℝ) • (sigma n * (S + 1) * (S - 1)⁻¹)

/-- PDF p.6, §3.1: the inverse Cayley expression, in the printed order.
Its domain in the theorem is det(M-J/2) nonzero. -/
def inverseCayley {n : ℕ} (M : Matrix (Phase n) (Phase n) ℝ) :
    Matrix (Phase n) (Phase n) ℝ :=
  (M - (1 / 2 : ℝ) • sigma n)⁻¹ * (M + (1 / 2 : ℝ) • sigma n)

/-- PDF p.4, (8): free symplectic projection of the quadratic generating data.
The source domain is P and Q symmetric and det L nonzero. -/
def freeProjection {n : ℕ} (P L Q : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Phase n) (Phase n) ℝ :=
  Matrix.fromBlocks (L⁻¹ * Q) L⁻¹ (P * L⁻¹ * Q - L.transpose) (P * L⁻¹)

/-- PDF p.8, before Proposition 6: Hessian of x ↦ W(x,x).
This is the diagonal Hessian, not the partial Hessian of W(x,xprime). -/
def diagonalHessian {n : ℕ} (P L Q : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := P + Q - L - L.transpose

/-- A one-mode entry fixes the source J sign and the grouped ordering. -/
example : sigma 1 (Sum.inl 0) (Sum.inr 0) = 1 := by
  rfl

/-- The one-mode matrix -I has Cayley transform zero. -/
example : cayley (n := 1) (-1) = 0 := by
  simp [cayley]

/-- At the excluded inverse-Cayley boundary the total matrix inverse is zero.
This default is why the theorem explicitly excludes this domain point. -/
example : inverseCayley (n := 1) ((1 / 2 : ℝ) • sigma 1) = 0 := by
  simp [inverseCayley]

/-- The one-mode Fourier generating data project to the source J. -/
example : freeProjection (n := 1) 0 1 0 = sigma 1 := by
  simp [freeProjection, sigma]

/-- The same one-mode data have diagonal Hessian -2I. -/
example : diagonalHessian (n := 1) 0 1 0 = -(2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  simp [diagonalHessian, Matrix.one_apply]
  <;> split_ifs <;> norm_num

end QAlgorithms.Papers.Independent.Next46.P37


