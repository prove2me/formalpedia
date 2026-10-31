-- Prove2me | Definitions.Def_ParamSDPTraj_frob
-- name    : ParamSDPTraj_frob
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:45.366759+00:00
-- url     : https://prove2.me/theorems/4ff1ea11-c52b-4d2f-9434-8f37f1dc7edd
-- title:
--   Frobenius norm $\|X\|_F$
-- statement:
--   The **Frobenius norm** of a real $n\times n$ matrix is
--
--   $$\|X\|_F=\Big(\sum_{i,j}X_{i,j}^2\Big)^{1/2}.$$
--
--   It measures matrices in the uniform bound of Assumption 3.1 and in the boundedness statements.
--
--   **Formalization Note** It is written out because Mathlib declares no global norm on matrices.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Theorem 2.15 proof, p.8 (the norm ‖·‖_F)

import Mathlib

namespace ParamSDPTraj

/-- **Frobenius norm ‖X‖_F.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Theorem 2.15 proof, p.8 (the norm ‖·‖_F).

**Formalization Note** Written out because Mathlib declares no global norm on `Matrix`. Its
topology on `Matrix` is the entrywise one, which every norm induces in finite dimension. -/
noncomputable def frob {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, X i j ^ 2)

end ParamSDPTraj


