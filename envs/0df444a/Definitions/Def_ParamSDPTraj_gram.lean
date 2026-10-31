-- Prove2me | Definitions.Def_ParamSDPTraj_gram
-- name    : ParamSDPTraj_gram
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:24.263982+00:00
-- url     : https://prove2.me/theorems/2c7ea13a-a528-4003-806b-1c623f0d306c
-- title:
--   The Gram matrix of $\mathcal A(t)\mathcal A^*(t)$
-- statement:
--   The operator $\mathcal A(t)\mathcal A^*(t)$ on $\mathbb R^m$ is represented by the **Gram matrix** $G(t)$ with entries
--
--   $$G(t)_{i,j}=\langle A_i(t),A_j(t)\rangle.$$
--
--   It is invertible exactly when the symmetric matrices $A_i(t)$ are linearly independent, and it enters the pseudo-inverse of Assumption 3.1.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Assumption 3.1, p.12

import Mathlib
import Definitions.Def_ParamSDPTraj_pair

namespace ParamSDPTraj

/-- **The Gram matrix of 𝒜(t)𝒜*(t).**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Assumption 3.1, p.12 (the operator A(t)A∗(t)).

**Formalization Note** 𝒜(t)𝒜*(t)[y] = `(gram A t).mulVec y`, with entries ⟨A_i(t), A_j(t)⟩. It is
invertible exactly when the A_i(t) are linearly independent (and A_i(t) symmetric). -/
noncomputable def gram {n m : ℕ} (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => pair (A i t) (A j t)

end ParamSDPTraj


