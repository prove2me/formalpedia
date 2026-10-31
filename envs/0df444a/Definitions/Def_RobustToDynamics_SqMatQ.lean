-- Prove2me | Definitions.Def_RobustToDynamics_SqMatQ
-- name    : RobustToDynamics_SqMatQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:38.960815+00:00
-- url     : https://prove2.me/theorems/383fbfba-ec90-4f90-9b1f-74f9b6535329
-- title:
--   A rational square matrix $G\in\mathbb Q^{n\times n}$
-- statement:
--   A size $n$ together with a rational matrix $G\in\mathbb Q^{n\times n}$: the input of the computation of the Lyapunov solution $M$ in Step 1 of the proof of Theorem 2.7, whose cost is polynomial in $\sigma(G)$.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 1, p.14

import Mathlib

namespace RobustToDynamics

/-- **A rational square matrix with its size.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 1, p.14 ("M is rational, can be computed in polynomial time, and has size polynomially bounded
by σ(G)"): the input `G ∈ ℚ^{n×n}` of the Lyapunov computation.

**Formalization Note.** Any `n`, including `0`. -/
structure SqMatQ where
  /-- the size `n` -/
  n : ℕ
  /-- the matrix `G ∈ ℚ^{n×n}` -/
  G : Matrix (Fin n) (Fin n) ℚ

end RobustToDynamics


