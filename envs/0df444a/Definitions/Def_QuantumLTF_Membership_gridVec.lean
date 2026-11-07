-- Prove2me | Definitions.Def_QuantumLTF_Membership_gridVec
-- name    : QuantumLTF_Membership_gridVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:34:09.070185+00:00
-- url     : https://prove2.me/theorems/ead09bcc-0ce5-4274-b8e4-4f2448e475a3
-- title:
--   The point of $G_b^n$ of a basis state
-- statement:
--   The basis state $|j\rangle$ of $b$ qubits is labelled by $g_b(j)=j/2^b-1/2+2^{-b-1}$, the centered grid $G_b\subset(-1/2,1/2)$. For $n$ registers, the vector $x$ of strings denotes the point of $G_b^n$ with coordinates $g_b(x_i)$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §3.1.2, p. 23 (PDF p. 24)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods

namespace QuantumLTF.Membership

open QAlgorithms

/-- **The grid point of a basis state of `n` registers.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §3.1.2, p. 23 (PDF p. 24):
`|j⟩` is labelled by `g_b(j) := j/2^b − 1/2 + 2^{−b−1}` (`gridPoint`), and the grid is `G_b^n`.

**Formalization Note.** Every string is a grid point, since `gridPoint` covers `G_b` exactly. -/
noncomputable def gridVec (n b : ℕ) (x : Fin n → Qubits b) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => gridPoint b (x i)

end QuantumLTF.Membership


