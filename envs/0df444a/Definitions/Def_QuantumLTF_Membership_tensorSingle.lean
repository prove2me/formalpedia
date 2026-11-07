-- Prove2me | Definitions.Def_QuantumLTF_Membership_tensorSingle
-- name    : QuantumLTF_Membership_tensorSingle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:51.494453+00:00
-- url     : https://prove2.me/theorems/ad887640-04c6-4de0-92a8-25f5945526ee
-- title:
--   A tensor product of $b$ single-qubit operators
-- statement:
--   For single-qubit operators $u_0,\dots,u_{b-1}$, the operator $u_0\otimes\dots\otimes u_{b-1}$ on $b$ qubits, whose entry at $(y,z)$ is $\prod_i (u_i)_{y_i,z_i}$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.3, p. 27 (PDF p. 28)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Membership

open QAlgorithms

/-- **A tensor product of `b` single-qubit operators.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Lemma 3.3, p. 27 (PDF p. 28): the
operator `u 0 ⊗ ⋯ ⊗ u (b−1)` on `b` qubits, with entry `∏_i (u i)_{y_i, z_i}`; `u i` acts on wire `i`. -/
def tensorSingle {b : ℕ} (u : Fin b → Matrix Bool Bool ℂ) : Matrix (Qubits b) (Qubits b) ℂ :=
  Matrix.of fun y z => ∏ i, u i (y i) (z i)

end QuantumLTF.Membership


