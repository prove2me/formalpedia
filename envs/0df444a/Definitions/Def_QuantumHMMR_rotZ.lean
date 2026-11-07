-- Prove2me | Definitions.Def_QuantumHMMR_rotZ
-- name    : QuantumHMMR_rotZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:54.791393+00:00
-- url     : https://prove2.me/theorems/47499184-d49f-4ada-90dd-941fdd8a74a6
-- title:
--   Single-qubit rotation $e^{i\varphi Z}$
-- statement:
--   For an angle $\varphi \in \mathbb R$, the single-qubit rotation about the $Z$ axis is
--   $$
--   e^{i\varphi Z} = \begin{pmatrix} e^{i\varphi} & 0 \\ 0 & e^{-i\varphi} \end{pmatrix},
--   $$
--   diagonal in the computational basis, with $e^{i\varphi}$ on $|0\rangle$ and $e^{-i\varphi}$ on $|1\rangle$. For $\varphi$ not a multiple of $\pi/4$ it is not a Clifford gate; it is the non-Clifford ingredient of the walk.
--
--   **Formalization Note** One-qubit matrices are indexed by bit strings of length one; the bit `false` is $|0\rangle$.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 4, p.11

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45

namespace QuantumHMMR

/-- The single-qubit rotation `e^{iφZ} = diag(e^{iφ}, e^{-iφ})` (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §4, p.11: "a uniformly random
rotation `e^{iϕZ}`").

**Formalization Note** A one-qubit matrix is indexed by `Qubits 1 = Fin 1 → Bool`; the bit
`false` is `|0⟩` (the `+1` eigenvector of `Z`) and gets `e^{iφ}`, the bit `true` is `|1⟩` and gets
`e^{-iφ}`. -/
noncomputable def rotZ (φ : ℝ) : QMat 1 :=
  Matrix.diagonal fun x => if x 0 then Complex.exp (-((φ : ℂ) * Complex.I))
    else Complex.exp ((φ : ℂ) * Complex.I)

end QuantumHMMR


