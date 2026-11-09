-- Prove2me | Definitions.Def_LindbladStructLearn_eigenProj
-- name    : LindbladStructLearn_eigenProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:51:38.37628+00:00
-- url     : https://prove2.me/theorems/a4e8047c-df12-4df7-9126-4d6a421293d8
-- title:
--   $n$-qubit Pauli eigenstate projector $|Q,v\rangle\langle Q,v|$
-- statement:
--   For $Q \in \mathcal P_n$ and $v \in \{\pm1\}^n$, $|Q,v\rangle$ is the tensor product of the single-qubit eigenstates $|Q_i, v_i\rangle$; this is its projector.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2.2, p.16

import Mathlib
import Definitions.Def_LindbladStructLearn_oneEigenProj

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- `n`-qubit Pauli eigenstate projector (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2.2, p.16): `|Q,v⟩⟨Q,v|`, the tensor
product of the single-qubit projectors. -/
def eigenProj {n : ℕ} (A : Pauli n) (v : Qubits n) : Op (Qubits n) := fun x y =>
  ∏ i, oneEigenProj (A i) (v i) (x i) (y i)

end LindbladStructLearn


