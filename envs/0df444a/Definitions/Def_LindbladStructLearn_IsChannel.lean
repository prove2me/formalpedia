-- Prove2me | Definitions.Def_LindbladStructLearn_IsChannel
-- name    : LindbladStructLearn_IsChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:54.362194+00:00
-- url     : https://prove2.me/theorems/d5514558-f4a1-4edf-9111-76cf6c6caaa3
-- title:
--   $n$-qubit quantum channel
-- statement:
--   A superoperator on $n$ qubits is a quantum channel when it is completely positive (the reused `IsCP`: positive on every finite ancilla extension) and trace preserving.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 1, input, p.17

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- An `n`-qubit quantum channel (the input `Φ` of Algorithm 1, Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.17): completely
positive (the reused `IsCP`) and trace preserving. -/
def IsChannel {n : ℕ} (Φ : Super (Qubits n) (Qubits n)) : Prop :=
  IsCP Φ ∧ ∀ x : Op (Qubits n), (applySuper Φ x).trace = x.trace

end LindbladStructLearn


