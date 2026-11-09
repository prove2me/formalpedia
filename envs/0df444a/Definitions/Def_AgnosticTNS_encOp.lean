-- Prove2me | Definitions.Def_AgnosticTNS_encOp
-- name    : AgnosticTNS_encOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:37:37.212433+00:00
-- url     : https://prove2.me/theorems/e0717053-8bca-424e-bd28-c339d5aefcb6
-- title:
--   An $n$-qudit operator on the qubit encoding
-- statement:
--   The operator on $n\lceil\log_2 d\rceil$ qubits that acts as $X$ on the encoded computational basis states and is zero outside their span; for a density operator $\rho$, the encoded copy is again a density operator.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Eq. (3.68), p.26

import Mathlib
import Definitions.Def_AgnosticTNS_encCfg

namespace AgnosticTNS

/-- **An `n`-qudit operator on the qubit encoding**, Eq. (3.68), p.26 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the operator on
`n·⌈log₂ d⌉` qubits that acts as `X` on the encoded basis states and is zero outside the span of
valid codes. -/
def encOp {n d : ℕ} (X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    Matrix (QAlgorithms.Complexity.Bits (n * Nat.clog 2 d)) (QAlgorithms.Complexity.Bits (n * Nat.clog 2 d)) ℂ :=
  Matrix.of fun X' Y' => ∑ x, ∑ y, if encCfg n d x = X' ∧ encCfg n d y = Y' then X x y else 0

end AgnosticTNS


