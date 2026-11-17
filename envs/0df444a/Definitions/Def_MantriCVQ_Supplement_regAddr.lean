-- Prove2me | Definitions.Def_MantriCVQ_Supplement_regAddr
-- name    : MantriCVQ_Supplement_regAddr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:03:56.878673+00:00
-- url     : https://prove2.me/theorems/6020d941-3a9f-4782-9169-7bba9b5d8a57
-- title:
--   Content of the address register
-- statement:
--   For a computational basis state $y$ on $a+k$ qubits whose first $a$ qubits form the **address register**, this is the string of the first $a$ bits of $y$, the address held in the register. It is used to describe the clean oracle and the projector $\Pi_0$ of Claim A.2.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §5.1, p. 18 (PDF p. 20); Claim A.2, p. 43 (PDF p. 45)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace MantriCVQ.Supplement

/-- The content of the address register of a basis state on `a + k` wires: its first `a` bits, as a
string (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §5.1, p. 18 (PDF p. 20); Claim A.2,
p. 43 (PDF p. 45): "receives the address of a node in a register, the address register"). The
registers are, in order, the address, then the remaining `k` wires. -/
def regAddr {a k : ℕ} (y : Bits (a + k)) : Str :=
  List.ofFn fun i : Fin a => y (Fin.castAdd k i)

end MantriCVQ.Supplement


