-- Prove2me | Definitions.Def_KTUnitary_Synth_allBits
-- name    : KTUnitary_Synth_allBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:56.685379+00:00
-- url     : https://prove2.me/theorems/677fb440-c9c5-4310-b397-35cf80dc73ab
-- title:
--   The computational basis in a fixed order
-- statement:
--   The list of the $2^k$ basis states of $k$ qubits, the state number $i$ having bit $q$ of $i$ on qubit $q$. It fixes the order in which gate entries are written in a circuit description.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.2, p. 14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **The computational basis of `k` qubits in a fixed order** (used to list the entries of a gate
in its description, Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.2, p. 14): the basis states `i = 0, 1, …, 2^k − 1`, where
qubit `q` of `i` is bit `q` of the binary expansion of `i`. Every element of `Bits k` occurs exactly
once. -/
def allBits (k : ℕ) : List (Bits k) :=
  (List.range (2 ^ k)).map fun i q => i.testBit q

end KTUnitary.Synth


