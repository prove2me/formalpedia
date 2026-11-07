-- Prove2me | Definitions.Def_QuantumLTF_Membership_gatesRev
-- name    : QuantumLTF_Membership_gatesRev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:46.706613+00:00
-- url     : https://prove2.me/theorems/0a55c4a5-364a-4cc9-9d70-908d7e749cde
-- title:
--   The reversible gates NOT, CNOT, Toffoli
-- statement:
--   The gates of the reversible circuit of Theorem 3.2: NOT (the gate $X^\sigma$ of p. 24), CNOT, and Toffoli (p. 26, "elementary Toffoli/CNOT gates").
--
--   **Formalization Note** Toffoli is written out with controls on its wires $0,1$ and target on wire $2$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, p. 24 (PDF p. 25); p. 26 (PDF p. 27)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit

namespace QuantumLTF.Membership

open QAlgorithms

/-- **The reversible gates: NOT, CNOT, Toffoli.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, p. 24 (PDF p. 25), the gate `X^σ`, and p. 26
(PDF p. 27): "elementary Toffoli/CNOT gates". Used only for the height oracle of Theorem 3.2, whose
printed statement says "reversible circuit".

**Formalization Note.** The Toffoli gate is written out as the arity-3 permutation matrix with targets
on wire `2`, controls on wires `0, 1`; NOT is `pauliX`, CNOT is `cnot`. All three are unitary. -/
noncomputable def gatesRev : Set Gate :=
  {Gate.ofMatrix1 pauliX, Gate.ofMatrix2 cnot,
    ⟨3, Matrix.of fun y z =>
      if y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1) then 1 else 0⟩}

end QuantumLTF.Membership


