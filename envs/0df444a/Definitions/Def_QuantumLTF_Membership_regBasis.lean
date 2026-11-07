-- Prove2me | Definitions.Def_QuantumLTF_Membership_regBasis
-- name    : QuantumLTF_Membership_regBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:54.528721+00:00
-- url     : https://prove2.me/theorems/5d52af1d-269a-475a-880e-1db46e8b8122
-- title:
--   The basis string $|x\rangle|v\rangle|0\rangle$ of the height oracle
-- statement:
--   The register of the height oracle: $x$ on the first $nb$ wires, the value $v$ on the next $V_b$ wires, and $W$ work wires in $|0\rangle$.
--
--   **Formalization Note** The paper leaves the work register implicit: "Reversing the q bisection rounds cleans all work registers".
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.2, p. 23 (PDF p. 24); p. 25 (PDF p. 26)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_flatReg

namespace QuantumLTF.Membership

open QAlgorithms

/-- **The basis string `x, v, 0` of the height oracle's register.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 3.2, p. 23
(PDF p. 24), `|x⟩|0⟩ ↦ |x⟩|H̃_p(x)⟩`: register `x` is on wires `0, …, n*b−1`, the value on the next
`Vb` wires, and `W` work wires follow, in `|0⟩`.

**Formalization Note.** The paper leaves the work register implicit ("Reversing the q bisection rounds
cleans all work registers", p. 25 (PDF p. 26)). -/
def regBasis (n b Vb W : ℕ) (x : Fin n → Qubits b) (v : Qubits Vb) : Qubits (n * b + Vb + W) :=
  Fin.append (Fin.append (flatReg n b x) v) (fun _ => false)

end QuantumLTF.Membership


