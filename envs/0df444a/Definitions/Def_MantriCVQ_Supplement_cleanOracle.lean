-- Prove2me | Definitions.Def_MantriCVQ_Supplement_cleanOracle
-- name    : MantriCVQ_Supplement_cleanOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:04:36.934118+00:00
-- url     : https://prove2.me/theorems/62aa2fe5-7a78-4b06-9949-0e743a40f900
-- title:
--   Clean oracle $E$ for node values
-- statement:
--   On $a+(1+k)$ qubits, an address register of $a$ qubits, one output qubit and $k$ work qubits, the **clean oracle** for a value function $\mathrm{val}$ on addresses is the linear map
--   $$E\,|w\rangle|b\rangle|z\rangle=|w\rangle|b\oplus\mathrm{val}(w)\rangle|z\rangle .$$
--   Claim A.2 and Theorem A.3 compare unitaries built from bounded-error algorithms with this oracle, for the values of nodes of trees valid with noise rate $\eta$.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim A.2, p. 43 (PDF p. 45); §5.1, p. 18 (PDF p. 20)

import Mathlib
import Definitions.Def_MantriCVQ_Supplement_regAddr

open QAlgorithms.Complexity

namespace MantriCVQ.Supplement

/-- The clean oracle `E` for a value function `val` on addresses (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), Claim A.2, p. 43 (PDF p. 45): "`E` is the clean oracle that adds the value of the node
at the address to an output qubit"; §5.1, p. 18 (PDF p. 20)): on `a + (1 + anc)` wires, the address
register (the first `a` wires), the output qubit (wire `a`) and `anc` work wires,
`E |w⟩|b⟩|z⟩ = |w⟩|b ⊕ val(w)⟩|z⟩`, extended linearly. -/
def cleanOracle {a anc : ℕ} (val : Str → Bool) (ψ : QState (a + (1 + anc))) :
    QState (a + (1 + anc)) :=
  fun y =>
    ψ (Function.update y (Fin.natAdd a ⟨0, by omega⟩)
      (xor (y (Fin.natAdd a ⟨0, by omega⟩)) (val (regAddr y))))

end MantriCVQ.Supplement


