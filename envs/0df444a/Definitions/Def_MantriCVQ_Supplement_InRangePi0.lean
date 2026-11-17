-- Prove2me | Definitions.Def_MantriCVQ_Supplement_InRangePi0
-- name    : MantriCVQ_Supplement_InRangePi0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:05:19.039384+00:00
-- url     : https://prove2.me/theorems/c19f3e06-4036-497a-bec2-305f042057d7
-- title:
--   Range of the projector $\Pi_0$ of Claim A.2
-- statement:
--   On $a+(1+k)$ qubits (address register, output qubit, $k$ work qubits), a state $\psi$ lies in the **range of $\Pi_0$** for a set of valid addresses if every basis state in its support has a valid address in the address register and all its work qubits equal to $0$; the output qubit is arbitrary. In Claim A.2, $\Pi_0$ is the orthogonal projector onto the span of these basis states, and the closeness bound $\|(G-E)\Pi_0\|\le\delta$ is the statement $\|(G-E)\psi\|\le\delta\|\psi\|$ for every such $\psi$.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim A.2, p. 43 (PDF p. 45)

import Mathlib
import Definitions.Def_MantriCVQ_Supplement_regAddr

open QAlgorithms.Complexity

namespace MantriCVQ.Supplement

/-- `ψ` lies in the range of the projector `Π₀` of Claim A.2 (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), Claim A.2, p. 43 (PDF p. 45): "`Π₀` is the orthogonal projector onto the subspace
spanned by the states whose address register holds a valid address and whose work registers, meaning
all work registers of `G`, are in the zero state"): on `a + (1 + anc)` wires (address, output qubit,
work), every basis state in the support of `ψ` has a valid address and all `anc` work wires `0`. The
output qubit is arbitrary. -/
def InRangePi0 {a anc : ℕ} (valid : Str → Prop) (ψ : QState (a + (1 + anc))) : Prop :=
  ∀ y : Bits (a + (1 + anc)), ψ y ≠ 0 →
    valid (regAddr y) ∧ ∀ k : Fin anc, y (Fin.natAdd a (Fin.natAdd 1 k)) = false

end MantriCVQ.Supplement


