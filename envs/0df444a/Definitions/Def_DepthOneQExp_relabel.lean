-- Prove2me | Definitions.Def_DepthOneQExp_relabel
-- name    : DepthOneQExp_relabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:24.439522+00:00
-- url     : https://prove2.me/theorems/7738f8df-0fd8-4503-9bea-fb7dc05dd0e7
-- title:
--   Qubit relabelling $1,4,\dots,3s-2,\,2,5,\dots,3s-1,\,3,6,\dots,3s$
-- statement:
--   In the proof of Theorem 2.3 (p.11) the $3s$ qubits are re-indexed by $1,4,\dots,3s-2,\ 2,5,\dots,3s-1,\ 3,6,\dots,3s$ instead of $1,2,\dots,3s$: the qubit in position $(a-1)s+i$ (block $a$, offset $i$) receives the label $3(i-1)+a$. This definition is the induced permutation of the computational basis: in 0-based terms the qubit at position $as+i$ moves to $3i+a$, and a bit string $x$ becomes $x\circ\pi^{-1}$.
--
--   Conjugating by it turns a gate $\mathrm{CNOT}_{c,t}$ in the old labels into $\mathrm{CNOT}_{\pi(c),\pi(t)}$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), proof of Theorem 2.3, p.11

import Mathlib
import Definitions.Def_MITMSynthesis_Gate

namespace DepthOneQExp

/-- The relabelling of the `3s` qubits used in the proof of Theorem 2.3
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, p.11: "if we index the 3s
qubits by 1, 4, …, 3s − 2, 2, 5, …, 3s − 1, 3, 6, …, 3s instead of 1, 2, …, 3s"), as the induced
permutation of the computational basis: the qubit in old position `a·s + i` (block `a ∈ {0,1,2}`,
offset `i < s`, 0-based) receives the new label `3i + a`, and a bit string `x` in the old labelling
becomes `x ∘ π⁻¹` in the new one.

**Formalization Note** Conjugation `relabel s * σ * (relabel s)⁻¹` turns a gate `CNOT_{c,t}` in the
old labels into `CNOT_{π c, π t}` in the new labels. -/
def relabel (s : ℕ) : Equiv.Perm (MITMSynthesis.Q (3 * s)) :=
  Equiv.arrowCongr
    (finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin 3) (Fin s)).trans
      (finProdFinEquiv.trans (finCongr (Nat.mul_comm s 3)))))
    (Equiv.refl (Fin 2))

end DepthOneQExp


