-- Prove2me | Definitions.Def_DepthOneQExp_cnotGate
-- name    : DepthOneQExp_cnotGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:11.898166+00:00
-- url     : https://prove2.me/theorems/3a7f3d0a-715c-401b-8be2-e78619c15092
-- title:
--   The two-qubit gate CNOT
-- statement:
--   The two-qubit CNOT gate $|c,t\rangle\mapsto|c,\,t\oplus c\rangle$ as a gate of arity 2 in the published gate model `MITMSynthesis.Gate`: wire 0 is the control and wire 1 the target. Placed on qubits $(a,b)$ of a register it is $\mathrm{CNOT}_{a,b}$, controlled by $a$ and acting on $b$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Notations, p.6

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_permToMatrix
import Definitions.Def_DepthOneQExp_cnotPerm

namespace DepthOneQExp

/-- The two-qubit CNOT gate as a gate of arity 2 (Anshu–Balasubramanian–Haferkamp–Harrow–Tan,
*Depth-1 expanders on the unitary group and applications*, arXiv:2609.01605, held version sha256
3c3f8513…aebfd87, Notations, p.6): wire `0` is the control and wire `1` the target,
`|c, t⟩ ↦ |c, t + c⟩`.

**Formalization Note** Placed on qubits `(a, b)` of a register (wire `0` on `a`, wire `1` on `b`),
it is `CNOT_{a,b}`, controlled by `a` and acting on `b`. -/
noncomputable def cnotGate : MITMSynthesis.Gate :=
  ⟨2, two_pos, ⟨permToMatrix (cnotPerm 2 0 1), permToMatrix_mem_unitaryGroup _⟩⟩

end DepthOneQExp


