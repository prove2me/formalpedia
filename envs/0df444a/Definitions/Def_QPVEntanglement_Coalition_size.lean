-- Prove2me | Definitions.Def_QPVEntanglement_Coalition_size
-- name    : QPVEntanglement_Coalition_size
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:38:09.351794+00:00
-- url     : https://prove2.me/theorems/21437801-8f26-4c63-ae16-260179411d53
-- title:
--   Quantum-register size of a coalition
-- statement:
--   This definition is part of the **operator-requested pinned-down model** (choice P7).
--
--   The **quantum-register size** of a coalition is
--
--   $$\mathrm{size}=\sum_a q_a,$$
--
--   the total number of qubits $q_a$ of the stations' fixed registers. A launched qubit is its own outgoing register: by the definition of a coalition it stays unavailable to its station until the verifier receives it, so it remains counted for the whole flight. This is the paper's "total number of qubits that its fixed local and outgoing quantum registers can hold. Every outgoing quantum register from an adversary remains included in the sending adversary's quantum-register size and unavailable for reuse until the verifier receives or discards its state" (p.29). Classical registers are not counted. With this accounting the honest prover needs $R_H$ qubits, as stated on p.32.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), §4, p.29 (quantum-register size) and footnote 22

import Mathlib
import Definitions.Def_QPVEntanglement_Coalition_acceptProb

set_option autoImplicit false

namespace QPVEntanglement

namespace Coalition

variable {G : Geometry} {m RH s : ℕ} {S : Schedule G m RH s} (C : Coalition S)

/-- **Quantum-register size** of the coalition (Adversary Model, p.29; pinned model P7).
Behera–Goyal, arXiv:2609.39234 (sha256 bdf2928d…), §4, p.29, and footnote 22.

`size = Σ_a q a`: the total number of qubits of the stations' fixed registers ("the total
number of qubits that its fixed local and outgoing quantum registers can hold. Every outgoing
quantum register from an adversary remains included in the sending adversary's quantum-register
size and unavailable for reuse until the verifier receives or discards its state", p.29).
Classical registers are not counted.

**Formalization Note.** Registers are qubits ("consists of `Q` qubits", p.27). A launched qubit
`j` of station `a` is its own outgoing register: the structure field `Coalition.launch_locked`
keeps it unavailable (no later event of `a` acts on it) until the qubit reaches the verifier, so
it stays counted in `q a` for the whole flight, and no separate in-flight count is added. With
this accounting the honest prover needs `R_H` qubits, as on p.32. -/
noncomputable def size : ℕ := ∑ a, C.q a

end Coalition

end QPVEntanglement


