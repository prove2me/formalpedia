-- Prove2me | Definitions.Def_QPVEntanglement_Supplement_CoalitionD_size
-- name    : QPVEntanglement_Supplement_CoalitionD_size
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:20:15.44321+00:00
-- url     : https://prove2.me/theorems/cc9ba79a-0453-44d3-a71d-0aa55867696f
-- title:
--   Quantum-register size of a coalition in $\mathbb R^d$
-- statement:
--   The **quantum-register size** of a coalition in $\mathbb R^d$ is the total number of qubits of its stations' registers,
--
--   $$Q=\sum_a q_a .$$
--
--   Classical registers are not counted. A launched qubit stays unavailable to its station until it reaches the verifier, so it stays counted for its whole flight. This is the paper's accounting: "Every outgoing quantum register from an adversary remains included in the sending adversary's quantum-register size and unavailable for reuse until the verifier receives or discards its state" (p.29).
--
--   **Formalization Note** The same definition as the published one-dimensional `QPVEntanglement.Coalition.size` (pinned model P7).
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), §4 Adversary Model, clause 6 and footnote 22, p.29; Definition 2, p.28

import Mathlib
import Definitions.Def_QPVEntanglement_Supplement_CoalitionD_acceptProb

set_option autoImplicit false

namespace QPVEntanglement.Supplement

namespace CoalitionD

variable {d : ℕ} {GD : GeometryD d} {m RH s : ℕ} {S : Schedule GD.G m RH s} (C : CoalitionD GD S)

/-- **Quantum-register size** of a `d`-dimensional coalition (Adversary Model, p.29; Definition 2,
p.28: "if the coalition has at most `r(λ)` qubits in total"). Behera–Goyal, arXiv:2609.39234
(sha256 bdf2928d…), §4, p.29.

`size = Σ_a q a`, the total number of qubits of the stations' fixed registers, as in the published
one-dimensional `QPVEntanglement.Coalition.size`. Classical registers are not counted.

**Formalization Note.** A launched qubit `j` of station `a` is its own outgoing register: the
field `CoalitionD.launch_locked` keeps it unavailable until it reaches the verifier, so it stays
counted in `q a` for the whole flight. -/
noncomputable def size : ℕ := ∑ a, C.q a

end CoalitionD

end QPVEntanglement.Supplement


