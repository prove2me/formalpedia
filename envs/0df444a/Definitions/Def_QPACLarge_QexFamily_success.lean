-- Prove2me | Definitions.Def_QPACLarge_QexFamily_success
-- name    : QPACLarge_QexFamily_success
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:46.469538+00:00
-- url     : https://prove2.me/theorems/0d1a7d8d-80d9-4de9-9bb0-5930dcabbb5a
-- title:
--   Success probability $\Pr_{Q}[\,\cdot\,]$ of a quantum learner
-- statement:
--   For a learner at index $i$ (targets on $n = \dim i$ bits), a target $f$ and a property $P$ of Boolean circuits, $\Pr_Q[P]$ is the probability that the learner, run on $\mathrm{ex}(i)$ independent copies of $|\mathrm{QEX}_f\rangle$ and $\mathrm{anc}(i)$ ancillas in $|0\rangle$, outputs the description of a Boolean circuit $C$ with property $P$:
--
--   $$
--   \Pr_Q[P] = \sum_{z} \big|\langle z|\,Q_i\,|\mathrm{QEX}_f\rangle^{\otimes \mathrm{ex}(i)}|0\rangle^{\otimes \mathrm{anc}(i)}\big|^2 \cdot \mathbf 1\big[\text{the output bits of } z \text{ begin with the code of a circuit } C \text{ with } P(C)\big].
--   $$
--
--   The success events of Theorems 1.2, 1.5 and 3.6 take $P(C)$ to be "$\mathrm{agreement}(f, h_C) \ge 1/2 + \gamma$" (with a size bound on $C$ where the theorem states one), $h_C$ the function computed by $C$.
--
--   **Formalization Note** The input is the published `qexInputState` of the published `exampleState f` under the uniform distribution; circuit codes are the binary prefix-free `encBoolCircuitBin`, so that a circuit of size $S$ takes $O(S \log S)$ output bits, as the time bounds $m \cdot \mathrm{poly}(n)$ and $\mathrm{poly}(n)/\eta$ of Theorems 3.6 and 1.2 require. An output that does not begin with a circuit code counts as failure.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.3, pp.15–16; Theorems 1.2 (p.5), 1.5 (p.7), 3.6 (p.29)

import Mathlib
import Definitions.Def_QPACLarge_QexFamily
import Definitions.Def_QAlgorithms_Defs_Learning
import Definitions.Def_QAlgorithms_Defs_LearningSeparation
import Definitions.Def_QPACLarge_encBoolCircuitBin

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity QAlgorithms.Learning

/-- **Success probability of a quantum learner from uniform quantum random examples.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.3, pp.15–16, and the success probabilities `Pr_A[·]`, `Pr_{Q⁺}[·]` of Theorems
1.2 and 1.5 (pp.5, 7) and 3.6 (p.29).

`L.success i f P` is the probability that the learner at index `i`, run on `ex i` independent
copies of `|QEX_f⟩ = 2^{−n/2} Σₓ |x⟩|f(x)⟩` (`n = dim i`) and `anc i` ancillas in `|0⟩`, outputs
the code of a well-formed Boolean circuit `C` (on `n` inputs, one output) with property `P`:
the total squared amplitude, after the circuit, of the basis strings whose output bits begin with
such a code.

**Formalization Note.** The input state is the published `qexInputState` of the published
`exampleState f` under the published uniform distribution. Circuits are the published
`BoolCircuit`, read in the binary code `encBoolCircuitBin` (prefix-free, so the circuit is
determined by the output string; binary so that printing a circuit of size `S` takes `O(S log S)`
output bits, as the time bounds of Theorems 1.2 and 3.6 require). An output that is not a circuit
code counts as failure. -/
noncomputable def QexFamily.success {ι : Type} {dim : ι → ℕ} (L : QexFamily ι dim) (i : ι)
    (f : Qubits (dim i) → Bool) (P : BoolCircuit (dim i) 1 → Prop) : ℝ :=
  open Classical in
  ∑ z : Qubits (L.ex i * (dim i + 1) + L.anc i),
    if ∃ C : BoolCircuit (dim i) 1, C.WellFormed ∧ encBoolCircuitBin C <+: (L.out i).map z ∧ P C then
      ‖runLayered (L.circ i)
          (WithLp.ofLp (qexInputState (L.ex i) (L.anc i)
            (exampleState f (uniformDist (Qubits (dim i)))))) z‖ ^ 2
    else 0

end QPACLarge


