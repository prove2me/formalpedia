-- Prove2me | Definitions.Def_QPACLarge_QexFamily
-- name    : QPACLarge_QexFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:24.63742+00:00
-- url     : https://prove2.me/theorems/3562bdcd-a929-4fe0-8bef-3c08188fe7a6
-- title:
--   Family of quantum learners on quantum random examples
-- statement:
--   A quantum learner from **uniform quantum random examples** receives copies of
--   $$
--   |\mathrm{QEX}_f\rangle = \frac{1}{\sqrt{2^n}} \sum_{x \in \{0,1\}^n} |x\rangle|f(x)\rangle
--   $$
--   and makes no quantum membership queries. A family is indexed by $i$ (by $n$ for a learner $\{Q_n\}$, by $(n, m)$ for the amplified learner $Q^+(n,m)$), and $\dim i$ is the input length of the targets at index $i$. At index $i$ the learner is a quantum circuit on $\mathrm{ex}(i)$ copies of the quantum example ($\dim i + 1$ wires each, the label wire last) followed by $\mathrm{anc}(i)$ ancilla wires in $|0\rangle$, over the gates $H, S, T, X, \mathrm{CNOT}$. At the end all wires are measured in the computational basis and the bits on a designated list of output wires form the learner's output string, read as the description of a classical Boolean circuit.
--
--   **Formalization Note** The gate set is the published Clifford+T instruction set; the paper fixes none. Classical post-processing is part of the circuit (Clifford+T circuits compute every reversible classical map exactly), which is why the output is read from wires. The circuit is a published layered circuit; only its gate count is used.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.3, pp.15–16

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity

/-- **A family of quantum learners that use quantum random examples.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.3, pp.15–16: "a quantum learning algorithm is described by a uniform sequence
`{Qₙ}` of quantum circuits"; the learners "use copies of this state
[`|QEX_f⟩ = 2^{−n/2} Σₓ |x⟩|f(x)⟩`] and make no quantum membership queries", and every learner of
the paper "produces a classical deterministic Boolean circuit as its output hypothesis" (p.16).

A family is indexed by `i : ι` (`ι = ℕ` for `Qₙ`, `ι = ℕ × ℕ` for the two-parameter `Q⁺(n, m)`
of Section 3.3), and `dim i` is the input length of the targets at index `i`. At index `i` the
circuit acts on `ex i` copies of the quantum example (`dim i + 1` wires each, the label wire
last) followed by `anc i` ancilla wires; it is a layered circuit over the published instruction
set `{H, S, T, X, CNOT}`. All wires are measured in the computational basis at the end, and the
bits on the wires `out i` (in order) are the learner's output string.

**Formalization Note.** The gate set is the published Clifford+T set
`QAlgorithms.Complexity.Instr`; the paper fixes no gate set. Classical post-processing is part of
the circuit (Clifford+T circuits compute every reversible classical map exactly), so the output is
read from designated wires. The layering carries no meaning here: only the gate count is used. -/
structure QexFamily (ι : Type) (dim : ι → ℕ) where
  /-- The number of quantum random examples used at index `i`. -/
  ex : ι → ℕ
  /-- The number of ancilla wires (initialized to `|0⟩`) at index `i`. -/
  anc : ι → ℕ
  /-- The circuit at index `i`. -/
  circ : (i : ι) → Layered (ex i * (dim i + 1) + anc i)
  /-- The output wires at index `i`, in order. -/
  out : (i : ι) → List (Fin (ex i * (dim i + 1) + anc i))

end QPACLarge


