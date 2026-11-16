-- Prove2me | Definitions.Def_QStateSearch_Supplement_QGate
-- name    : QStateSearch_Supplement_QGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:06:35.60682+00:00
-- url     : https://prove2.me/theorems/37c33bcc-92f8-4307-ad27-873965f31971
-- title:
--   Gates over $\{H,S,T,X,\mathrm{CNOT}\}$ with controlled quantum-oracle and classical-oracle gates
-- statement:
--   A gate of an explicit oracle circuit, over the fixed finite universal gate set $\{H,S,T,X,\mathrm{CNOT}\}$ plus two oracle gates. Wires are natural numbers.
--
--   1. $H$, $S$, $T$, $X$ on one wire, and CNOT with a control and a target wire;
--   2. a **controlled quantum-oracle call**: the component of the quantum oracle with a classical label $\ell$ acting on $k$ qubits is applied to a list of $k$ wires, controlled on a further wire;
--   3. a **classical call** to a Boolean oracle $O$: a list of query wires is measured in the computational basis (deferred: copied onto fresh ancilla wires), and $O(\text{query})$ is XORed onto a target wire.
--
--   The paper uses "a fixed finite universal gate set" without naming one; this is the gate set of all circuits in the supplement.
--
--   **Formalization Note** Every quantum oracle call is controlled (an uncontrolled call is a call controlled on a wire set to $|1\rangle$). The label addresses a component of a tagged oracle (Section 6); the Section 5 oracle ignores it.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.1, p.8; Section 5, p.15; Section 6.1, p.16

import Mathlib

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- A gate of an explicit quantum circuit with oracle access, over the fixed finite gate set
`{H, S, T, X, CNOT}` plus two oracle gates. Wires are natural numbers.

* `h i`, `s i`, `t i`, `x i` — the single-qubit gates `H`, `S`, `T`, `X` on wire `i`;
* `cnot c t` — CNOT with control `c` and target `t`;
* `oracle lab c ws` — the **controlled quantum oracle call**: the component of the quantum
  oracle with classical label `lab` on `k = |ws|` qubits is applied to the wires `ws` (in
  order), controlled on wire `c`;
* `cquery qs anc tgt` — a **classical** call to a Boolean oracle `O`: the query wires `qs` are
  measured in the computational basis (deferred: copied onto the fresh ancilla wires `anc`,
  which no other gate touches), and `O(query)` is XORed onto wire `tgt`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.1, p.8 ("controlled oracle calls are allowed"); Section 5, p.15 ("using a fixed
finite universal gate set"); Section 6.1, p.16 ("explicit descriptions over a fixed finite
universal gate set"; "the distinguisher has quantum query access to T and classical access to
O, meaning that its query register is measured in the computational basis before each call").

**Formalization Note.** The gate set `{H, S, T, X, CNOT}` is one fixed finite universal gate
set (the paper fixes one without naming it). Every quantum oracle call is controlled; an
uncontrolled call is a controlled call on a wire set to `|1⟩` by `X`. The label `lab` addresses
a component of a tagged oracle (Section 6: testing block, yes sampler with tag `t`, no
sampler); for the Section 5 oracle, which has one component per length, it is ignored. -/
inductive QGate where
  | h (i : ℕ)
  | s (i : ℕ)
  | t (i : ℕ)
  | x (i : ℕ)
  | cnot (c tgt : ℕ)
  | oracle (lab : List ℕ) (c : ℕ) (ws : List ℕ)
  | cquery (qs anc : List ℕ) (tgt : ℕ)
  deriving DecidableEq

end QStateSearch.Supplement


