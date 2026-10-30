-- Prove2me | Definitions.Def_AKNMixed_FQP_QGate
-- name    : AKNMixed_FQP_QGate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:38.162007+00:00
-- url     : https://prove2.me/theorems/90d5ffb5-99f5-4b75-844a-e327e5439835
-- title:
--   Gate of order $(k,l)$ (Definition 1)
-- statement:
--   A **gate of order $(k,l)$** is a super-operator $g$ from $k$-qubit matrices to $l$-qubit matrices, written $\rho\mapsto g\circ\rho$. A `QGate` records $k$ (`inOrd`), $l$ (`outOrd`) and the map. The predicate $\mathrm{IsQuantum}(g)$ says that the map is linear, trace preserving and completely positive; a **quantum gate** in the sense of Definition 1 is a `QGate` satisfying it.
--
--   A gate set $\mathcal G$ is a set of `QGate`s.
--
--   **Formalization Note** The basis of an $n$-qubit register is $\{0,1\}^n$, encoded as `Qubits n = Fin n → Bool` ($\mathtt{false}=|0\rangle$, wire $0$ most significant). The property is kept separate from the data so that concrete gates (unitary conjugations) are written down without proofs; the theorems assume $\mathrm{IsQuantum}$ where the paper says "gate".
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Definition 1, p. 7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_AKNMixed_FQP_IsQuantumOperation

namespace AKNMixed.FQP

open QAlgorithms

/-- **A gate of order `(k, l)`: a super-operator from `k`-qubit to `l`-qubit matrices.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Definition 1, p. 7: "A quantum gate, g, of order (k, l) is a trace preserving, completely
positive, linear map from density matrices on k qubits to density matrices on l qubits."

A `QGate` records its order `(inOrd, outOrd)` = the paper's `(k, l)` and its map
`map : Superop (Qubits inOrd) (Qubits outOrd)`. The predicate `QGate.IsQuantum` says that the map
is a quantum operation (linear, trace preserving, completely positive); a *quantum gate* in the
sense of Definition 1 is a `QGate` with `IsQuantum`.

**Formalization Note.** The structure is unbundled: the property is the separate predicate
`IsQuantum`, so that concrete gates (unitary conjugations) are written down without proofs, and
the goal theorem assumes `IsQuantum` for every gate of `G`. An `n`-qubit register has basis
`Qubits n = Fin n → Bool` (`false` = `|0⟩`, wire `0` most significant). A gate set is a
`Set QGate`. -/
structure QGate where
  /-- The number `k` of input qubits. -/
  inOrd : ℕ
  /-- The number `l` of output qubits. -/
  outOrd : ℕ
  /-- The super-operator `ρ ↦ g ∘ ρ`. -/
  map : Superop (Qubits inOrd) (Qubits outOrd)

/-- Definition 1, p. 7: the gate's map is linear, trace preserving and completely positive. -/
def QGate.IsQuantum (g : QGate) : Prop :=
  IsQuantumOperation g.map

end AKNMixed.FQP


