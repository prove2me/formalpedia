-- Prove2me | Definitions.Def_AKNMixed_FQP_consumeProduce
-- name    : AKNMixed_FQP_consumeProduce
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:57.80922+00:00
-- url     : https://prove2.me/theorems/a00df073-fe57-4400-95c6-19a81bf24ba4
-- title:
--   A gate of order $(k,l)$ acting on its input wires and fresh output wires
-- statement:
--   Let $T$ be a super-operator from $k$ to $l$ qubits. On $k+l$ wires, the first $k$ being the gate's input wires and the last $l$ its output wires, define
--
--   $$\mathrm{consumeProduce}(T)(X)=|0^k\rangle\langle0^k|\otimes T\bigl(\operatorname{Tr}_{\text{last }l}X\bigr).$$
--
--   The output wires are traced out (they are fresh and hold $|0\rangle$), $T$ is applied to the inputs, its result is written on the output wires, and the consumed input wires are left in $|0\rangle$.
--
--   This is the action of one node of a circuit (Definitions 2–3) in the wire-pool encoding used by this mission: a node of order $(k_v,l_v)$ has in-degree $k_v$ and out-degree $l_v$.
--
--   **Formalization Note** Consumed wires are never read again in a well-formed circuit, so resetting them to $|0\rangle$ is the same as discarding them. Bit order: input wires first (`Fin.append`).
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Definition 2, p. 7; Definition 3, p. 8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel

namespace AKNMixed.FQP

open QAlgorithms

/-- **A gate of order `(k, l)` as an operation on its `k` input wires and `l` fresh output
wires.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Definition 2, p. 7 (a node of order `(k_v, l_v)` has in-degree `k_v` and out-degree `l_v`) and
Definition 3, p. 8 (`Q ∘ ρ = g_t ∘ … ∘ g_1 ∘ ρ`).

For a super-operator `T` from `k` to `l` qubits, `consumeProduce T` acts on `k + l` wires, the
first `k` being the gate's input wires and the last `l` its output wires:
`X ↦ |0^k⟩⟨0^k| ⊗ T(Tr_{last l} X)`. It reads the inputs, traces out the (fresh) output wires,
writes `T`'s output on the output wires, and leaves the consumed input wires in `|0⟩`.

**Formalization Note.** This is the step of a node in the wire-pool encoding of a circuit
(`AKNMixed.FQP.Node.step`): output wires are unused before the node and so hold `|0⟩`, and
consumed input wires are never read again, so resetting them to `|0⟩` is the same as discarding
them. Wire order: `Fin.append`, input wires first. -/
noncomputable def consumeProduce {k l : ℕ} (T : Superop (Qubits k) (Qubits l)) :
    Superop (Qubits (k + l)) (Qubits (k + l)) :=
  fun X => Matrix.of fun y z =>
    if (fun i => y (Fin.castAdd l i)) = (fun _ => false) ∧
        (fun i => z (Fin.castAdd l i)) = (fun _ => false) then
      T (Matrix.of fun a b => ∑ c : Qubits l, X (Fin.append a c) (Fin.append b c))
        (fun j => y (Fin.natAdd k j)) (fun j => z (Fin.natAdd k j))
    else 0

end AKNMixed.FQP


