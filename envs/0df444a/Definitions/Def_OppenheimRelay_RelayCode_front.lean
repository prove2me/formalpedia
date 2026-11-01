-- Prove2me | Definitions.Def_OppenheimRelay_RelayCode_front
-- name    : OppenheimRelay_RelayCode_front
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:20.504984+00:00
-- url     : https://prove2.me/theorems/639b1215-8583-4331-b383-6c3d0986227b
-- title:
--   Alice and Charlie of a relay code, seen as one sender
-- statement:
--   For a relay code, the joint operation of Alice and Charlie: Alice's channel followed by Charlie's channel acting on Alice's message, which is transmitted as a quantum register (contracted coherently, never measured). The output is regrouped as Alice's final Bell halves, Charlie's $C^n$ and final Bell halves, and, last, Charlie's message to Bob.
--
--   It is the first two stages of the sequential composition that defines the whole protocol.
--
--   **Formalization Note** Built with the published `forwardApply` of the Devetak–Yard layer.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.2, protocol steps 1–3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_RelayCode

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **Alice and Charlie together.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.2, protocol steps 1–3: the joint operation of
Alice and Charlie, seen as one sender towards Bob. Alice's message to Charlie is transmitted by
`forwardApply`, as a quantum register. The output is regrouped so that Charlie's message to Bob is
the last factor. -/
noncomputable def RelayCode.front {A C B : Type*} [Fintype A] [Fintype C] [Fintype B] {n : ℕ}
    (P : RelayCode A C B n) :
    Superop ((Copies A n × Qubits P.kAC) × ((Copies C n × Qubits P.kAC) × Qubits P.kCB))
      ((Qubits P.lAC × ((Copies C n × Qubits P.lAC) × Qubits P.lCB)) × Qubits P.qCB) :=
  fun rho p p' =>
    forwardApply P.alice P.charlie rho (p.1.1, (p.1.2, p.2)) (p'.1.1, (p'.1.2, p'.2))

end OppenheimRelay


