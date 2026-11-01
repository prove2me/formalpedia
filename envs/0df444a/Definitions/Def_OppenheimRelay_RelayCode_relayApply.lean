-- Prove2me | Definitions.Def_OppenheimRelay_RelayCode_relayApply
-- name    : OppenheimRelay_RelayCode_relayApply
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:28:23.145986+00:00
-- url     : https://prove2.me/theorems/5928d439-79ca-4082-ba52-5901ec9d81ec
-- title:
--   The whole relay protocol as one channel
-- statement:
--   For a relay code, the channel on all registers of the three parties (the reference $R$ excluded): Alice, then Charlie on Alice's message, then Bob on Charlie's message. Both messages are transmitted as quantum registers.
--
--   Input: $A^n$ with Alice's $k_{AC}$ Bell halves; $C^n$ with Charlie's $k_{AC}$ and $k_{CB}$ halves; $B^n$ with Bob's $k_{CB}$ halves. Output: Alice's $l_{AC}$ halves; $C^n$ with Charlie's $l_{AC}$ and $l_{CB}$ halves; $A^nB^n$ with Bob's $l_{CB}$ halves.
--
--   **Formalization Note** Built with the published `forwardApply` applied to `RelayCode.front` and Bob's channel.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.2, protocol steps 1–3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_RelayCode_front

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **The whole relay protocol.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.2, protocol steps 1–3: Alice, then Charlie on her
message, then Bob on Charlie's message, on all the registers of the three parties (`R` excluded).
Both messages are contracted coherently by the published `forwardApply`, so neither is measured. -/
noncomputable def RelayCode.relayApply {A C B : Type*} [Fintype A] [Fintype C] [Fintype B] {n : ℕ}
    (P : RelayCode A C B n) :
    Superop (((Copies A n × Qubits P.kAC) × ((Copies C n × Qubits P.kAC) × Qubits P.kCB)) ×
        (Copies B n × Qubits P.kCB))
      ((Qubits P.lAC × ((Copies C n × Qubits P.lAC) × Qubits P.lCB)) ×
        ((Copies A n × Copies B n) × Qubits P.lCB)) :=
  forwardApply P.front P.bob

end OppenheimRelay


