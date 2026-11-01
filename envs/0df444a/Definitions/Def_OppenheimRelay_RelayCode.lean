-- Prove2me | Definitions.Def_OppenheimRelay_RelayCode
-- name    : OppenheimRelay_RelayCode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:23.024203+00:00
-- url     : https://prove2.me/theorems/ce622b5e-3e41-4085-8e9d-b17d85461f06
-- title:
--   Relay code of blocklength $n$: Alice → Charlie → Bob
-- statement:
--   A **relay code** of blocklength $n$ consists of six counts and three local quantum operations:
--
--   1. $q_{AC}$ qubits sent from Alice to Charlie and $q_{CB}$ qubits sent from Charlie to Bob;
--   2. $k_{AC}$ and $k_{CB}$ Bell pairs $|\phi^+\rangle$ shared at the start on the links Alice–Charlie and Charlie–Bob, and $l_{AC}$, $l_{CB}$ Bell pairs these links must share at the end;
--   3. Alice's channel, from $A^n$ and her $k_{AC}$ Bell halves to her $l_{AC}$ final halves and a $q_{AC}$-qubit message;
--   4. Charlie's channel, from Alice's message, $C^n$, his $k_{AC}$ and $k_{CB}$ Bell halves, to $C^n$, his $l_{AC}$ and $l_{CB}$ final halves and a $q_{CB}$-qubit message;
--   5. Bob's channel, from Charlie's message, $B^n$ and his $k_{CB}$ Bell halves, to $A^nB^n$ and his $l_{CB}$ final halves.
--
--   All three operations are completely positive trace-preserving maps between finite-dimensional systems. No party acts on the reference $R$.
--
--   This is the three-party protocol of the paper, "a more general three party protocol with Charlie acting as a relay station".
--
--   **Formalization Note** Messages flow only from Alice to Charlie to Bob, so collecting each party's operations into one channel applied after its incoming message arrives loses no generality. Local ancillas and discarded registers are absorbed into the rectangular channels. Alice's output does not contain $A^n$.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.2, "Alice is split into two parties…", box "Protocol: redistribution from merging", and the accounting sentence before the rate display

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

attribute [local instance] Classical.propDecidable Classical.decEq

/-- **A relay code of blocklength n.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.2, "Alice is split into two parties…", the box
"Protocol: redistribution from merging", and "Accounting for sent qubits Q^{A→C} between Alice and
Charlie and Q^{C→B} between Charlie and Bob, as well as consumed ebits".

`qAC`, `qCB` count the qubits sent on the two links, `kAC`, `kCB` the Bell pairs held at the start
of the protocol on the links Alice–Charlie and Charlie–Bob, and `lAC`, `lCB` the Bell pairs each
link must hold at the end. `alice`, `charlie`, `bob` are the three local operations.

**Formalization Note** Alice holds `A^n` and her `kAC` Bell halves; she keeps her `lAC` final
halves and sends the message, so her `A^n` is gone. Charlie holds `C^n`, his `kAC` and `kCB` Bell
halves and Alice's message, and outputs `C^n`, his final halves and his message. Bob holds `B^n`,
his `kCB` halves and Charlie's message, and outputs `A^n`, `B^n` and his final halves. No party's
input contains `R`. Local ancillas and discarded work are part of the arbitrary rectangular CPTP
maps. The order Alice, then Charlie, then Bob is general: no message flows backwards, so each party
can postpone every operation until the message addressed to it has arrived. -/
structure RelayCode (A C B : Type*) [Fintype A] [Fintype C] [Fintype B] (n : ℕ) where
  /-- Qubits sent from Alice to Charlie. -/
  qAC : ℕ
  /-- Qubits sent from Charlie to Bob. -/
  qCB : ℕ
  /-- Bell pairs shared by Alice and Charlie at the start. -/
  kAC : ℕ
  /-- Bell pairs shared by Alice and Charlie at the end. -/
  lAC : ℕ
  /-- Bell pairs shared by Charlie and Bob at the start. -/
  kCB : ℕ
  /-- Bell pairs shared by Charlie and Bob at the end. -/
  lCB : ℕ
  /-- Alice's operation. -/
  alice : Superop (Copies A n × Qubits kAC) (Qubits lAC × Qubits qAC)
  /-- Charlie's operation. -/
  charlie : Superop (Qubits qAC × ((Copies C n × Qubits kAC) × Qubits kCB))
    (((Copies C n × Qubits lAC) × Qubits lCB) × Qubits qCB)
  /-- Bob's operation. -/
  bob : Superop (Qubits qCB × (Copies B n × Qubits kCB))
    ((Copies A n × Copies B n) × Qubits lCB)
  alice_channel : IsChannel alice
  charlie_channel : IsChannel charlie
  bob_channel : IsChannel bob

end OppenheimRelay


