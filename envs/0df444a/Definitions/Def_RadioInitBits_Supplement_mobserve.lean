-- Prove2me | Definitions.Def_RadioInitBits_Supplement_mobserve
-- name    : RadioInitBits_Supplement_mobserve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:04:21.536232+00:00
-- url     : https://prove2.me/theorems/b32ee5ed-f1f6-4c9c-8ad1-43b7c2b1fa6d
-- title:
--   The no-CD single-hop radio channel with multi-bit messages
-- statement:
--   In Section 4 of the paper the nodes of a **single-hop radio network** send messages of $O(\log n)$ bits instead of single bits. In each synchronous round a node **sleeps**, **listens**, or **transmits** a message $m$, a finite string of bits.
--
--   The **no-CD channel** decides what each node observes at the end of a round:
--
--   1. a listening node **hears** $m$ if exactly one node transmits and that node transmits $m$;
--   2. a listening node hears **silence** if no node transmits, or if two or more nodes transmit (even the same message); it cannot tell these cases apart (no collision detection);
--   3. a transmitting node and a sleeping node learn nothing (no sender-side feedback).
--
--   Given the actions of all $n$ nodes in one round, the definition returns the observation of node $i$.
--
--   This is the multi-bit analogue of the published single-bit channel `RadioInitBits.observe`; it is the communication model of Theorem 3.
--
--   **Formalization Note** Nodes are `Fin n`. A message is a `List Bool` of any length: the $O(\log n)$ length bound is a property of a protocol, stated in Theorem 3, not of the channel. An observation is `none`, `silence` or `heard m`; there is no collision value.
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), full version §2.1, pp.4–5 (PDF pp.25–26) and §2.1.1, p.5 (PDF p.26); message size: "In Section 4, we assume O(log n)-bit message sizes", p.5 (PDF p.26)

import Mathlib

set_option autoImplicit false

namespace RadioInitBits

namespace Supplement

/-- The action of one node in one round of a single-hop radio network with **multi-bit
messages**: sleep, listen, or transmit a message `m`, a finite string of bits.
D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), full version §2.1, p.4 (PDF p.25): "In any round, a
node can either transmit, listen, or sleep. When a node transmits, it broadcasts the same message
to all neighbors. The model can be parameterized by the size of messages", and p.5 (PDF p.26):
"In Section 4, we assume O(log n)-bit message sizes".

**Formalization Note** A message is a `List Bool` of any length; the length bound `O(log n)` is not
part of the channel but a property of a protocol (`MProtocol.MsgBounded`), stated in Theorem 3. -/
inductive MAction where
  /-- The node sleeps: it neither sends nor receives. -/
  | sleep
  /-- The node listens to the channel. -/
  | listen
  /-- The node transmits the message `m`. -/
  | send (m : List Bool)
  deriving DecidableEq

/-- The message a node transmits under an action: `some m` for `send m`, `none` otherwise. -/
def MAction.msg? : MAction → Option (List Bool)
  | .send m => some m
  | _ => none

/-- What a node learns at the end of a round with multi-bit messages: `none` (it slept or
transmitted), `silence` (it listened and did not receive a message), or `heard m` (it listened and
received the message `m`).

**Formalization Note** There is no `collision` value: in the no-CD model a listener cannot tell
zero senders from two or more senders (full version §2.1, p.4, PDF p.25), and a transmitter
receives nothing ("there is no sender-side feedback", §2.1.1, p.5, PDF p.26). -/
inductive MObs where
  /-- No observation (the node slept or transmitted). -/
  | none
  /-- The node listened and heard silence: zero senders, or at least two senders. -/
  | silence
  /-- The node listened and exactly one node transmitted, the message `m`. -/
  | heard (m : List Bool)
  deriving DecidableEq

/-- The **no-CD single-hop channel** with multi-bit messages. Given the actions `acts j` of all
`n` nodes in one round, node `i` observes:

* `heard m` if `i` listens and exactly one node transmits, and that node transmits `m`;
* `silence` if `i` listens and zero or at least two nodes transmit;
* `none` if `i` sleeps or transmits.

Banasik, Dani, Hayes, STOC 2027 submission, full version §2.1, p.4 (PDF p.25): "When a node
listens, it hears a message if and only if exactly one of its neighbors transmits. In the no-CD
Model, a listening node cannot distinguish between zero neighbors sending and at least two
neighbors sending"; §2.1.1, p.5 (PDF p.26): "there is no sender-side feedback".

**Formalization Note** The network is a clique on `Fin n` (single hop). This is the multi-bit
analogue of the published single-bit channel `RadioInitBits.observe`; two simultaneous senders give
silence even when they send the same message. -/
noncomputable def mobserve {n : ℕ} (acts : Fin n → MAction) (i : Fin n) : MObs := by
  classical
  exact
    match acts i with
    | .listen =>
      if h : ∃ j, (acts j).msg?.isSome ∧ ∀ j', (acts j').msg?.isSome → j' = j then
        .heard ((acts h.choose).msg?.getD [])
      else .silence
    | _ => .none

end Supplement

end RadioInitBits


