-- Prove2me | Definitions.Def_RadioInitBits_observe
-- name    : RadioInitBits_observe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:07.613436+00:00
-- url     : https://prove2.me/theorems/6fca9001-1c87-4462-9466-5dc17406241f
-- title:
--   The no-CD single-hop radio channel with single-bit messages
-- statement:
--   In a **single-hop radio network** the $n$ nodes form a clique and share one channel. Communication happens in synchronous rounds. In each round a node either **sleeps**, **listens**, or **transmits** a message. In the single-bit setting the message is one bit $b\in\{0,1\}$.
--
--   The **no-CD channel** decides what each node observes at the end of a round:
--
--   1. a listening node **hears** the bit $b$ if exactly one node transmits and that node transmits $b$;
--   2. a listening node hears **silence** if no node transmits, *or if two or more nodes transmit*. It cannot tell these two cases apart (no collision detection);
--   3. a transmitting node learns nothing (no sender-side feedback), and a sleeping node learns nothing.
--
--   Given the actions of all $n$ nodes in a round, the definition returns the observation of node $i$: "heard $b$", "silence", or "nothing".
--
--   This channel is the communication model of the whole mission. Every execution of a protocol is built by applying it round after round.
--
--   **Formalization Note** Nodes are `Fin n`. An action is `sleep`, `listen` or `send b` with `b : Bool`. An observation is `none`, `silence` or `heard b`; there is no separate "collision" observation. "Exactly one sender, sending $b$" is encoded as: exactly one node sends $b$ and no node sends the other bit.
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), full version §2.1, pp.4–5 (PDF pp.25–26) and §2.1.1, p.5 (PDF p.26); same text in the short version, pp.4–5 (PDF pp.6–7)

import Mathlib

set_option autoImplicit false

namespace RadioInitBits

/-- The action of one node in one round of a single-hop radio network with **single-bit
messages**: sleep, listen, or transmit one bit `b`.
D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), full version §2.1, p.4 (PDF p.25): "In any round, a
node can either transmit, listen, or sleep", and p.5 (PDF p.26): "In Section 5, we restrict the
model to single-bit message sizes". -/
inductive Action where
  /-- The node sleeps: it neither sends nor receives. -/
  | sleep
  /-- The node listens to the channel. -/
  | listen
  /-- The node transmits the single bit `b`. -/
  | send (b : Bool)
  deriving DecidableEq

/-- What a node learns at the end of a round: `none` (it slept or transmitted), `silence`
(it listened and did not receive a message), or `heard b` (it listened and received the bit `b`).

**Formalization Note** There is no `collision` value: in the no-CD model a listener cannot tell
zero senders from two or more senders (full version §2.1, p.4, PDF p.25), and a transmitter
receives nothing ("there is no sender-side feedback", §2.1.1, p.5, PDF p.26). -/
inductive Obs where
  /-- No observation (the node slept or transmitted). -/
  | none
  /-- The node listened and heard silence: zero senders, or at least two senders. -/
  | silence
  /-- The node listened and exactly one node transmitted, the bit `b`. -/
  | heard (b : Bool)
  deriving DecidableEq

/-- The **no-CD single-hop channel** with single-bit messages. Given the actions `acts j` of all
`n` nodes in one round, node `i` observes:

* `heard b` if `i` listens and exactly one node transmits, and that node transmits `b`;
* `silence` if `i` listens and zero or at least two nodes transmit;
* `none` if `i` sleeps or transmits.

Banasik, Dani, Hayes, STOC 2027 submission, full version §2.1, p.4 (PDF p.25): "When a node
listens, it hears a message if and only if exactly one of its neighbors transmits. In the no-CD
Model, a listening node cannot distinguish between zero neighbors sending and at least two
neighbors sending"; §2.1.1, p.5 (PDF p.26): "there is no sender-side feedback".

**Formalization Note** The network is a clique on `Fin n` (single hop), so every node is every
other node's neighbor. "Exactly one sender, sending `b`" is written as: exactly one node sends `b`
and no node sends `!b`. A listener is not itself a sender. -/
def observe {n : ℕ} (acts : Fin n → Action) (i : Fin n) : Obs :=
  match acts i with
  | .listen =>
    if (Finset.univ.filter fun j => acts j = .send true).card = 1 ∧
        (Finset.univ.filter fun j => acts j = .send false).card = 0 then .heard true
    else if (Finset.univ.filter fun j => acts j = .send false).card = 1 ∧
        (Finset.univ.filter fun j => acts j = .send true).card = 0 then .heard false
    else .silence
  | _ => .none

end RadioInitBits


