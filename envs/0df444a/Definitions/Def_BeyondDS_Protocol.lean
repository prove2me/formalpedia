-- Prove2me | Definitions.Def_BeyondDS_Protocol
-- name    : BeyondDS_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:41.657179+00:00
-- url     : https://prove2.me/theorems/dcce59b6-4767-4a38-a63a-b60c93fa4f3c
-- title:
--   Operations, model answers and protocols as state machines
-- statement:
--   An honest player interacts with the model through **operations**: sign a batch of messages under its own key; verify a batch of triples (identity $j$, message, signature) under $j$'s public key; draw a fresh private value uniform on $\{0,\dots,N\}$; send one point-to-point message to an identity; yield (no further action this round); decide a bit; halt. The model answers each operation: the signatures, the verdicts, the sampled value, an acknowledgement, or, after a yield, the messages delivered at the round's delivery boundary as (immediate sender, message) pairs together with the common election output if this boundary reveals one.
--
--   A **protocol** is one state machine for all parameters: an initial state of identity $i$ (the sender also receives its input bit), a transition $\mathrm{next}:\text{state}\times\text{answer}\to\text{operation}\times\text{state}$, and public caps: the number of rounds, the number of operations per round, and the public set of round boundaries at which an election output is revealed.
--
--   **Formalization Note** No operation carries a key, so a protocol is generic in the signature scheme and every signature is recorded by the model. A batch is one operation; the operations of one activation are atomic anyway, so a batch has the same power as a sequence, and a batch of adversarial records can be checked in full ("No fixed-size buffer truncation is permitted to discard a verifying record", p.22).
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §1.1, p.3 (PDF p.4) ("public execution caps"); §4.1, pp.11–12 (PDF pp.12–13); §7.1, pp.21–22 (PDF pp.22–23)

import Mathlib
import Definitions.Def_BeyondDS_Sig

set_option autoImplicit false

open QAlgorithms.Complexity

namespace BeyondDS

/-- One operation of an honest player, in the model of Rambaud, *Beyond Dolev–Strong*, STOC 2027
submission (manuscript sha256 c84cf9c9…), §§4.1, 7.1, pp.11–12, 21–22. Identities are natural numbers
`< n`.

* `signAll ms`: sign each message of the batch with fresh coins, under the player's own key.
* `verifyAll qs`: for each `(j, m, s)`, verify `s` on `m` under the public key of identity `j`.
* `sample N`: a fresh private value uniform on `{0, …, N}`.
* `send j msg`: one point-to-point transmission.
* `yield`: no further action in this round.
* `decide b`: output `b`; only the first decision counts.
* `halt`: stop forever.

**Formalization Note.** No constructor carries a key: the keys stay in the model, so a protocol is
generic in the signature scheme and each signature is logged. Batches are one operation, so a batch
of adversarial records can be checked in full within a bounded number of operations: "No fixed-size
buffer truncation is permitted to discard a verifying record" (p.22). The operations of one activation
are atomic anyway, so a batch has the same power as a sequence. -/
inductive Op (Msg : Type) where
  | signAll (ms : List Str)
  | verifyAll (qs : List (ℕ × Str × Str))
  | sample (N : ℕ)
  | send (j : ℕ) (msg : Msg)
  | yield
  | decide (b : Bool)
  | halt

/-- The model's answer to the previous operation. `start` is the answer before the first operation.
`boundary inbox elect` answers `yield`: what was delivered at the round's delivery boundary, as
`(immediate sender, message)` pairs in order of arrival ("channels identify their immediate sender",
p.14), and the common election output if this boundary reveals one. -/
inductive Resp (Msg : Type) where
  | start
  | signatures (ss : List Str)
  | verdicts (vs : List Bool)
  | sampled (k : ℕ)
  | done
  | boundary (inbox : List (ℕ × Msg)) (elect : Option ℕ)

/-- A protocol: one state machine for all parameters (`paper.md` decision 4), driven by
`next : state → answer → operation × state`.

* `init P i input`: the initial state of identity `i`; `input` is the sender's bit and `none` for
  everyone else.
* `roundCap P`: the public execution cap, in rounds (p.3: "public execution caps").
* `opCap P`: the number of operations a player may use per round; further operations are not run.
* `electAt P r`: whether the delivery boundary of round `r` (counted from `0`) reveals an election
  output. Election times are public and lie at a boundary, after every send of that round. -/
structure Protocol (Msg St : Type) where
  init : (P : Params) → Fin P.n → Option Bool → St
  next : Params → St → Resp Msg → Op Msg × St
  roundCap : Params → ℕ
  opCap : Params → ℕ
  electAt : Params → ℕ → Bool

end BeyondDS


