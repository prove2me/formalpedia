-- Prove2me | Definitions.Def_ShiAuthentication_BA_Cost
-- name    : ShiAuthentication_BA_Cost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:13:37.064385+00:00
-- url     : https://prove2.me/theorems/66facfc1-ba8e-4428-ba37-a82eccc7bc2e
-- title:
--   Polynomial local computation (Turing machines) and honest communication in bits
-- statement:
--   Fix the prefix-free binary codec `encMsg`: a constructor uses three tag bits, numbers and keys have self-delimiting binary codes, and a signature is represented injectively by its key and signed term. This representation does not confer a signing capability. With the encoding convention of §3.1 fixed once, designated keys and identifiers have code length at most κ; the bounded-depth signatures used here have size O(κ). A fixed rescaling makes this a signature-size parameter. Arbitrary finite key assignments are covered by choosing a compatible budget.
--
--   The bit length of a message and total honest communication through round R are
--   $$|m|=\operatorname{length}(\operatorname{encMsg}(m)),\qquad
--    B_H(R)=\sum_{r<R}\sum_{i\in H}\sum_{j\in P}|m_{r,i,j}|.$$
--   Absent messages contribute zero. The measure includes every honest send and actual signed-term encodings.
--
--   For local work, each labelled channel supplies at most its permitted packet prefix plus one overflow bit. Oversized packets are discarded, and at most 5(t+1) rounds are retained. The explicit `inputReadWork` counts the bounded input reads. A single finite multi-stack Turing machine must compute the protocol's exact raw-view behavior from these bounded prefixes, returning the evaluated outgoing messages and decision in time polynomial in the encoded input length. Thus copying, signature generation/checking, parsing, expression evaluation and general maximum matching are charged. Under the setup encoding convention, both preprocessing and encoded input length are polynomial in n,t,κ, independently of adversarial packet length. The machine and polynomial precede all varying parameters; they are not instance-dependent witnesses.
--
--   This is the resource assertion used by Theorem 4.6 and Main Theorem 1. It assumes neither correct output nor an efficient matching oracle. The existence of a machine implementing the semantic maximum matching is part of the theorem conclusion.
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), §3.1 p. 15 (κ bounds signature size; keys and identifiers O(κ); ln n = O(κ)), Theorem 4.6 and its proof, pp. 21–22

import Definitions.Def_ShiAuthentication_BA_Protocols

set_option autoImplicit false

namespace ShiAuthentication.BA

/-! # Operational resource conventions

Shi §3.1 p.15 and Theorem 4.6 pp.21–22. `encMsg` is the actual wire codec, shared with the
parsers. A signature is represented by its key and signed term; this is an injective symbolic
representation, whose generation is still restricted by the execution's capability rules.
For the bounded-depth signatures used here its size is O(κ), with a fixed coefficient.
There is no assertion that infinitely many arbitrary signatures fit in a fixed finite alphabet
of κ-bit strings. Keys remain unbounded natural-number atoms; `Setup.EncodingOK` fixes the
source's encoding budget for each finite setup, without restricting adversarial strings.

The machine below computes EVALUATED outgoing messages, including copying, signing, signature
checking, parsing, and matching. Its input gives each channel's first `forwardLimit I + 1`
bits, and retains at most the fixed schedule's rounds. Oversized packets are discarded after
that prefix; the network delivers each packet on its separate sender-labelled channel.
Constructing this input requires at most that many reads per packet, independently of an
adversary's packet length. The protocol itself must ignore the discarded suffix: computing
its exact raw-view behavior from this prefix encoding is part of the machine assertion.
Under `EncodingOK`, the encoding has polynomial length in n,t,κ. One machine and one
polynomial must work for ALL inputs; there is no instance-dependent computation or cost oracle.
-/

/-- Code of initial data. Size parameters are unary; identifiers and keys use `encNat`. -/
def encInit (I : LocalInit) : List Bool :=
  encUnary I.n ++ encUnary I.t ++ encUnary I.κ ++ encNat I.session ++
    encNat I.self ++ encNat I.ownKey ++ encList encPair I.table ++
    encOption (fun b => [b]) I.input ++ encOption encNat I.sender ++
    encOption (encList encPair) I.graph

/-- The fixed public schedule used for this mission's bit-output protocol. Views past this
point have the same relevant prefix. This does not constrain arbitrary protocols in BAPossible. -/
def resourceHorizon (I : LocalInit) : ℕ := 5 * (I.t + 1)

/-- The actual n channels when t<n. On malformed initial records with t≥n, retain also
all syntactically named kings, so the universal machine assertion loses no inputs. -/
def resourceChannels (I : LocalInit) : ℕ := max I.n (I.t + 1)

/-- Bounded input from each channel, with an extra bit to distinguish overflow. A read of
`some m` is complete iff its code has length at most `forwardLimit I`. -/
def packetPrefix (I : LocalInit) (m : Msg) : List Bool :=
  (encMsg m).take (forwardLimit I + 1)

/-- Input encoding for a round: initial data and the first scheduled rounds, n separately
bounded packets per round. This includes missing channels explicitly. No full adversarial
packet is part of the input length. -/
def encLocalInput (x : LocalInit × View) : List Bool :=
  encInit x.1 ++ encList (fun row =>
    encList (encOption (packetPrefix x.1))
      ((List.range (resourceChannels x.1)).map (fun j => row.getD j none)))
    (x.2.take (resourceHorizon x.1))

/-- Bounded preprocessing read budget: the encoded initial data and at most L+1 bits
plus a presence marker on each separate channel, in each retained round. Discarding a packet
suffix is a channel operation; decoding the retained prefix is charged to the machine. -/
def inputReadWork (x : LocalInit × View) : ℕ :=
  (encInit x.1).length + (x.2.take (resourceHorizon x.1)).length * resourceChannels x.1 * (forwardLimit x.1 + 2)

/-- Actual outgoing messages and decision, rather than unevaluated expressions. The machine
must implement copying and expression evaluation as well as selecting the expressions. -/
def Protocol.wireStep (P : Protocol Bool) (x : LocalInit × View) :
    List (Option Msg) × Option Bool :=
  ((P.send x.1 x.2).map (Option.map (Expr.eval x.1.ownKey x.2)), P.decide x.1 x.2)

/-- Code of actual sends and decision. -/
def encLocalOutput (y : List (Option Msg) × Option Bool) : List Bool :=
  encList (encOption encMsg) y.1 ++ encOption (fun b => [b]) y.2

/-- A single Mathlib multi-stack Turing machine computes actual local behavior from bounded
channel prefixes in time polynomial in their encoded length. Combined with the explicit
bounded reads in `packetPrefix` this is uniform polynomial work in n,t,κ on admissible setups,
including executions with arbitrarily long malformed messages. Existence of this machine,
including a polynomial implementation of general maximum matching, is a theorem conclusion. -/
def PolyTimeLocal (P : Protocol Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encLocalInput encLocalOutput P.wireStep)

/-- Actual encoded bit length, including the signed term in this fixed codec. -/
def Msg.size (m : Msg) : ℕ := (encMsg m).length

/-- Total honest-sent communication in rounds `< R`, over the complete network. -/
def honestBits {n : ℕ} (s : Setup n) (tr : Trace n) (R : ℕ) : ℕ :=
  ∑ r ∈ Finset.range R, ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ∉ s.F),
    ∑ j : Fin n, ((tr r i j).map Msg.size).getD 0

end ShiAuthentication.BA


