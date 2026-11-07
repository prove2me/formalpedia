-- Prove2me | Definitions.Def_BeyondDS_Config
-- name    : BeyondDS_Config
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:07:55.861887+00:00
-- url     : https://prove2.me/theorems/e795107b-5844-45a9-a323-03f67b000c53
-- title:
--   Observations, adaptive adversaries and execution configurations
-- statement:
--   **Observations.** The adversary observes the public keys; every honest transmission in full (sender, destination, contents); the current state, pending model answer and secret key of each newly corrupted player; each election output at its reveal; and each round boundary.
--
--   **Adversary.** An adaptive adversary is an arbitrary randomized stateful strategy: a state space, an initial law, and a kernel which, from its state and its pending observations, draws a new state and a **decision**: a set of new corruptions, messages to inject through corrupted identities, and the honest player that acts next (or "end the round").
--
--   **Configuration.** The state of an execution records the round, the corrupted set and the round of each corruption, the keys, the log of (identity, message) pairs signed while honest, every player's local state and pending answer, activity and per-round operation budgets, the inboxes of the current round, first decisions, the adversary's state and pending observations, the whole transcript, and the round at which every uncorrupted player had halted. A player is **uncorrupted through round $r$** if it was not corrupted during rounds $0,\dots,r$, and **forever honest** if never corrupted. A start configuration can carry an already corrupted set, a log of earlier signatures and an adversary state: it represents a fixed reachable prefix.
--
--   **Formalization Note** The adversary's state type and kernel are unrestricted, so "the execution's probability space includes … the adversary's randomness" (p.13) needs no tape and the adversary may be computationally unbounded; computational limits are imposed separately (`ReactiveFamily`). Self-deliveries are also shown to the adversary, a slightly stronger adversary than the paper requires.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §4.1, pp.11–12 (PDF pp.12–13); §4.3, p.13 (PDF p.14); §7.1, pp.21–22 (PDF pp.22–23)

import Mathlib
import Definitions.Def_BeyondDS_Protocol

set_option autoImplicit false

open QAlgorithms.Complexity

namespace BeyondDS

/-- What the adversary observes (§§4.1, 7.1, pp.12, 22): the public keys; every honest transmission in
full, with sender, destination and contents; the current state, pending answer and secret key of each
newly corrupted player; each election output at its reveal; and each round boundary.

**Formalization Note.** Self-deliveries are shown as well. The paper only requires transmissions to be
visible, so this is a slightly stronger adversary. -/
inductive Obs (n : ℕ) (Msg St : Type) where
  | keys (pk : Fin n → Str)
  | sent (i j : Fin n) (msg : Msg)
  | revealed (i : Fin n) (st : St) (resp : Resp Msg) (sk : Str)
  | elected (r : ℕ) (L : Fin n)
  | boundary (r : ℕ)

/-- The full transcript of an execution; the adversary sees only the `obs` part.

* `injected f t msg`: a message of the adversary, sent through the corrupted identity `f`.
* `state i st`: the local state of an honest player at the end of an activation.
* `signed i m`: identity `i` signed `m` while honest.
* `forgery i j m`: the honest player `i` verified a signature of `j` on `m`, with `j` uncorrupted and
  `(j, m)` not yet signed. -/
inductive Event (n : ℕ) (Msg St : Type) where
  | obs (o : Obs n Msg St)
  | injected (f t : Fin n) (msg : Msg)
  | state (i : Fin n) (st : St)
  | signed (i : Fin n) (m : Str)
  | forgery (i j : Fin n) (m : Str)

/-- One move of the adversary: new corruptions; messages through corrupted identities; and which
honest player acts next (`none` means "end the round"). -/
structure Decision (n : ℕ) (Msg : Type) where
  corrupt : Finset (Fin n)
  inject : List (Fin n × Fin n × Msg)
  next : Option (Fin n)

/-- An adaptive adversary (§4.1, p.11; §4.3, p.13): an arbitrary randomized stateful strategy.

**Formalization Note.** `σ` is an arbitrary type and `step` an arbitrary kernel, so "the execution's
probability space includes … the adversary's randomness" (p.13) needs no tape and no restriction on its
computation. Computational bounds are imposed separately by `BeyondDS.ReactiveFamily`. -/
structure Adversary (n : ℕ) (Msg St : Type) where
  σ : Type
  init : PMF σ
  step : σ → List (Obs n Msg St) → PMF (σ × Decision n Msg)

/-- The state of an execution. It holds the whole history, so a configuration in the support of a
prefix of the execution is a "fixed reachable prefix" (§4.3, p.13).

* `round`: rounds completed so far.
* `corrupted`: the corrupted identities, and `corruptAt i` the round during which `i` was corrupted.
* `pk`, `sk`: the keys. `signLog`: every `(identity, message)` signed while honest.
* `st`, `resp`: local state and pending answer of each player.
* `active i`: `i` has not halted. `yielded i`: `i` finished this round. `budget i`: operations left.
* `inbox i`: messages to be delivered to `i` at this round's boundary.
* `decision i`: the first decision of `i`.
* `adv`, `obs`: the adversary's state and its observations not yet handed over.
* `log`: the transcript, oldest first.
* `doneAt`: the number of rounds completed when every uncorrupted player had first halted. -/
structure Config (n : ℕ) (Msg St σ : Type) where
  round : ℕ
  corrupted : Finset (Fin n)
  corruptAt : Fin n → Option ℕ
  pk : Fin n → Str
  sk : Fin n → Str
  signLog : List (Fin n × Str)
  st : Fin n → St
  resp : Fin n → Resp Msg
  active : Fin n → Bool
  yielded : Fin n → Bool
  budget : Fin n → ℕ
  inbox : Fin n → List (ℕ × Msg)
  decision : Fin n → Option Bool
  adv : σ
  obs : List (Obs n Msg St)
  log : List (Event n Msg St)
  doneAt : Option ℕ

/-- `i` is still uncorrupted at the delivery boundary of round `r` (counted from `0`). -/
def Config.UncorruptedThrough {n : ℕ} {Msg St σ : Type} (c : Config n Msg St σ) (i : Fin n)
    (r : ℕ) : Prop :=
  ∀ q, c.corruptAt i = some q → r < q

/-- `i` was never corrupted in this execution ("forever honest", p.11). -/
def Config.ForeverHonest {n : ℕ} {Msg St σ : Type} (c : Config n Msg St σ) (i : Fin n) : Prop :=
  i ∉ c.corrupted

/-- A configuration at the start of an instance. The prefix is the set `C₀` of players already
corrupted, the keys, the log of earlier signatures and the adversary's state. -/
def Config.start {Msg St σ : Type} (Pi : Protocol Msg St) (P : Params) (x : Bool)
    (pk sk : Fin P.n → Str) (C₀ : Finset (Fin P.n)) (signLog : List (Fin P.n × Str)) (adv : σ)
    (obs : List (Obs P.n Msg St)) : Config P.n Msg St σ where
  round := 0
  corrupted := C₀
  corruptAt := fun i => if i ∈ C₀ then some 0 else none
  pk := pk
  sk := sk
  signLog := signLog
  st := fun i => Pi.init P i (if i = P.sender then some x else none)
  resp := fun _ => Resp.start
  active := fun _ => true
  yielded := fun _ => false
  budget := fun _ => 0
  inbox := fun _ => []
  decision := fun _ => none
  adv := adv
  obs := obs
  log := []
  doneAt := none

end BeyondDS


