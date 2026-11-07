-- Prove2me | Definitions.Def_ByzSigT_Protocol
-- name    : ByzSigT_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:52:39.897146+00:00
-- url     : https://prove2.me/theorems/193fd5ed-67e3-47db-8023-5397061627f3
-- title:
--   Deterministic event-driven protocols and well-formedness
-- statement:
--   A **protocol** for $n$ parties with a $k$-SigT setup is a deterministic state machine: a state type, an initial state for each party $p$ and input $u\in\{0,1\}$, and a handler that maps a party, a state and a local event to a new state and a finite list of actions.
--
--   The local events are the start, the arrival of a term on the authenticated link from a named sender, the expiry of a timer, and the environment's reply to a SigT use. The actions are sending a term to a named party, setting a timer of a given duration, using token index $i$ on a term, and deciding a value. No action reads a clock, the stabilization time, or the state or input of another party.
--
--   A protocol is **well-formed** when two conditions hold for every party and every local history:
--
--   1. every term the party sends or token-signs is derivable from the terms it has received and its token replies, using only its own PKI key;
--   2. every timer duration is at least a fixed $d_0>0$.
--
--   The first condition means a correct party cannot forge a signature or a token, which is what gives the limit of one use per token index its force. The second means a protocol cannot force infinitely many events into a bounded time interval, which would leave it without executions and make its security vacuous.
--
--   **Formalization Note** The state type is a field of the structure. The protocol may depend on any data it is built from; in Theorem 4.1 these are $f$ and $\Delta$.
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), §2, pp.4–5 (PDF 5–6); Theorem 4.1, p.12 (PDF 13)

import Mathlib
import Definitions.Def_ByzSigT_Term

namespace ByzSigT

/-!
# Deterministic protocols and well-formedness

Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…), §2 "Model", "Partial synchrony & The adversary" and
"SigT setup", pp.4–5; "deterministic" as in Theorem 4.1, p.12.

A protocol for `n` parties with a `k`-SigT setup is a deterministic event-driven state machine run
by every correct party `p : Fin n`. It starts from `init p u` on input `u : Bool` and reacts to
local events with a new state and a finite list of actions.

**Formalization Note.**
* Local events: `start` (the party begins executing), `recv src t` (a term `t` arrives on the
  authenticated link from `src`), `timer id` (a timer set earlier expires), `sigtReply i t` (the
  environment returns the token `t` for a use of index `i`).
* Actions: `send dst t`, `setTimer id d` (a relative timer of local duration `d`), `useSigT i t`
  (the paper's "Use `SigT^{(i+1)}(t)`"), `decide v` (the party decides `v`).
* Time is seen only through relative timers: no action reads a clock, GST, global time, or
  another party's state or input. The protocol may depend on `n`, `k` (its type) and on any data
  it is built from (in Theorem 4.1: `f` and `Δ`).
* `WellFormed`: along every local event history, every term the party sends or token-signs is
  derivable from what it has received and its own token replies, with only its own PKI key
  (`Derivable {p} ∅`); so a protocol cannot forge another party's signature or any token. Also
  every timer duration is at least some fixed `d₀ > 0`, so that a protocol cannot force infinitely
  many events into a bounded time interval (which would leave it without executions).
-/

/-- A local event of a party. -/
inductive LocalEvent (n k : ℕ) : Type where
  | start : LocalEvent n k
  | recv (src : Fin n) (t : Term n k) : LocalEvent n k
  | timer (id : ℕ) : LocalEvent n k
  | sigtReply (i : Fin k) (t : Term n k) : LocalEvent n k

/-- An action emitted by a party's handler. -/
inductive Action (n k : ℕ) : Type where
  | send (dst : Fin n) (t : Term n k) : Action n k
  | setTimer (id : ℕ) (d : ℝ) : Action n k
  | useSigT (i : Fin k) (t : Term n k) : Action n k
  | decide (v : Bool) : Action n k

/-- The terms an action sends or token-signs. -/
def Action.terms {n k : ℕ} : Action n k → List (Term n k)
  | .send _ t => [t]
  | .useSigT _ t => [t]
  | _ => []

/-- `isUse i a`: the action `a` is a use of token index `i`. -/
def Action.isUse {n k : ℕ} (i : Fin k) : Action n k → Bool
  | .useSigT j _ => Decidable.decide (j = i)
  | _ => false

/-- A deterministic protocol: a local state type, the initial state of party `p` on input `u`, and
the handler. -/
structure Protocol (n k : ℕ) where
  /-- The local state of a party. -/
  State : Type
  /-- The initial state of party `p` with input `u`. -/
  init : Fin n → Bool → State
  /-- The handler: new state and emitted actions. -/
  step : Fin n → State → LocalEvent n k → State × List (Action n k)

namespace Protocol

variable {n k : ℕ}

/-- The state of party `p` with input `u` after the local history `h` (oldest event first). -/
def run (P : Protocol n k) (p : Fin n) (u : Bool) (h : List (LocalEvent n k)) : P.State :=
  h.foldl (fun s e => (P.step p s e).1) (P.init p u)

/-- What a party knows after the local history `h`: every term it received and every token
reply. -/
def knowledge (h : List (LocalEvent n k)) : Set (Term n k) :=
  {t | ∃ src, LocalEvent.recv src t ∈ h} ∪ {t | ∃ i, LocalEvent.sigtReply i t ∈ h}

/-- Well-formedness (see the module note): every sent or token-signed term is derivable by `p`
alone from its knowledge, including the event being handled, and timer durations are bounded
below by a positive constant. -/
def WellFormed (P : Protocol n k) : Prop :=
  (∀ (p : Fin n) (u : Bool) (h : List (LocalEvent n k)) (e : LocalEvent n k),
      ∀ a ∈ (P.step p (P.run p u h) e).2, ∀ t ∈ a.terms,
        Derivable {p} ∅ (knowledge (h ++ [e])) t) ∧
  ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (p : Fin n) (u : Bool) (h : List (LocalEvent n k)) (e : LocalEvent n k)
      (id : ℕ) (d : ℝ), Action.setTimer id d ∈ (P.step p (P.run p u h) e).2 → d₀ ≤ d

end Protocol

end ByzSigT


