-- Prove2me | Definitions.Def_ByzSigT_IsExecution
-- name    : ByzSigT_IsExecution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:53:53.424886+00:00
-- url     : https://prove2.me/theorems/789a4323-6489-4ba1-baee-0166b0940e3e
-- title:
--   Executions in partial synchrony with a static Byzantine adversary and a k-SigT setup
-- statement:
--   An **execution** is a sequence of global events indexed by $\mathbb N$ with real times: the start of a party, the delivery of a term from a sender to a receiver, a timer firing, a SigT reply, or an idle event. It is an execution of a protocol $P$ with corrupt set $F$, inputs $u$, stabilization time $\mathrm{GST}$ and delay bound $\Delta$ when:
--
--   1. times start at a nonnegative value, never decrease and are unbounded;
--   2. each correct party starts exactly once, at a time at most $\mathrm{GST}$, has no local event before its start, and its states and actions are obtained by running the handler over its own local events;
--   3. a term sent by a correct party at time $\tau$ is delivered by time $\max(\tau,\mathrm{GST})+\Delta$, and nothing is delivered with a correct sender unless that sender sent it;
--   4. a delivery with a corrupt sender carries a term derivable, with the corrupt parties' keys and tokens, from everything correct parties have sent so far; and for a corrupt party $q$ and index $i$, at most one content $t$ has $\mathrm{SigT}^{(i)}_q(t)$ occurring in any delivered term;
--   5. a timer of duration $d$ set at time $\tau$ fires at a time in $[\tau,\max(\tau,\mathrm{GST})+d]$, exactly at $\tau+d$ when $\tau\ge\mathrm{GST}$, and every firing comes from a timer that was set;
--   6. a timer of a correct party that fires at time $\tau$ is handled after the deliveries to that party at time $\tau$ of messages correct parties sent before the timer event; all other simultaneous events are ordered by the adversary;
--   7. the first use of index $i$ by a correct party $p$ on a term $t$ is answered at the same time by $\mathrm{SigT}^{(i)}_p(t)$, any later use of $i$ does nothing, and every reply comes from such a first use.
--
--   This is the paper's partially synchronous model with a static adversary, in which corrupt parties may equivocate, stay silent, delay and replay. Their only limits are clauses 4 and 6.
--
--   **Formalization Note** Unbounded times exclude Zeno executions, which would make termination false for every protocol. Executions exist for every well-formed protocol because a second use of a token is a no-op rather than a violation. Delivery is at least once and timers may fire several times in their window; both give the adversary more power than the paper's model.
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), §2, pp.4–5 (PDF 5–6), and §4.2.2, p.24 (PDF 25)

import Mathlib
import Definitions.Def_ByzSigT_Protocol

namespace ByzSigT

/-!
# Executions in partial synchrony with a static Byzantine adversary and a k-SigT setup

Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…), §2, pp.4–5: "any message broadcast at time τ is received
by time max(τ, GST) + ∆"; "all correct processes begin executing the protocol on or before GST";
"hardware clocks, while subject to arbitrary skew & drift before GST, do not drift after GST"; the
adversary selects `F ⊆ [n]` at the beginning, given the protocol code, and corrupt parties "may
exhibit arbitrary behavior"; a `k`-SigT setup gives each party one use of each index
`i ∈ {1, …, k}`, "Each index can be used once, regardless of the other indices".

An execution is a sequence of global events indexed by `ℕ` with real times. `IsExecution P F u GST Δ E`
says that `E` is an execution of protocol `P` with corrupt set `F`, inputs `u`, global stabilization
time `GST` and delay bound `Δ`.

**Formalization Note.**
* Times are real, start at `≥ 0`, are non-decreasing and unbounded (no Zeno executions). Events at
  equal times are ordered arbitrarily, i.e. adversarially. `idle` events let every prefix extend.
* Each correct party starts exactly once, at a time `≤ GST`, and has no local event before its
  start. Its states and actions are the fold of the handler over its own local events
  (`stateAt`, `actionsAt`), starting from `init p (u p)`: it sees nothing else.
* Links are authenticated: a delivery records its true sender. A term sent by a correct party at
  time `τ` is delivered to its destination at least once, at a later position, by time
  `max(τ, GST) + Δ`; nothing is delivered with a correct sender unless that sender sent it.
  The adversary may delay within this window, reorder, and duplicate deliveries.
* Simultaneous events are ordered adversarially, with one exception (`timer_after_delivery`): a timer
  of a correct party that fires at time `τ` is handled after every delivery to that party at time `τ`
  of a message a correct party sent before that timer event. This is the paper's "by time" (p.24: "By
  time t + 2∆ ≤ t_ℓ + 2∆, the leader receives the suggest messages of all correct parties", with the
  leader's Wait 2∆ ending at `t_ℓ + 2∆`): a message received by time `τ` is available at `τ`.
* Corrupt parties are the adversary: deliveries with a corrupt sender are arbitrary terms subject
  only to derivability (`Derivable F F`) from every term the correct parties sent before (the
  adversary sees all traffic) and to token uniqueness: for a corrupt `q` and an index `i`, at most
  one content `t` has `tok q i t` occurring in any delivered term.
* Clocks are relative timers: a timer of duration `d` set at time `τ` fires at a later position, at a
  time in `[τ, max(τ, GST) + d]`, and exactly at `τ + d` when `τ ≥ GST`. Every firing comes from a
  timer that was set.
* SigT: the first use of index `i` by a correct party `p` (`FreshUse`) is answered by the token
  `tok p i t` at a later position at the same time; any later use of `i` is a no-op. Every reply
  comes from a fresh use.
-/

/-- A global event of an execution. -/
inductive Event (n k : ℕ) : Type where
  | start (p : Fin n) : Event n k
  | deliver (src dst : Fin n) (t : Term n k) : Event n k
  | timer (p : Fin n) (id : ℕ) : Event n k
  | sigtReply (p : Fin n) (i : Fin k) (t : Term n k) : Event n k
  | idle : Event n k

/-- The local event that a global event is for party `p`, if any. -/
def Event.localFor {n k : ℕ} (p : Fin n) : Event n k → Option (LocalEvent n k)
  | .start q => if q = p then some .start else none
  | .deliver src dst t => if dst = p then some (.recv src t) else none
  | .timer q id => if q = p then some (.timer id) else none
  | .sigtReply q i t => if q = p then some (.sigtReply i t) else none
  | .idle => none

/-- An execution: the event at each position and its real time. -/
structure Execution (n k : ℕ) where
  /-- The event at position `j`. -/
  ev : ℕ → Event n k
  /-- The real time of position `j`. -/
  time : ℕ → ℝ

namespace Execution

variable {n k : ℕ}

/-- The local history of `p` before position `j` (oldest first). -/
def hist (E : Execution n k) (p : Fin n) (j : ℕ) : List (LocalEvent n k) :=
  (List.range j).filterMap (fun m => (E.ev m).localFor p)

/-- The state of `p` (running `P` with input `u p`) just before position `j`. -/
def stateAt (E : Execution n k) (P : Protocol n k) (u : Fin n → Bool) (p : Fin n) (j : ℕ) :
    P.State :=
  P.run p (u p) (E.hist p j)

/-- The actions that `p` (running `P`) emits when handling the event at position `j`. -/
def actionsAt (E : Execution n k) (P : Protocol n k) (u : Fin n → Bool) (p : Fin n) (j : ℕ) :
    List (Action n k) :=
  match (E.ev j).localFor p with
  | some e => (P.step p (E.stateAt P u p j) e).2
  | none => []

/-- `useSigT i t` at position `j` is `p`'s first use of index `i` in the execution. -/
def FreshUse (E : Execution n k) (P : Protocol n k) (u : Fin n → Bool) (p : Fin n) (j : ℕ)
    (i : Fin k) (t : Term n k) : Prop :=
  (E.actionsAt P u p j).find? (Action.isUse i) = some (.useSigT i t) ∧
    ∀ j₀ < j, ∀ a ∈ E.actionsAt P u p j₀, a.isUse i = false

/-- The adversary's knowledge before position `j`: every term a correct party sent before `j`. -/
def advKnowledge (E : Execution n k) (P : Protocol n k) (F : Finset (Fin n)) (u : Fin n → Bool)
    (j : ℕ) : Set (Term n k) :=
  {t | ∃ j₀ < j, ∃ p ∉ F, ∃ q, Action.send q t ∈ E.actionsAt P u p j₀}

end Execution

/-- `E` is an execution of `P` with corrupt set `F`, inputs `u`, stabilization time `GST` and
delay bound `Δ` (see the module note). -/
structure IsExecution {n k : ℕ} (P : Protocol n k) (F : Finset (Fin n)) (u : Fin n → Bool)
    (GST Δ : ℝ) (E : Execution n k) : Prop where
  time_nonneg : 0 ≤ E.time 0
  time_mono : Monotone E.time
  time_unbounded : ∀ T : ℝ, ∃ j, T ≤ E.time j
  start_unique : ∀ p ∉ F, ∃ j, E.ev j = .start p ∧ E.time j ≤ GST ∧
    ∀ j', E.ev j' = .start p → j' = j
  local_after_start : ∀ p ∉ F, ∀ j (e : LocalEvent n k), (E.ev j).localFor p = some e →
    ∃ j₀ ≤ j, E.ev j₀ = .start p
  delivered : ∀ p ∉ F, ∀ j (q : Fin n) (t : Term n k), Action.send q t ∈ E.actionsAt P u p j →
    ∃ j' > j, E.ev j' = .deliver p q t ∧ E.time j' ≤ max (E.time j) GST + Δ
  sent : ∀ p ∉ F, ∀ j' (q : Fin n) (t : Term n k), E.ev j' = .deliver p q t →
    ∃ j < j', Action.send q t ∈ E.actionsAt P u p j
  corrupt_derivable : ∀ p ∈ F, ∀ j (q : Fin n) (t : Term n k), E.ev j = .deliver p q t →
    Derivable F F (E.advKnowledge P F u j) t
  token_unique : ∀ q ∈ F, ∀ (i : Fin k) (t t' : Term n k) (j j' : ℕ) (p r p' r' : Fin n)
    (s s' : Term n k), E.ev j = .deliver p r s → Term.Subterm (.tok q i t) s →
    E.ev j' = .deliver p' r' s' → Term.Subterm (.tok q i t') s' → t = t'
  timer_fires : ∀ p ∉ F, ∀ j (id : ℕ) (d : ℝ), Action.setTimer id d ∈ E.actionsAt P u p j →
    ∃ j' > j, E.ev j' = .timer p id ∧ E.time j ≤ E.time j' ∧
      E.time j' ≤ max (E.time j) GST + d ∧ (GST ≤ E.time j → E.time j' = E.time j + d)
  timer_set : ∀ p ∉ F, ∀ j' (id : ℕ), E.ev j' = .timer p id → ∃ j < j', ∃ d : ℝ,
    Action.setTimer id d ∈ E.actionsAt P u p j ∧
      E.time j' ≤ max (E.time j) GST + d ∧ (GST ≤ E.time j → E.time j' = E.time j + d)
  timer_after_delivery : ∀ p ∉ F, ∀ (m : ℕ) (id : ℕ), E.ev m = .timer p id → ∀ src ∉ F,
    ∀ (j' : ℕ) (t : Term n k), m < j' → E.ev j' = .deliver src p t → E.time j' = E.time m →
      ∃ j, m ≤ j ∧ j < j' ∧ Action.send p t ∈ E.actionsAt P u src j
  sigt_reply : ∀ p ∉ F, ∀ j (i : Fin k) (t : Term n k), E.FreshUse P u p j i t →
    ∃ j' > j, E.ev j' = .sigtReply p i (.tok p i t) ∧ E.time j' = E.time j
  sigt_source : ∀ p ∉ F, ∀ j' (i : Fin k) (s : Term n k), E.ev j' = .sigtReply p i s →
    ∃ j < j', ∃ t, s = .tok p i t ∧ E.FreshUse P u p j i t

end ByzSigT


