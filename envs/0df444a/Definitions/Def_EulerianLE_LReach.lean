-- Prove2me | Definitions.Def_EulerianLE_LReach
-- name    : EulerianLE_LReach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:50.628199+00:00
-- url     : https://prove2.me/theorems/0135b4d4-5df4-43e7-b3ef-a22905bbb41d
-- title:
--   Local runs of one program and the local conditions of Theorem 8
-- statement:
--   A **local run** of one node program executes the program alone under an arbitrary pattern of pulse deliveries to its ports, in any order and at any times, including before the program starts. Its configuration records the program's status, the number of pulses queued at each port, the counters $\sigma_i,\rho_i$, and the number of pulses observed so far at each port. As in executions, a delivery occurs only when the program cannot execute an instruction.
--
--   A port $i$ has **terminated** at a configuration if, for every pattern of deliveries afterwards, the program performs no further operation on $i$ (Definition 2, read as in App. C.1). The **local conditions** of Theorem 8, at every configuration reached by some local run, are:
--
--   1. when the program completes, $\sum_i\sigma_i=\sum_i\rho_i$;
--   2. port $i$ has terminated if and only if $\sigma_i+\rho_i=d$;
--   3. the program, with no further delivery, consumes every pulse it has observed.
--
--   These conditions concern one program at a time and are what Theorem 8 turns into composability.
--
--   **Formalization Note** Condition 3 is read with Lemma 19's "for any arbitrary pattern of pulse deliveries afterwards, even if there are none": from every reachable configuration the program's own operations reach a configuration in which every observed pulse is consumed.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §3.2, p.10 (PDF p.12), Definition 2 and Theorem 8, conditions (1)–(3); App. C.1, p.34 (port termination, Lemma 19 (3))

import Mathlib
import Definitions.Def_EulerianLE_Run

namespace EulerianLE

variable {deg : ℕ} {Out : Type}

/-- A configuration of one node program `P` run on its own, under an arbitrary pattern of pulse
deliveries to its ports (Frei, Gelles, Ghazy, Nolin, STOC 2027 submission (manuscript sha256
90954a93…), Theorem 8, p.10; Lemma 19, p.34): its status, the number of pulses queued at each port,
the counters σ (`sent`) and ρ (`consumed`), and `obs i`, the number of pulses at port `i` observed so
far, counted in delivery order (the observed pulses at `i` are the first `obs i` pulses ever
delivered there). Pulses have no content, so only queue lengths matter. -/
structure LConfig (P : NodeProg deg Out) where
  status : Status P.State Out
  queue : Fin deg → ℕ
  sent : Fin deg → ℕ
  consumed : Fin deg → ℕ
  obs : Fin deg → ℕ

variable {P : NodeProg deg Out}

/-- The start: asleep, nothing delivered. Deliveries may occur before the program starts ("including
before u starts the chunk", Lemma 19, p.34). -/
def LConfig.init (P : NodeProg deg Out) : LConfig P :=
  ⟨.asleep, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- The program is awake and its next instruction can be executed. -/
def LConfig.enabled (c : LConfig P) : Bool :=
  match c.status with
  | .running s =>
    match P.step s with
    | .test gs fl _ => (fireFrom c.queue gs 0).isSome || fl.isSome
    | _ => true
  | _ => false

/-- The configuration after the program's next operation, if it can be executed: as in
`Config.step`, with `obs` raised to cover the pulses the operation observes. -/
def LConfig.opStep (c : LConfig P) : Option (LConfig P) :=
  match c.status with
  | .running s =>
    match P.step s with
    | .send i n =>
      some { c with status := .running n, sent := Function.update c.sent i (c.sent i + 1) }
    | .tau n => some { c with status := .running n }
    | .complete o => some { c with status := .completed o }
    | .test gs fl sc =>
      match fireFrom c.queue gs 0 with
      | some (n, g, p) =>
        let c₁ := { c with
          status := .running (sc n p)
          obs := Function.update c.obs p (max (c.obs p) (c.consumed p + max g.need 1)) }
        if g.take then
          some { c₁ with
            queue := Function.update c.queue p (c.queue p - 1)
            consumed := Function.update c.consumed p (c.consumed p + 1) }
        else some c₁
      | none =>
        match fl with
        | some s' => some { c with status := .running s' }
        | none => none
  | _ => none

/-- The next operation of the program at `c` is an operation on port `i` (a send through `i`, a
consumption at `i`, or an inspection of `i`'s queue). -/
def LConfig.Touches (c : LConfig P) (i : Fin deg) : Prop :=
  match c.status with
  | .running s => (P.step s).Touches i
  | _ => False

/-- One step of a local run: wake-up, an operation of the program, or the delivery of a pulse at a
port. As in `Config.step`, a wake-up or a delivery requires that the program cannot execute an
instruction. -/
inductive LStep (P : NodeProg deg Out) : LConfig P → LConfig P → Prop
  | wake (c : LConfig P) (h : c.status = .asleep) : LStep P c { c with status := .running P.init }
  | deliver (c : LConfig P) (i : Fin deg) (h : c.enabled = false) :
      LStep P c { c with queue := Function.update c.queue i (c.queue i + 1) }
  | op (c c' : LConfig P) (h : c.opStep = some c') : LStep P c c'

/-- `c` is reached by some local run of `P`, that is, under some pattern of pulse deliveries. -/
def LReach (P : NodeProg deg Out) (c : LConfig P) : Prop :=
  Relation.ReflTransGen (LStep P) (LConfig.init P) c

/-- Definition 2 (Port termination), p.10, read as in App. C.1 (p.34: "a port has terminated if, for
any arbitrary pattern of pulse deliveries afterwards, the program performs no further operation on
it"): from `c`, under every continuation, no executed operation is an operation on port `i`. -/
def PortTerminated (P : NodeProg deg Out) (c : LConfig P) (i : Fin deg) : Prop :=
  ∀ c', Relation.ReflTransGen (LStep P) c c' → ∀ c'', c'.opStep = some c'' → ¬ c'.Touches i

/-- Condition (1) of Theorem 8 (p.10), for every pattern of deliveries: "When the program completes,
it holds ∑_i σ_i[u] = ∑_i ρ_i[u]". -/
def LocalCond1 (P : NodeProg deg Out) : Prop :=
  ∀ c, LReach P c → c.status.isDone = true → ∑ i, c.sent i = ∑ i, c.consumed i

/-- Condition (2) of Theorem 8 (p.10), for every pattern of deliveries: "For every port i ∈ [deg(u)],
port i has terminated if and only if σ_i[u] + ρ_i[u] = d". -/
def LocalCond2 (P : NodeProg deg Out) (d : ℕ) : Prop :=
  ∀ c, LReach P c → ∀ i, PortTerminated P c i ↔ c.sent i + c.consumed i = d

/-- Condition (3) of Theorem 8 (p.10), for every pattern of deliveries: "The program eventually
consumes every pulse that it observes", read with Lemma 19's "for any arbitrary pattern of pulse
deliveries afterwards, even if there are none" (p.34): from every reachable configuration, the
program's own operations alone, with no further delivery, reach a configuration in which it has
consumed every pulse observed so far at each port. -/
def LocalCond3 (P : NodeProg deg Out) : Prop :=
  ∀ c, LReach P c → ∀ i, ∃ c', Relation.ReflTransGen (fun a b : LConfig P => a.opStep = some b) c c' ∧
    c.obs i ≤ c'.consumed i

end EulerianLE


