-- Prove2me | Definitions.Def_CrashLocal_ConsNbhd_Model
-- name    : CrashLocal_ConsNbhd_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:58:12.781902+00:00
-- url     : https://prove2.me/theorems/d5915c85-baef-4571-abee-583a9bfd481a
-- title:
--   Deterministic synchronous LOCAL node programs under standard crash failures
-- statement:
--   The model of §3.2–3.3. A NodeProgram L Out has a state type and a message type, an initial state computed from the node's identifier, its input label and the set of its neighbors' identifiers (its star; the known parameters n, Δ, R, f are fixed when the program is chosen), a message for each neighbor addressed by the neighbor's identifier, a state update from the messages received in the round indexed by the sender's identifier, and an optional output. It never sees the graph, the vertex type or the crash pattern. An Adversary chooses for each node a crash time (none = never; some 0 = before the initial computation; some t = during round t) and, for a crash in round t, the set of neighbors that receive the crashing node's round-t message (standard crash faults: an arbitrary subset, chosen per recipient). alive t v: v has not crashed by the end of round t; survivors: nodes that never crash; crashCount: the number of crashed nodes. msgFrom/inbox: in round r a node v that completes the round receives from each neighbor u that had not crashed before round r its message for v, unless u crashes in round r and the adversary withholds it. config t v is v's state at the end of round t (none once v has crashed; a node crashing in round t sends in round t but does not receive or update), and outputAt t v its output at the end of round t.
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, §3.2–3.3, pp. 14–16

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Graphs

noncomputable section
open Classical

namespace CrashLocal.ConsNbhd

/-- A deterministic node program of the synchronous LOCAL model (§3.2–3.3). It never sees the
graph: its initial state is computed from the node's own identifier, its input label and the
identifiers of its neighbors (its star); in every round it computes one message for each neighbor,
addressed by that neighbor's identifier; it updates its state from the messages received in the
round, indexed by the sender's identifier (`none` = nothing received from that identifier); and
it reads an output (`none` = no output yet) from its state. Known parameters (`n`, `Δ`, `R`, `f`)
are fixed when the program is chosen. -/
structure NodeProgram (L Out : Type) where
  State : Type
  Msg : Type
  init : ℕ → L → Set ℕ → State
  send : State → ℕ → Msg
  update : State → (ℕ → Option Msg) → State
  output : State → Option Out

/-- A standard crash-fault adversary (§3.2). `crashTime v = none`: `v` never crashes;
`some 0`: `v` crashes before the initial local computation; `some t` with `t ≥ 1`: `v` crashes in
round `t`, and then its round-`t` message to `w` is delivered iff `delivered v w`. -/
structure Adversary (V : Type) where
  crashTime : V → Option ℕ
  delivered : V → V → Prop

namespace Adversary

variable {V : Type}

/-- `v` has not crashed by the end of round `t` (round `0` = the initial computation). -/
def alive (adv : Adversary V) (t : ℕ) (v : V) : Prop :=
  ∀ s, adv.crashTime v = some s → t < s

/-- Surviving nodes `S = V \ F`. -/
def survivors (adv : Adversary V) : Set V :=
  {v | adv.crashTime v = none}

/-- Number of crashed nodes `|F|`. -/
def crashCount (adv : Adversary V) : ℕ :=
  {v | adv.crashTime v ≠ none}.ncard

end Adversary

section Execution

variable {V L Out : Type}

/-- The message node `v` receives from `u` in round `r ≥ 1`, given the configuration `c` at the
end of round `r − 1`: `u`'s prescribed message for `v` if `u` is a neighbor of `v`, has not crashed
before round `r`, and, if it crashes in round `r`, the adversary delivers this message. -/
def msgFrom (G : SimpleGraph V) (id : V → ℕ) (P : NodeProgram L Out) (adv : Adversary V)
    (c : V → Option P.State) (r : ℕ) (u v : V) : Option P.Msg :=
  if G.Adj u v ∧ (adv.crashTime u = some r → adv.delivered u v) then
    (c u).map (fun su => P.send su (id v))
  else none

/-- What `v` receives in round `r`, indexed by sender identifier. -/
def inbox (G : SimpleGraph V) (id : V → ℕ) (P : NodeProgram L Out) (adv : Adversary V)
    (c : V → Option P.State) (r : ℕ) (v : V) : ℕ → Option P.Msg :=
  fun a => if h : ∃ u, id u = a then msgFrom G id P adv c r h.choose v else none

/-- The execution: `config … t v` is `v`'s state at the end of round `t` (`none` once `v` has
crashed). A node crashing in round `t` sends (partially) in round `t` but does not complete it. -/
def config (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (P : NodeProgram L Out)
    (adv : Adversary V) : ℕ → V → Option P.State
  | 0 => fun v =>
      if adv.crashTime v = some 0 then none
      else some (P.init (id v) (lab v) (id '' G.neighborSet v))
  | t + 1 => fun v =>
      if adv.crashTime v = some (t + 1) then none
      else (config G id lab P adv t v).map
        (fun s => P.update s (inbox G id P adv (config G id lab P adv t) (t + 1) v))

/-- `v`'s output at the end of round `t` (`none`: crashed, or no output yet). -/
def outputAt (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (P : NodeProgram L Out)
    (adv : Adversary V) (t : ℕ) (v : V) : Option Out :=
  (config G id lab P adv t v).bind P.output

end Execution

end CrashLocal.ConsNbhd


