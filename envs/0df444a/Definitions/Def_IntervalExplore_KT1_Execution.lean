-- Prove2me | Definitions.Def_IntervalExplore_KT1_Execution
-- name    : IntervalExplore_KT1_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:51.688918+00:00
-- url     : https://prove2.me/theorems/3e4b8424-03f7-4c16-b1f4-81e2c7dc8f75
-- title:
--   Execution, first termination, exploration deadline and common-tree extension
-- statement:
--   Fix a finite dynamic graph with identifiers, fixed ports and a starting vertex, and a deterministic observation-only algorithm $A$. At time $t$ the active agent observes snapshot $G_t$, appends that observation to its history, and either terminates or traverses the selected available port. After a valid traversal the incoming port is the destination endpoint's fixed port for the edge just traversed.
--
--   The execution has three modes: active, halted, and stuck. An invalid port produces a permanently stuck execution; halted executions are also frozen. The exploration deadline is the predicate
--   $$
--   \exists t\le B:\quad A\text{ first terminates at }t\quad\text{and}\quad
--   \forall v\in V\ \exists s\le t:\ \nu(s)=v.
--   $$
--   The observation and traversal at time $t$ both use snapshot $G_t$. There is no waiting action. After halt or an invalid move, no further observations are processed. This preserves the distinction between visiting everything and recognizing completion.
--
--   For a tree $H\subseteq G$ and a positive window $T$, the extension keeps $G_t$ unchanged for $t<T$ and replaces it by $G_t\cup H$ for $t\ge T$. This is the schedule modification in Remark 1; its consequences are theorem statements, not defining assumptions.
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), §1.2, p.3 (PDF p.4); §2.1 and Remark 1, p.6 (PDF p.7)

import Definitions.Def_IntervalExplore_KT1_Model

set_option autoImplicit false

namespace IntervalExplore.KT1

inductive Mode where
  | active | halted | stuck
  deriving DecidableEq, Inhabited

structure RunState (V : Type) where
  position : V
  incoming : Option ℕ
  past : List Obs
  mode : Mode

/-- A decision at time t uses snapshot t. An invalid port enters an absorbing
stuck state, distinct from successful termination. Halted states also absorb. -/
noncomputable def step {V : Type} [Fintype V] (W : World V) (A : Alg)
    (t : ℕ) (s : RunState V) : RunState V := by
  classical
  exact if s.mode = .active then
    let h := s.past ++ [observe W t s.position s.incoming]
    match A h with
    | none => {s with past := h, mode := .halted}
    | some p =>
      if hw : ∃ w, (W.dynamic.snapshot t).Adj s.position w ∧ W.ports.number s.position w = p then
        let w := Classical.choose hw
        ⟨w, some (W.ports.number w s.position), h, .active⟩
      else {s with past := h, mode := .stuck}
  else s

noncomputable def state {V : Type} [Fintype V] (W : World V) (A : Alg) : ℕ → RunState V
  | 0 => ⟨W.start, none, [], .active⟩
  | t + 1 => step W A t (state W A t)

/-- Process the current observation before deciding. After halt or error the history
is frozen, so there are no fictitious observations or charge events. -/
noncomputable def history {V : Type} [Fintype V] (W : World V) (A : Alg) (t : ℕ) : List Obs :=
  let s := state W A t
  if s.mode = .active then s.past ++ [observe W t s.position s.incoming] else s.past

/-- An outer none means there is no decision (already halted/stuck).
An inner none is the first termination decision. -/
noncomputable def decision {V : Type} [Fintype V] (W : World V) (A : Alg) (t : ℕ) :
    Option (Option ℕ) :=
  if (state W A t).mode = .active then some (A (history W A t)) else none

def TerminatedAt {V : Type} [Fintype V] (W : World V) (A : Alg) (t : ℕ) : Prop :=
  decision W A t = some none

/-- Both visiting every vertex and a first termination decision by the deadline.
There is no stay action, and an invalid choice cannot satisfy this predicate. -/
def ExploresWithin {V : Type} [Fintype V] (W : World V) (A : Alg) (B : ℕ) : Prop :=
  ∃ t ≤ B, TerminatedAt W A t ∧ ∀ v : V, ∃ s ≤ t, (state W A s).position = v

def MovesAt {V : Type} [Fintype V] (W : World V) (A : Alg) (t : ℕ) : Prop :=
  (state W A t).mode = .active ∧ (state W A (t + 1)).mode = .active

/-- Remark 1: add the selected spanning tree only from time T onward. -/
def extendSchedule {V : Type} {G : SimpleGraph V} (D : DynamicGraph G)
    (H : SimpleGraph V) (hH : H ≤ G) (T : ℕ) : DynamicGraph G where
  snapshot t := if t < T then D.snapshot t else D.snapshot t ⊔ H
  subgraph t := by
    split_ifs
    · exact D.subgraph t
    · exact sup_le (D.subgraph t) hH

def extendWorld {V : Type} [Fintype V] (W : World V) (H : SimpleGraph V)
    (hH : H ≤ W.graph) (T : ℕ) : World V :=
  {W with dynamic := extendSchedule W.dynamic H hH T}

end IntervalExplore.KT1


