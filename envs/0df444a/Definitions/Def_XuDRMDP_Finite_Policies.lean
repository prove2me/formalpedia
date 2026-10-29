-- Prove2me | Definitions.Def_XuDRMDP_Finite_Policies
-- name    : XuDRMDP_Finite_Policies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:28:05.506058+00:00
-- url     : https://prove2.me/theorems/6b49a71f-63cb-429e-b559-094ea5959cf6
-- title:
--   Staged histories and randomized behavioral policies
-- statement:
--   A history consists of a chronological list of past state/action pairs and the current state. The initial history has an empty past and the designated initial state. Extending a history appends its current state and a chosen admissible action, and installs the next state. Structurally admissible histories are generated from the initial history by extensions to the immediately following stage. This definition does not test whether a transition or chosen action has positive probability.
--
--   A mixed action at state $s$ is a nonnegative real vector indexed by $A_s$ with sum one. A policy assigns a mixed action to every history and cannot observe the unknown parameter vector or its law. Values on structurally inadmissible histories are unused; every source policy extends to this total function domain, and restrictions give exactly the source's policies. Terminal action choices are unrestricted and have no effect on returns. This is the full history-dependent randomized policy domain, including different choices at different histories ending at the same state.
-- source:
--   Xu and Mannor (2012), Distributionally Robust Markov Decision Processes, Mathematics of Operations Research 37(2), 288–300, DOI:10.1287/moor.1120.0540. Published basis; printed page = PDF page + 287. Sections 2–3, printed pp. 289–293 (PDF pp. 2–6).

import Definitions.Def_XuDRMDP_Finite_Setup
open scoped BigOperators

namespace XuDRMDP.Finite

/-- State/action history; the current state has no action yet. -/
structure History {n : ℕ} (a : Fin n → ℕ) where
  past : List (Sigma fun s => Fin (a s))
  state : Fin n

def initialHistory {n : ℕ} {a : Fin n → ℕ} (G : Setup n a) : History a :=
  ⟨[], G.initial⟩

def History.extend {n : ℕ} {a : Fin n → ℕ} (h : History a)
    (b : Fin (a h.state)) (j : Fin n) : History a :=
  ⟨h.past ++ [⟨h.state, b⟩], j⟩

/-- All structurally admissible histories, without a positive-probability restriction. -/
inductive Admissible {n : ℕ} {a : Fin n → ℕ} (G : Setup n a) : History a → Prop
  | initial : Admissible G (initialHistory G)
  | extend {h : History a} (hh : Admissible G h) (b : Fin (a h.state)) (j : Fin n)
      (next : G.stage j = G.stage h.state + 1) : Admissible G (h.extend b j)

abbrev MixedAction {n : ℕ} (a : Fin n → ℕ) (s : Fin n) :=
  {q : Fin (a s) → ℝ // q ∈ stdSimplex ℝ (Fin (a s))}

/-- Behavioral policies; values on structurally inadmissible histories are unused. -/
abbrev Policy {n : ℕ} (a : Fin n → ℕ) := (h : History a) → MixedAction a h.state

end XuDRMDP.Finite


