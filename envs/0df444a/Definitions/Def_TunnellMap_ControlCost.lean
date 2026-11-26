-- Prove2me | Definitions.Def_TunnellMap_ControlCost
-- name    : TunnellMap_ControlCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:00:05.67619+00:00
-- url     : https://prove2.me/theorems/55576fcc-0067-4288-834f-185328d9a9c6
-- title:
--   Control Cost
-- statement:
--   Definitions and structural lemmas for Control Cost, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ControlCost.lean

import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
structure ControlCost where
  generatorAdvances : ℕ
  keyComparisons : ℕ
  queueOperations : ℕ
  assignmentWrites : ℕ
namespace ControlCost
def zero : ControlCost := ⟨0, 0, 0, 0⟩
def add (a b : ControlCost) : ControlCost :=
  ⟨a.generatorAdvances + b.generatorAdvances,
    a.keyComparisons + b.keyComparisons,
    a.queueOperations + b.queueOperations,
    a.assignmentWrites + b.assignmentWrites⟩
end ControlCost
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace DAState
variable (I : GloballyRanked K S T)
noncomputable def oneStepCost (st : I.DAState) : ControlCost :=
  match st.queue with
  | [] => ControlCost.zero
  | s :: _rest =>
      if h : st.cursor s < Fintype.card T then
        let t := st.nextTarget I s h
        match st.held t with
        | none => ⟨1, 0, 1, 2⟩
        | some old =>
            if I.rank s t < I.rank old t then
              ⟨1, 1, 2, 3⟩
            else
              ⟨1, 1, 2, 0⟩
      else
        ControlCost.zero
noncomputable def runCost (st : I.DAState) : ControlCost :=
  match hstep : st.step I with
  | none => ControlCost.zero
  | some st' => ControlCost.add (st.oneStepCost I) (runCost st')
termination_by st.remaining I
decreasing_by exact remaining_step_lt I st st' hstep
end DAState
end GloballyRanked
end TunnellMap


