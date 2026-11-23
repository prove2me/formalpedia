-- Prove2me | Definitions.Def_Comp_LeakyGateQ
-- name    : Comp_LeakyGateQ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T00:14:05.621086+00:00
-- url     : https://prove2.me/theorems/08813337-a1f8-4850-8c09-677410b678b7
-- title:
--   Leaky Gate Q
-- statement:
--   Definitions and structural lemmas for Leaky Gate Q, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean

import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
set_option linter.hashCommand false
namespace Comp
namespace LeakyGate
abbrev gate : ModelData where
  nAct1 := 2
  nAct2 := 2
  states :=
    [ -- state 0: action 0 holds the pair, action 1 risks the sink
      ⟨0, [⟨0, 0, [(0, 1/2), (1, 1/2)], 0⟩, ⟨0, 1, [(1, 1)], 0⟩,
           ⟨1, 0, [(3, 1)], 1⟩,             ⟨1, 1, [(0, 1)], 0⟩]⟩,
      -- state 1: same shape, mirrored
      ⟨0, [⟨0, 0, [(0, 1/2), (1, 1/2)], 0⟩, ⟨0, 1, [(0, 1)], 0⟩,
           ⟨1, 0, [(3, 1)], 1⟩,             ⟨1, 1, [(1, 1)], 0⟩]⟩,
      -- state 2: the leak -- every row action can be answered into the sink
      ⟨0, [⟨0, 0, [(2, 1/2), (3, 1/2)], 0⟩, ⟨0, 1, [(2, 1)], 0⟩,
           ⟨1, 0, [(3, 1)], 1⟩,             ⟨1, 1, [(2, 1)], 0⟩]⟩,
      -- state 3: the sink, and the only state with a reward
      ⟨1, [⟨0, 0, [(3, 1)], 0⟩, ⟨0, 1, [(3, 1)], 0⟩,
           ⟨1, 0, [(3, 1)], 0⟩, ⟨1, 1, [(3, 1)], 0⟩]⟩ ]
instance : NeZero gate.nStates := ⟨by decide⟩
instance : NeZero gate.nAct1 := ⟨by decide⟩
instance : NeZero gate.nAct2 := ⟨by decide⟩
theorem gate_shape : gate.Shape := by decide
theorem gate_stochastic : gate.Stochastic := by
  intro s
  fin_cases s <;>
    norm_num [ModelData.transOf, ModelData.stateAt, or_imp, and_imp, forall_and,
      forall_eq']
theorem gate_wf : gate.toCsgQ.WellFormed :=
  gate.wellFormed gate_shape gate_stochastic
def gateSafe : Finset (Fin gate.nStates) := {0, 1, 2}
def gateGood : Finset (Fin gate.nStates) := {0, 1}
def gateTarget : Finset (Fin gate.nStates) := {0}
end LeakyGate
end Comp


