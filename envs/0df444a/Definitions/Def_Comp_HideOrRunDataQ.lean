-- Prove2me | Definitions.Def_Comp_HideOrRunDataQ
-- name    : Comp_HideOrRunDataQ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T00:14:09.099505+00:00
-- url     : https://prove2.me/theorems/3df0293d-8104-486b-bcec-eebf92563158
-- title:
--   Hide Or Run Data Q
-- statement:
--   Definitions and structural lemmas for Hide Or Run Data Q, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean

import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
set_option linter.hashCommand false
namespace Comp
namespace HideOrRunData
abbrev hrd : ModelData where
  nAct1 := 2
  nAct2 := 2
  states :=
    [ -- state 0, the stand-off: run into a throw dies, run into a wait arrives,
      -- waiting out a throw arrives, waiting against a wait stays
      ⟨0, [⟨0, 0, [(2, 1)], 0⟩, ⟨0, 1, [(1, 1)], 0⟩,
           ⟨1, 0, [(1, 1)], 0⟩, ⟨1, 1, [(0, 1)], 0⟩]⟩,
      -- state 1, the goal: absorbing
      ⟨0, [⟨0, 0, [(1, 1)], 0⟩, ⟨0, 1, [(1, 1)], 0⟩,
           ⟨1, 0, [(1, 1)], 0⟩, ⟨1, 1, [(1, 1)], 0⟩]⟩,
      -- state 2, death: absorbing
      ⟨0, [⟨0, 0, [(2, 1)], 0⟩, ⟨0, 1, [(2, 1)], 0⟩,
           ⟨1, 0, [(2, 1)], 0⟩, ⟨1, 1, [(2, 1)], 0⟩]⟩ ]
instance : NeZero hrd.nStates := ⟨by decide⟩
instance : NeZero hrd.nAct1 := ⟨by decide⟩
instance : NeZero hrd.nAct2 := ⟨by decide⟩
theorem hrd_shape : hrd.Shape := by decide
theorem hrd_stochastic : hrd.Stochastic := by
  intro s
  fin_cases s <;>
    norm_num [ModelData.transOf, ModelData.stateAt, or_imp, and_imp, forall_and,
      forall_eq']
theorem hrd_wf : hrd.toCsgQ.WellFormed :=
  hrd.wellFormed hrd_shape hrd_stochastic
def hrdTarget : Finset (Fin hrd.nStates) := {1}
def hrdWinning : Finset (Fin hrd.nStates) := {0, 1}
end HideOrRunData
end Comp


