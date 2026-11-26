-- Prove2me | Definitions.Def_BKAR_CubePartition_Support_Contribution
-- name    : BKAR_CubePartition_Support_Contribution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:53:07.249346+00:00
-- url     : https://prove2.me/theorems/96dc9a57-cbfb-486a-bf50-9b58cf63f46d
-- title:
--   Contribution
-- statement:
--   Definitions and structural lemmas for Contribution, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean

import Definitions.Def_BKAR_CubePartition_Support_Growth
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace ActiveTerminalBranchData
variable {F : Forest V}
noncomputable def supportContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) : ℝ := by
  classical
  exact
    Finset.sum
      ((Forest.empty V).activeEdges.attach.filter
        (fun e => (data.growth e).support = I))
      (fun e => (data.growth e).terminal.orderedContribution
        (data.growthOrder e) ρ)
noncomputable def supportOrderContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) : ℝ := by
  classical
  exact
    Finset.sum
      ((Forest.empty V).activeEdges.attach.filter
        (fun e => (data.growth e).support = I ∧
          data.growthOrder e = order))
      (fun e => (data.growth e).terminal.orderedContribution order ρ)
end ActiveTerminalBranchData
end Forest
end BKAR


