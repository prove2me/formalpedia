-- Prove2me | Definitions.Def_FD1D_V5_Complexity
-- name    : FD1D_V5_Complexity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:17:47.976638+00:00
-- url     : https://prove2.me/theorems/a900a398-779f-4f90-8d6f-91b7788f08ae
-- title:
--   Complexity
-- statement:
--   Definitions and structural lemmas for Complexity, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Complexity.lean

import Definitions.Def_FD1D_V5_Parameters
set_option autoImplicit true
namespace FD1D.V5
noncomputable section
open Filter Asymptotics
def hierarchicalOperationCount (m : ℕ) : ℕ :=
  20 * (treeDepth m + 1)
def hierarchicalMemoryCount (m : ℕ) : ℕ :=
  m + 4 * leafCount m
structure HierarchicalResourceGuarantees : Prop where
  operationsExplicit :
    ∀ {m : ℕ}, 2 ≤ m →
      (hierarchicalOperationCount m : ℝ) ≤
        (100 / Real.log 2) * Real.log (m : ℝ)
  memoryExplicit :
    ∀ {m : ℕ}, 1 ≤ m → hierarchicalMemoryCount m ≤ 5 * m
  operationsAsymptotic :
    (fun m : ℕ => (hierarchicalOperationCount m : ℝ)) =O[atTop]
      (fun m : ℕ => Real.log (m : ℝ))
  memoryAsymptotic :
    (fun m : ℕ => (hierarchicalMemoryCount m : ℝ)) =O[atTop]
      (fun m : ℕ => (m : ℝ))
end
end FD1D.V5


