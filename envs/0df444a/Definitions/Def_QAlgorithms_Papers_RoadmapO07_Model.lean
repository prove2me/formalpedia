-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapO07_Model
-- name    : QAlgorithms_Papers_RoadmapO07_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:51.713838+00:00
-- url     : https://prove2.me/theorems/9a86c58a-e103-4064-8412-b21894cbaf6b
-- title:
--   Quantum algorithms for zero-sum games: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Quantum algorithms for zero-sum games, arXiv:1904.03180v1, https://arxiv.org/abs/1904.03180v1. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_ZeroSumDynamics
noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapO07

open QAlgorithms.ZeroSum

/-- Extract the setup, update body and finishing pass of the frozen dense implementation.
This syntax accessor is used only on `denseImplementation`, whose setup consists of
unconditional instructions before its single outer loop (arXiv:1904.03180v1, PDF p.6). -/
def denseLoopParts : ClassicalEntryProgram →
    ClassicalEntryProgram × (ClassicalEntryProgram × ClassicalEntryProgram)
  | .done => (.done, .done, .done)
  | .step op next =>
      let parts := denseLoopParts (next false)
      (.step op (fun _ => parts.1), parts.2)
  | .loop _ body rest => (.done, body, rest)


end QAlgorithms.Papers.RoadmapO07


