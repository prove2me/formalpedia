-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_BrownianFiniteEvaluationExactCleanV1
-- name    : MarkovProcess_V3HRepair_BrownianFiniteEvaluationExactCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:14:45.12312+00:00
-- url     : https://prove2.me/theorems/b981ac60-b5c6-49b5-b7c2-5836f59d6851
-- title:
--   Verified MarkovProcess source repair: BrownianFiniteEvaluationExactCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess BrownianFiniteEvaluationExactCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.BrownianFiniteEvaluationExactCleanV1 source SHA-256 b8ac4881bb3abd84a96b02035d924a4048867380dd12376cd2d4c6b79d448a4c. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets 3e63c2cd-a2e5-4b25-8c77-827e45eb445b; these add no mathematical assumptions.

import Definitions.Def_MarkovProcess_V3HRepair_BrownianFiniteEvaluationCleanV2
open MarkovProcess
theorem MarkovProcess.brownianMotion_map_finsetEvaluation (I : Finset NNReal) :
    brownianMotion.map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel heatSemigroup I :=
  _root_.solution I

#print axioms MarkovProcess.brownianMotion_map_finsetEvaluation

noncomputable def MarkovProcess.V3HRepairProof_3e63c2cda2e54b258c77827e45eb445b :=
  @MarkovProcess.brownianMotion_map_finsetEvaluation


