-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_BrownianUniquenessExactCleanV1
-- name    : MarkovProcess_V3HRepair_BrownianUniquenessExactCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:19:54.792329+00:00
-- url     : https://prove2.me/theorems/88571388-56be-424c-9d74-1bea14a8639b
-- title:
--   Verified MarkovProcess source repair: BrownianUniquenessExactCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess BrownianUniquenessExactCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.BrownianUniquenessExactCleanV1 source SHA-256 048779c4e1b4826a78eb76ce088ce8694c6a033339057a379a442c898c216195. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Definitions.Def_MarkovProcess_V3HRepair_BrownianUniquenessCleanV1
open MeasureTheory ProbabilityTheory MarkovProcess
theorem MarkovProcess.eq_brownianMotion_of_map_finsetEvaluation (Q : Kernel ℝ (ContinuousPath ℝ))
    [IsFiniteKernel Q]
    (hQ : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel heatSemigroup I) :
    Q = brownianMotion :=
  _root_.solution Q hQ

#print axioms MarkovProcess.eq_brownianMotion_of_map_finsetEvaluation


