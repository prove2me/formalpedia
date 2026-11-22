-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_FoldDCUnfoldOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_FoldDCUnfoldOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:22.343961+00:00
-- url     : https://prove2.me/theorems/c6a7e817-fb5e-458c-a08c-9d26af318ed0
-- title:
--   Fold DCUnfold Of
-- statement:
--   Definitions and structural lemmas for Fold DCUnfold Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FoldingUnfolding/FoldDCUnfoldOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldDCUnfold
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldUnfold
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_TransExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
namespace PI.FoldDCUnfold.W
universe u
end PI.FoldDCUnfold.W


