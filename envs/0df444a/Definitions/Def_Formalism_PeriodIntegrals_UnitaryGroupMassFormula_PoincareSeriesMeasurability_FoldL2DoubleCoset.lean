-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoincareSeriesMeasurability_FoldL2DoubleCoset
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoincareSeriesMeasurability_FoldL2DoubleCoset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:39.452608+00:00
-- url     : https://prove2.me/theorems/edab7021-61d5-4d72-ab11-0c11e572cbb3
-- title:
--   Fold L2 Double Coset
-- statement:
--   Definitions and structural lemmas for Fold L2 Double Coset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PoincareSeriesMeasurability/FoldL2DoubleCoset.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldUnfold
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace PI.PoincareSeriesMemLp.UnitaryGroupMassFormula
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
end PI.PoincareSeriesMemLp.UnitaryGroupMassFormula


