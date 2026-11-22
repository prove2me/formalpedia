-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_FoldL2ComplexOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_FoldL2ComplexOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:22.577305+00:00
-- url     : https://prove2.me/theorems/f9332e5b-514c-4dbf-a870-dea099371ec2
-- title:
--   Fold L2 Complex Of
-- statement:
--   Definitions and structural lemmas for Fold L2 Complex Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ComplexDoubleCosets/FoldL2ComplexOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_CplxDC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldDCUnfold
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldUnfold
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_TranslationIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
namespace PI.PoincareSeriesInner.W
universe u
end PI.PoincareSeriesInner.W


