-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OfRealGramDeterminantBoundLeProdCutoffStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_OfRealGramDeterminantBoundLeProdCutoffStatement
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:51.21283+00:00
-- url     : https://prove2.me/theorems/6dc1fdf9-4d2b-4a0e-9931-4e0d245ffcc1
-- title:
--   Of Real Gram Determinant Bound Le Prod Cutoff Statement
-- statement:
--   Definitions and structural lemmas for Of Real Gram Determinant Bound Le Prod Cutoff Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OfRealGramDeterminantBoundLeProdCutoffStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OfRealGramDeterminantBoundLeProdCutoff
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix


