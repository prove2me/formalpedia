-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:51.256496+00:00
-- url     : https://prove2.me/theorems/12cf5dfc-ccf0-43d5-86d1-ec124a653dda
-- title:
--   Norm Sq Riemann Theta Mul Exp Periodic
-- statement:
--   Definitions and structural lemmas for Norm Sq Riemann Theta Mul Exp Periodic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/NormSqRiemannThetaMulExpPeriodic.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
namespace GlobalTheory.RiemannThetaModel
variable {ι : Type*} [Fintype ι]
end GlobalTheory.RiemannThetaModel


