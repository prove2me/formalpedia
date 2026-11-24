-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemThetaDomainIffIsSiegelAddTranspose
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemThetaDomainIffIsSiegelAddTranspose
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:55.743096+00:00
-- url     : https://prove2.me/theorems/99cddb36-eeb0-4f2f-912c-7dd7d028097e
-- title:
--   Mem Theta Domain Iff Is Siegel Add Transpose
-- statement:
--   Definitions and structural lemmas for Mem Theta Domain Iff Is Siegel Add Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemThetaDomainIffIsSiegelAddTranspose.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology ReciprocityTheory.PTheta
namespace GlobalTheory
variable {ι : Type*} [Fintype ι]
end GlobalTheory


