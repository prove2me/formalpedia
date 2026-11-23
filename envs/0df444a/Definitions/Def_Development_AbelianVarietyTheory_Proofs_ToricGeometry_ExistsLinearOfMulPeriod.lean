-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:08.403327+00:00
-- url     : https://prove2.me/theorems/634a27b9-8026-494f-86ff-c738c9058cc5
-- title:
--   Exists Linear Of Mul Period
-- statement:
--   Definitions and structural lemmas for Exists Linear Of Mul Period, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearOfMulPeriod.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
namespace GlobalTheory.ArtinKernel
section Artin
variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]
end Artin
end GlobalTheory.ArtinKernel


