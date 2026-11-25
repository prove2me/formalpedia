-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGaussPoint
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGaussPoint
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:54:34.480846+00:00
-- url     : https://prove2.me/theorems/c7b89f7e-4ee7-4641-aab5-ea51b9b583d4
-- title:
--   Exists Gauss Point
-- statement:
--   Definitions and structural lemmas for Exists Gauss Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGaussPoint.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj IsLocalRing
namespace GlobalTheory.GaussPoint
section Val
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]
end Val
end GlobalTheory.GaussPoint


