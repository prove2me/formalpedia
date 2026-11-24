-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:37.512867+00:00
-- url     : https://prove2.me/theorems/7acc0cfa-25a3-4913-86b5-4506a52246e8
-- title:
--   PGeneric Cycle Corresp
-- statement:
--   Definitions and structural lemmas for PGeneric Cycle Corresp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericCycleCorresp.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GenericCycleCorresp
section LocalizationLength
variable {S T : Type*} [CommRing S] [CommRing T] [Algebra S T] (M : Submonoid S)
  [IsLocalization M T]
end LocalizationLength
section DVR
variable {K : Type*} {ι : K → Type*} {O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O]
end DVR
end GenericCycleCorresp
end
end GroundTheory.Heights₂.Heights.NumbersDVR


