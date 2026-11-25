-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
-- name    : GroundTheory_LocalFields_LowerIndexQuotient
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:24:01.050842+00:00
-- url     : https://prove2.me/theorems/53483a30-d8d3-4069-a5fe-1e6f3e9ce6d4
-- title:
--   Lower Index Quotient
-- statement:
--   Definitions and structural lemmas for Lower Index Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndexQuotient.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RamificationLowerIndex
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_GeneralBFactAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
section Restrict
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L)
end Restrict
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
section
variable (M : IntermediateField K L)
variable [IsGalois K L]
end
end GroundTheory.LocalField


