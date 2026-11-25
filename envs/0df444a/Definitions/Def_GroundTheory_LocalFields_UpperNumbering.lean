-- Prove2me | Definitions.Def_GroundTheory_LocalFields_UpperNumbering
-- name    : GroundTheory_LocalFields_UpperNumbering
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T08:45:54.341075+00:00
-- url     : https://prove2.me/theorems/f4821a80-ae2e-51e5-8718-ffd9df9fa737
-- title:
--   Upper Numbering
-- statement:
--   Definitions and structural lemmas for Upper Numbering, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
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
open ValuativeRel
section Fiber
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) [Normal K M]
end Fiber
section QuotientMap
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
end QuotientMap
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsGalois K L] (M : IntermediateField K L) [IsGalois K M]
section Quotient
variable (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
end Quotient
end GroundTheory.LocalField


