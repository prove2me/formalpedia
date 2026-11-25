-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LowerIndex
-- name    : GroundTheory_LocalFields_LowerIndex
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:53:20.050539+00:00
-- url     : https://prove2.me/theorems/0fcbbee6-7ac0-4de4-9d46-b54dc284b662
-- title:
--   Lower Index
-- statement:
--   Definitions and structural lemmas for Lower Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_Unramified
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
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
def lowerIndex (σ : L ≃ₐ[K] L) : ℕ∞ :=
  ⨅ x : 𝒪[L], addVal 𝒪[L] (integerAlgEquiv K L σ x - x)
variable {K L}
section Subgroup
variable (M : IntermediateField K L)
end Subgroup
end GroundTheory.LocalField


