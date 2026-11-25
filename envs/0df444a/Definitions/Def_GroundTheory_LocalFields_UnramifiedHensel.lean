-- Prove2me | Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
-- name    : GroundTheory_LocalFields_UnramifiedHensel
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:51:45.180394+00:00
-- url     : https://prove2.me/theorems/c7993241-a2cd-4977-b57d-9354d69326aa
-- title:
--   Unramified Hensel
-- statement:
--   Definitions and structural lemmas for Unramified Hensel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedHensel.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Theorems.Thm_GroundTheory_LocalField_isAdicComplete_integer

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
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
section Base
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
instance henselianLocalRing_integer : HenselianLocalRing 𝒪[K] where
  toIsLocalRing := inferInstance
  is_henselian f hf a₀ h₁ h₂ := by
    have := isAdicComplete_integer K
    exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)
end Base
section Residue
variable (K M : Type*) [Field K] [ValuativeRel K] [Field M] [ValuativeRel M]
  [Algebra K M] [ValuativeExtension K M]
end Residue
section Extension
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
end Extension
end GroundTheory.LocalField


