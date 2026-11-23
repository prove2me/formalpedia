-- Prove2me | Definitions.Def_GroundTheory_LocalFields_UnitsGalois
-- name    : GroundTheory_LocalFields_UnitsGalois
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:43.934122+00:00
-- url     : https://prove2.me/theorems/8a03ce05-4816-477d-9f12-ce3411efdffc
-- title:
--   Units Galois
-- statement:
--   Definitions and structural lemmas for Units Galois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsGalois.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
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
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
instance integerUnitsAction : MulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ where
  smul σ u := Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u
  one_smul u := by ext; rfl
  mul_smul σ τ u := by ext; rfl
  smul_mul σ u w := map_mul (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L])) u w
  smul_one σ := map_one (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]))
end GroundTheory.LocalField


