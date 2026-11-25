-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois
-- name    : GroundTheory_GlobalFields_Artin_PlacesGalois
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:57:17.335229+00:00
-- url     : https://prove2.me/theorems/f65a78cc-a70a-430f-bcc7-057f99d9fad5
-- title:
--   Places Galois
-- statement:
--   Definitions and structural lemmas for Places Galois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesGalois.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
namespace GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))
def fixedFieldMulEquiv : H ≃* Gal(L/fixedField H) where
  toFun := toFixedFieldAlgEquiv H
  invFun σ := ⟨σ.restrictScalars K, restrictScalars_mem H σ⟩
  left_inv _ := Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)
  right_inv _ := AlgEquiv.ext fun _ ↦ rfl
  map_mul' _ _ := AlgEquiv.ext fun _ ↦ rfl
end GroundTheory.Global.Artin


