-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UpperTriangularInverseIsUpper
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UpperTriangularInverseIsUpper
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:54:11.399052+00:00
-- url     : https://prove2.me/theorems/0e37d49f-582c-4be4-a52c-431871219e50
-- title:
--   Upper Triangular Inverse Is Upper
-- statement:
--   Definitions and structural lemmas for Upper Triangular Inverse Is Upper, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UpperTriangularInverseIsUpper.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
namespace GlobalTheory.CompanionTheory.Iwahori.UpInv
variable {L V ι : Type} [Field L] [AddCommGroup V] [Module L V] [Fintype ι]
def low (wt : ι → ℕ) (P : ι → Module.End L V) (m : ℕ) : Submodule L V where
  carrier := {x | ∀ i, m ≤ wt i → P i x = 0}
  add_mem' {x y} hx hy i hi := by rw [map_add, hx i hi, hy i hi, add_zero]
  zero_mem' i _ := map_zero _
  smul_mem' c x hx i hi := by rw [map_smul, hx i hi, smul_zero]
end GlobalTheory.CompanionTheory.Iwahori.UpInv
end


