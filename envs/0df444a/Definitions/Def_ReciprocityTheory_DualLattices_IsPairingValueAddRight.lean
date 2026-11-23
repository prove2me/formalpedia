-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
-- name    : ReciprocityTheory_DualLattices_IsPairingValueAddRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:13.457846+00:00
-- url     : https://prove2.me/theorems/3025470f-d14c-4efc-8eaf-176e8b42361e
-- title:
--   Is Pairing Value Add Right
-- statement:
--   Definitions and structural lemmas for Is Pairing Value Add Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace BX
variable (B : BX R₀) {R : LAlg R₀}
end BX
end ReciprocityTheory.PGsh


