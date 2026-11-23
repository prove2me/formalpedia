-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
-- name    : ReciprocityTheory_DualLattices_NsmulFstAddSnd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:40.365098+00:00
-- url     : https://prove2.me/theorems/6d1dada2-242c-49aa-b55d-e5fa148c8e6d
-- title:
--   Nsmul Fst Add Snd
-- statement:
--   Definitions and structural lemmas for Nsmul Fst Add Snd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulFstAddSnd.lean

import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
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


