-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_CharR
-- name    : ReciprocityTheory_DualLattices_CharR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:33.824115+00:00
-- url     : https://prove2.me/theorems/7583c035-5afb-43f7-9da0-714be92262ff
-- title:
--   Char R
-- statement:
--   Definitions and structural lemmas for Char R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/CharR.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsLimTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
end ReciprocityTheory.PGsh


