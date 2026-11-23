-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique
-- name    : ReciprocityTheory_DualLattices_IsHeightUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:46.508237+00:00
-- url     : https://prove2.me/theorems/33b108f5-e1a7-4d72-8e6f-a721a22cf827
-- title:
--   Is Height Unique
-- statement:
--   Definitions and structural lemmas for Is Height Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean

import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
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
namespace BX
variable (B : BX R₀)
end BX
end ReciprocityTheory.PGsh


