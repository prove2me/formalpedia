-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_NsmulKerZero
-- name    : ReciprocityTheory_DualLattices_NsmulKerZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:14.124815+00:00
-- url     : https://prove2.me/theorems/82d6b634-807d-41a8-9bad-341f85065ae4
-- title:
--   Nsmul Ker Zero
-- statement:
--   Definitions and structural lemmas for Nsmul Ker Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulKerZero.lean

import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique
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
namespace ATower
variable {p : ℕ} (Tw : ATower R₀ p)
end ATower
namespace BX
variable (B : BX R₀) {p : ℕ}
end BX
end ReciprocityTheory.PGsh


