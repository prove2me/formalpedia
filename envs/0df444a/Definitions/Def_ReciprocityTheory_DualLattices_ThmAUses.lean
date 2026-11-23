-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ThmAUses
-- name    : ReciprocityTheory_DualLattices_ThmAUses
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:20:37.568932+00:00
-- url     : https://prove2.me/theorems/5b285859-d6ad-4a6c-8834-2ddc4606ff50
-- title:
--   Thm AUses
-- statement:
--   Definitions and structural lemmas for Thm AUses, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAUses.lean

import Definitions.Def_ReciprocityTheory_DualLattices_StThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
namespace ReciprocityTheory.PGsh
section Mat
variable {D : Type} [CommRing D] {g : ℕ}
end Mat
section Span
variable {R₀ : Type} [CommRing R₀]
end Span
section Val
variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
end Val
end ReciprocityTheory.PGsh


