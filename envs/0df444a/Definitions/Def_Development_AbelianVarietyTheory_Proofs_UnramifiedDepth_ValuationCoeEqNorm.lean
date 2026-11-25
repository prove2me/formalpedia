-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:34:46.999498+00:00
-- url     : https://prove2.me/theorems/b1194b65-01f3-41c8-be8b-e83051331aec
-- title:
--   Valuation Coe Eq Norm
-- statement:
--   Definitions and structural lemmas for Valuation Coe Eq Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Ideal
namespace GlobalTheory.PadicComplexHost
variable (p : ℕ) [hp : Fact p.Prime]
end GlobalTheory.PadicComplexHost


