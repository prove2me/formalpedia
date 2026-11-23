-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZeroMemLatOf
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZeroMemLatOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:02.547808+00:00
-- url     : https://prove2.me/theorems/832c6240-ccae-45f8-bffd-b1e51d80a3cd
-- title:
--   Zero Mem Lat Of
-- statement:
--   Definitions and structural lemmas for Zero Mem Lat Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ZeroMemLatOf.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
namespace GlobalTheory.AdLat.Scale
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
end GlobalTheory.AdLat.Scale
namespace GlobalTheory.AdLat
open Scale
end GlobalTheory.AdLat


