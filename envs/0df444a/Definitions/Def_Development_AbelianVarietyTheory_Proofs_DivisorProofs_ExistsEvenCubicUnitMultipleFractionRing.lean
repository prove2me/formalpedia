-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEvenCubicUnitMultipleFractionRing
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEvenCubicUnitMultipleFractionRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:09.302732+00:00
-- url     : https://prove2.me/theorems/38d8952d-7bee-4534-a935-1f0b5ca06df4
-- title:
--   Exists Even Cubic Unit Multiple Fraction Ring
-- statement:
--   Definitions and structural lemmas for Exists Even Cubic Unit Multiple Fraction Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEvenCubicUnitMultipleFractionRing.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
namespace EvenCubicNorm
open Finset
section Quadratic
variable {M : Type*} [CommGroup M] {ι : Type*} [Fintype ι]
def prodPow (z : ι → ι → M) (e : ι → ι → ℤ) : M := ∏ i, ∏ j, z i j ^ e i j
end Quadratic
end EvenCubicNorm
end GlobalTheory


