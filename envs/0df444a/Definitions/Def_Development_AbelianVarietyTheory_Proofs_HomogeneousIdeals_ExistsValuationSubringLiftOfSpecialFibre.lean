-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:57.673935+00:00
-- url     : https://prove2.me/theorems/f537a0b6-4370-46e2-9073-454afba30302
-- title:
--   Exists Valuation Subring Lift Of Special Fibre
-- statement:
--   Definitions and structural lemmas for Exists Valuation Subring Lift Of Special Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory
universe u
section Algebra
end Algebra
section Scheme
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {O K : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]
end Scheme
end GlobalTheory


