-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CompactUnitaryFiniteInvariantSubspace
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CompactUnitaryFiniteInvariantSubspace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:49.85666+00:00
-- url     : https://prove2.me/theorems/c33615e6-03c2-4623-b0f8-c74184c75262
-- title:
--   Compact Unitary Finite Invariant Subspace
-- statement:
--   Definitions and structural lemmas for Compact Unitary Finite Invariant Subspace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CompactUnitaryFiniteInvariantSubspace.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
namespace GlobalTheory.CompactRep
section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] {X : Type} [MeasurableSpace X] {μ : Measure X}
end
end GlobalTheory.CompactRep


