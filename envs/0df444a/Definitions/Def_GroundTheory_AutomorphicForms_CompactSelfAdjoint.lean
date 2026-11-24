-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint
-- name    : GroundTheory_AutomorphicForms_CompactSelfAdjoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:20.656582+00:00
-- url     : https://prove2.me/theorems/6be2bf90-37f1-4e4c-b036-c934b24eaab6
-- title:
--   Compact Self Adjoint
-- statement:
--   Definitions and structural lemmas for Compact Self Adjoint, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Automorphic.CompactSelfAdjoint
open Module End Submodule Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
section HilbertBasis
variable [CompleteSpace E]
end HilbertBasis
section Spectrum
variable {T : E →L[𝕜] E}
variable [CompleteSpace E]
end Spectrum
section Eigenbasis
variable [CompleteSpace E]
end Eigenbasis
end GroundTheory.Automorphic.CompactSelfAdjoint


