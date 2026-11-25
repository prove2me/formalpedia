-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CompactRep
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_CompactRep
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:16.879508+00:00
-- url     : https://prove2.me/theorems/e4e90b17-9900-4ef6-bf2d-ed972d4115d3
-- title:
--   Compact Rep
-- statement:
--   Definitions and structural lemmas for Compact Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/CompactRep.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace CompactRep
open MeasureTheory Module Set
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  {σ : Representation ℂ K W}
end CompactRep
end GroundTheory.Automorphic


