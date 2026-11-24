-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
-- name    : GroundTheory_AutomorphicForms_SmoothRepSchur
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:35.263063+00:00
-- url     : https://prove2.me/theorems/697ee5d9-dd08-4f97-876b-e76b9427c025
-- title:
--   Smooth Rep Schur
-- statement:
--   Definitions and structural lemmas for Smooth Rep Schur, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
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
open Polynomial Cardinal
section Schur
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
end Schur
section Smooth
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
end Smooth
end GroundTheory.Automorphic


