-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:55.662174+00:00
-- url     : https://prove2.me/theorems/19f89f95-3b57-4dd3-ab7b-bae0c7d3c8f9
-- title:
--   PGeneric Freeness Loc
-- statement:
--   Definitions and structural lemmas for PGeneric Freeness Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean

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
namespace GroundTheory.Heights₂.Heights
namespace GenericFreeness
open Module
universe u
variable {A : Type u} [CommRing A]
def IsGenericallyFree (A : Type u) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)
end GenericFreeness
end GroundTheory.Heights₂.Heights


