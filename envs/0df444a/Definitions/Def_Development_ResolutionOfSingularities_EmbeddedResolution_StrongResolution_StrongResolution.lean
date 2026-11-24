-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:29.716278+00:00
-- url     : https://prove2.me/theorems/babea27c-73a0-40d1-8101-bfe75643c333
-- title:
--   Strong Resolution
-- statement:
--   Definitions and structural lemmas for Strong Resolution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrongResolution.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def IsStrongResolution (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
    (s : SequenceOfBlowups X) : Prop :=
  AlgebraicGeometry.Smooth (s.lastStructMap ≫ f) ∧
  AlgebraicGeometry.IsProper s.lastStructMap ∧
  CategoryTheory.IsIso
    (AlgebraicGeometry.morphismRestrict s.lastStructMap f.smoothLocus) ∧
  Dense (s.lastStructMap.base ⁻¹' (f.smoothLocus : Set X)) ∧
  s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X) ∧
  IsStrictNormalCrossingsDivisor (reducedInverseImage s.lastStructMap (smoothLocusComplement f))
end FunctorialResolution.EmbeddedResolution
end


