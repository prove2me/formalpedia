-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:27.932486+00:00
-- url     : https://prove2.me/theorems/169c9ea4-99d9-4dd3-ae36-d93a36e5df54
-- title:
--   Monomial Splitting
-- statement:
--   Definitions and structural lemmas for Monomial Splitting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialSplitting.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}
def IsMonomialIn (E : List X.IdealSheafData) (M : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
    M.comap U.ι = ∏ i : Fin E.length, (E.get i).comap U.ι ^ a i
structure IsMonomialSplitting (E : List X.IdealSheafData) (I M N : X.IdealSheafData) :
    Prop where
  eq_mul : I = M * N
  monomial_support : (M.support : Set X) ⊆ ⋃ D ∈ E, (D.support : Set X)
  monomial : IsMonomialIn E M
  transversal : ∀ D ∈ E, ∀ C : Set X, IsIrreducible C → C ⊆ (D.support : Set X) →
    (∀ C' : Set X, IsIrreducible C' → C' ⊆ (D.support : Set X) → C ⊆ C' → C' ⊆ C) →
    ¬ C ⊆ (N.support : Set X)
end FunctorialResolution.EmbeddedResolution


