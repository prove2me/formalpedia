-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_VanishingIdealOfComponents
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_VanishingIdealOfComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:30.875845+00:00
-- url     : https://prove2.me/theorems/0af1e8d3-fcfd-4ae6-a67f-6ba0bae5c388
-- title:
--   Vanishing Ideal Of Components
-- statement:
--   Definitions and structural lemmas for Vanishing Ideal Of Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/VanishingIdealOfComponents.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
variable {α : Type*} [TopologicalSpace α]
theorem isClosed_sUnion_irreducibleComponents [NoetherianSpace α]
    {S : Set (Set α)} (hS : S ⊆ irreducibleComponents α) :
    IsClosed (⋃₀ S) := by
  have hfin : S.Finite :=
    Set.Finite.subset (by apply NoetherianSpace.finite_irreducibleComponents) hS
  rw [Set.sUnion_eq_biUnion]
  refine hfin.isClosed_biUnion ?_
  intro s hs
  apply isClosed_of_mem_irreducibleComponents
  exact hS hs
theorem isOpen_compl_sUnion_irreducibleComponents_sdiff [NoetherianSpace α]
    (S : Set (Set α)) :
    IsOpen ((⋃₀ (irreducibleComponents α \ S))ᶜ) :=
  (isClosed_sUnion_irreducibleComponents Set.sdiff_subset).isOpen_compl
def complSUnionOtherComponents (X : Scheme.{u}) [NoetherianSpace ↥X] (S : Set (Set ↥X)) : X.Opens :=
  ⟨(⋃₀ (irreducibleComponents ↥X \ S))ᶜ,
    isOpen_compl_sUnion_irreducibleComponents_sdiff S⟩
end FunctorialResolution.EmbeddedResolution


