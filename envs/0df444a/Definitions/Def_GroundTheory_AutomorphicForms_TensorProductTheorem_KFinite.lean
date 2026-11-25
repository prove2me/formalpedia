-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:11.321366+00:00
-- url     : https://prove2.me/theorems/8caf6d33-1072-4bd2-bfdf-4a0395c97fde
-- title:
--   KFinite
-- statement:
--   Definitions and structural lemmas for KFinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CompactRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
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
open Module Set
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X]
structure IsKFinite (σ : Representation ℂ K X) : Prop where
  locallyFinite : ∀ v, FiniteDimensional ℂ (Submodule.span ℂ (range fun k => σ k v))
  continuous : Representation.HasContinuousCoeff σ
variable {σ : Representation ℂ K X}
variable (σ) in

abbrev Alg := MonoidAlgebra ℂ K
section Isotypic
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
theorem isCompl_isotypicComponent {c : Submodule R M} (hc : c ∈ isotypicComponents R M) :
    IsCompl c (sSup (isotypicComponents R M \ {c})) := by
  refine ⟨sSupIndep_isotypicComponents R M hc, codisjoint_iff.2 ?_⟩
  rw [eq_top_iff, ← sSup_isotypicComponents (R := R) (M := M)]
  refine sSup_le fun m hm => ?_
  by_cases hmc : m = c
  · exact hmc ▸ le_sup_left
  · exact le_sup_of_le_right (le_sSup ⟨hm, hmc⟩)
def isoProj {c : Submodule R M} (hc : c ∈ isotypicComponents R M) : Module.End R M :=
  c.subtype ∘ₗ Submodule.projectionOnto c _ (isCompl_isotypicComponent hc)
end Isotypic
end CompactRep
end GroundTheory.Automorphic


