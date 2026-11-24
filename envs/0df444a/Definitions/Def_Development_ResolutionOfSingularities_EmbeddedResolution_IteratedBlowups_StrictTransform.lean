-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:59.412958+00:00
-- url     : https://prove2.me/theorems/be8dbb01-580d-4ac0-a96c-8a1da84de6c8
-- title:
--   Strict Transform
-- statement:
--   Definitions and structural lemmas for Strict Transform, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ReducedSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def strictTransformOpens {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    ((D.comap π).subscheme).Opens :=
  (D.comap π).subschemeι ⁻¹ᵁ (Z.comap π).support.compl
def strictTransformι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    (strictTransformOpens π Z D).toScheme ⟶ X₁ :=
  Scheme.Opens.ι (strictTransformOpens π Z D) ≫ (D.comap π).subschemeι
theorem isCompact_of_subset_noetherianSpace {α : Type u} [TopologicalSpace α] (s : Set α)
    [NoetherianSpace s] (t : Set α) (ht : t ⊆ s) : IsCompact t := by
  have h1 : IsCompact ((Subtype.val : s → α) ⁻¹' t) := NoetherianSpace.isCompact _
  have h2 := h1.image continuous_subtype_val
  have h3 : (Subtype.val : s → α) '' ((Subtype.val : s → α) ⁻¹' t) = t := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      exact ⟨⟨x, ht hx⟩, hx, rfl⟩
  rwa [h3] at h2
theorem isCompact_of_subset_isCompact {B : Scheme.{u}} [IsLocallyNoetherian B]
    {U : Set B} (hc : IsCompact U) {T : Set B} (hT : T ⊆ U) : IsCompact T := by
  have hcov : U ⊆ ⋃ W : B.affineOpens, (W.1 : Set B) := by
    intro x _
    have hx : x ∈ (⊤ : B.Opens) := Set.mem_univ x
    rw [← iSup_affineOpens_eq_top B] at hx
    obtain ⟨W, hW⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨W, hW⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun W : B.affineOpens => (W.1 : Set B)) (fun W => W.1.isOpen) hcov
  have hTeq : T = ⋃ W ∈ (s : Set B.affineOpens), (T ∩ (W.1 : Set B)) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨W, hWs, hxW⟩ := Set.mem_iUnion₂.mp (hs (hT hx))
      exact Set.mem_biUnion (show W ∈ (s : Set B.affineOpens) from hWs) ⟨hx, hxW⟩
    · intro x hx
      obtain ⟨W, -, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact hx'.1
  rw [hTeq]
  refine (Finset.finite_toSet s).isCompact_biUnion ?_
  intro W _
  have : IsNoetherianRing (B.presheaf.obj (Opposite.op (W.1 : B.Opens))) :=
    IsLocallyNoetherian.component_noetherian W
  have : NoetherianSpace (W.1 : Set B) := noetherianSpace_of_isAffineOpen W.1 W.2
  exact isCompact_of_subset_noetherianSpace (W.1 : Set B) (T ∩ (W.1 : Set B)) Set.inter_subset_right
theorem quasiCompact_of_isInducing {A B : Scheme.{u}} [IsLocallyNoetherian B]
    (f : A ⟶ B) (hf : Topology.IsInducing ⇑f.base) : QuasiCompact f := by
  refine ⟨fun U _ hU' => ?_⟩
  refine hf.isCompact_iff.mpr ?_
  exact isCompact_of_subset_isCompact hU' (Set.image_preimage_subset _ _)
theorem quasiCompact_strictTransformι_of_isLocallyNoetherian {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [IsLocallyNoetherian X₁] :
    QuasiCompact (strictTransformι π Z D) := by
  refine quasiCompact_of_isInducing _ ?_
  have h1 : Topology.IsInducing ⇑(Scheme.Opens.ι (strictTransformOpens π Z D)).base :=
    (Scheme.Opens.ι (strictTransformOpens π Z D)).isEmbedding.toIsInducing
  have h2 : Topology.IsInducing ⇑(D.comap π).subschemeι.base :=
    (D.comap π).subschemeι.isEmbedding.toIsInducing
  have heq : ⇑(strictTransformι π Z D).base
      = ⇑(D.comap π).subschemeι.base ∘
        ⇑(Scheme.Opens.ι (strictTransformOpens π Z D)).base := rfl
  rw [heq]
  exact h2.comp h1
instance instQuasiCompactStrictTransformMorphism {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [IsLocallyNoetherian X₁] :
    QuasiCompact (strictTransformι π Z D) :=
  quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D
end FunctorialResolution.EmbeddedResolution


