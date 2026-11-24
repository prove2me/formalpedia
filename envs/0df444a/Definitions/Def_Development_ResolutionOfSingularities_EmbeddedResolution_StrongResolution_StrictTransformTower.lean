-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrictTransformTower
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrictTransformTower
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:08:25.892862+00:00
-- url     : https://prove2.me/theorems/7edcdbe6-e53c-4b0f-9f55-bf60ad29b45e
-- title:
--   Strict Transform Tower
-- statement:
--   Definitions and structural lemmas for Strict Transform Tower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrictTransformTower.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_tower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_discardedUnion_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_discardedUnion_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformIdeal_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformIdeal_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_totalSpaceZeroIso_spec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedCoprod_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedCoprod_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_inducedBlowups_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_inducedBlowups_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_inducedBlowups_tower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformIdeal_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformIdeal_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_totalSpaceZeroIso_spec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedResolutionRule_toAffineResolutionRule_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_nontrivialIndex_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_schemeAt
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_tower
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.discardedUnion_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.discardedUnion_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.strictTransformIdeal_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.strictTransformIdeal_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.detachedCoprod_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.detachedCoprod_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_tower
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformIdeal_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformIdeal_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedResolutionRule.toAffineResolutionRule_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.nontrivialIndex_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_schemeAt
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
instance instIsClosedImmersionEmbCompIsoZeroInv (S : EmbeddedBlowupSequence k Y pY) :
    AlgebraicGeometry.IsClosedImmersion (S.emb ≫ S.ambientSeq.isoZero.inv) :=
  inferInstance
def detachedToCoprod (T : EmbeddedBlowupSequence k Y pY) (s : ℕ) :
    ∀ (i : ℕ), s < i → (T.detachedScheme s ⟶ T.detachedCoprod i)
  | 0, h => absurd h (Nat.not_lt_zero s)
  | (i + 1), h =>
      if hs : s = i then
        eqToHom (congrArg T.detachedScheme hs) ≫
          (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod i ⨿ T.detachedScheme i)
      else
        detachedToCoprod T s i (by omega) ≫
          (coprod.inl : T.detachedCoprod i ⟶ T.detachedCoprod i ⨿ T.detachedScheme i)
variable (S : EmbeddedBlowupSequence k Y pY)
def strictTransformMapOfLE {a b : ℕ} (h : a ≤ b) : S.strictTransform b ⟶ S.strictTransform a :=
  Nat.leRec (motive := fun n _ => S.strictTransform n ⟶ S.strictTransform a)
    (𝟙 (S.strictTransform a)) (fun n _ f => S.strictTransformMap n ≫ f) h
@[simp] theorem strictTransformMapOfLE_self (a : ℕ) :
    S.strictTransformMapOfLE (le_refl a) = 𝟙 (S.strictTransform a) := by
  exact Nat.leRec_self ..
theorem exists_iso_coprod_of_isInitial {A B : Scheme.{u}} (hB : IsInitial B) :
    ∃ u : A ≅ A ⨿ B, u.hom = (coprod.inl : A ⟶ A ⨿ B) := by
  refine ⟨⟨(coprod.inl : A ⟶ A ⨿ B), coprod.desc (𝟙 A) (hB.to A),
    coprod.inl_desc (𝟙 A) (hB.to A), ?_⟩, rfl⟩
  refine coprod.hom_ext ?_ (hB.hom_ext _ _)
  calc (coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc (𝟙 A) (hB.to A) ≫ (coprod.inl : A ⟶ A ⨿ B)
      = ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc (𝟙 A) (hB.to A)) ≫
          (coprod.inl : A ⟶ A ⨿ B) := (Category.assoc _ _ _).symm
    _ = 𝟙 A ≫ (coprod.inl : A ⟶ A ⨿ B) :=
        congrArg (fun t => t ≫ (coprod.inl : A ⟶ A ⨿ B)) (coprod.inl_desc (𝟙 A) (hB.to A))
    _ = (coprod.inl : A ⟶ A ⨿ B) := Category.id_comp _
    _ = (coprod.inl : A ⟶ A ⨿ B) ≫ 𝟙 (A ⨿ B) := (Category.comp_id _).symm
theorem exists_iso_of_coprodIso_of_isInitial {A B Z : Scheme.{u}} (hB : IsInitial B)
    (w : A ⨿ B ≅ Z) :
    ∃ e : A ≅ Z, e.hom = (coprod.inl : A ⟶ A ⨿ B) ≫ w.hom := by
  obtain ⟨u, hu⟩ := exists_iso_coprod_of_isInitial (A := A) (B := B) hB
  refine ⟨u ≪≫ w, ?_⟩
  show u.hom ≫ w.hom = (coprod.inl : A ⟶ A ⨿ B) ≫ w.hom
  exact congrArg (fun t => t ≫ w.hom) hu
theorem comp_inv_comp_hom_cancel {A B C D E : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (h : C ⟶ E) (i : D ≅ E) :
    (f ≫ g ≫ (h ≫ i.inv)) ≫ i.hom = (f ≫ g) ≫ h := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
theorem exists_strictTransformZeroIso :
    ∃ e : S.strictTransform 0 ≅ Y, e.hom ≫ S.emb = S.strictTransformι 0 ≫ S.ambientSeq.isoZero.hom := by
  obtain ⟨e, he⟩ := exists_iso_of_coprodIso_of_isInitial (A := S.strictTransform 0)
    (B := S.detachedCoprod 0) (Z := Y) initialIsInitial S.totalSpaceZeroIso
  refine ⟨e, ?_⟩
  calc e.hom ≫ S.emb
      = ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom) ≫ S.emb :=
        congrArg (fun t => t ≫ S.emb) he
    _ = ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom ≫
          (S.emb ≫ S.ambientSeq.isoZero.inv)) ≫ S.ambientSeq.isoZero.hom :=
        (comp_inv_comp_hom_cancel (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0)
          S.totalSpaceZeroIso.hom S.emb S.ambientSeq.isoZero).symm
    _ = S.strictTransformι 0 ≫ S.ambientSeq.isoZero.hom :=
        congrArg (fun t => t ≫ S.ambientSeq.isoZero.hom) S.totalSpaceZeroIso_spec
def strictTransformZeroIso : S.strictTransform 0 ≅ Y := S.exists_strictTransformZeroIso.choose
def strictTransformToBase (i : ℕ) : S.strictTransform i ⟶ Y :=
  S.strictTransformMapOfLE (Nat.zero_le i) ≫ S.strictTransformZeroIso.hom
def detachedCoprodInl (i : ℕ) : S.detachedCoprod i ⟶ S.detachedCoprod (i + 1) :=
  (coprod.inl : S.detachedCoprod i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i)
def detachedCoprodInr (i : ℕ) : S.detachedScheme i ⟶ S.detachedCoprod (i + 1) :=
  (coprod.inr : S.detachedScheme i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i)
def totalMapOfLE {a b : ℕ} (h : a ≤ b) : S.totalSpace b ⟶ S.totalSpace a :=
  Nat.leRec (motive := fun n _ => S.totalSpace n ⟶ S.totalSpace a)
    (𝟙 (S.totalSpace a)) (fun n _ f => S.totalTransition n ≫ f) h
def detachedCoprodMapOfLE {a b : ℕ} (h : a ≤ b) : S.detachedCoprod a ⟶ S.detachedCoprod b :=
  Nat.leRec (motive := fun n _ => S.detachedCoprod a ⟶ S.detachedCoprod n)
    (𝟙 (S.detachedCoprod a)) (fun n _ f => f ≫ S.detachedCoprodInl n) h
end EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
end FunctorialResolution.EmbeddedResolution
end


