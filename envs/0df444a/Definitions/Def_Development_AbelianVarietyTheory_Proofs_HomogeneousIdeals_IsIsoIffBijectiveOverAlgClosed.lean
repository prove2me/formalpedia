-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:14.200487+00:00
-- url     : https://prove2.me/theorems/a02074bb-ac3e-482c-8f8d-b066a6a82276
-- title:
--   Is Iso Iff Bijective Over Alg Closed
-- statement:
--   Definitions and structural lemmas for Is Iso Iff Bijective Over Alg Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
namespace GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}
theorem isIso_iff_isIso_left (f : X ⟶ Y) : IsIso f ↔ IsIso f.left :=
  (isIso_iff_of_reflects_iso f (Over.forget S)).symm
theorem isPullback_pullback_map {T : Scheme.{u}} (t : T ⟶ S) (f : X ⟶ Y) :
    IsPullback ((Over.pullback t).map f).left (pullback.fst X.hom t) (pullback.fst Y.hom t)
      f.left := by
  refine IsPullback.of_right (h₁₂ := pullback.snd Y.hom t) (v₁₃ := t) (h₂₂ := Y.hom) ?_ (by simp)
    (IsPullback.of_hasPullback Y.hom t).flip
  simpa using (IsPullback.of_hasPullback X.hom t).flip
theorem isFinite_left (f : X ⟶ Y) [IsFinite X.hom] [IsSeparated Y.hom] : IsFinite f.left := by
  have : IsFinite (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  exact IsFinite.of_comp f.left Y.hom
theorem etale_left (f : X ⟶ Y) [Etale X.hom] [LocallyOfFiniteType Y.hom]
    [FormallyUnramified Y.hom] : Etale f.left := by
  have : Etale (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  exact Etale.of_comp f.left Y.hom
def isoLocus (f : X ⟶ Y) : Set S :=
  {s | IsIso ((Over.pullback (S.fromSpecResidueField s)).map f)}
theorem isIso_pullback_map_iff_finrank {T : Scheme.{u}} (t : T ⟶ S) (f : X ⟶ Y)
    [IsFinite f.left] [Flat f.left] :
    IsIso ((Over.pullback t).map f) ↔
      ∀ y : Y.left, Y.hom y ∈ Set.range t → f.left.finrank y = 1 := by
  have H := isPullback_pullback_map t f
  have h1 : IsFinite ((Over.pullback t).map f).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) H.flip inferInstance
  have h2 : Flat ((Over.pullback t).map f).left :=
    MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance
  rw [isIso_iff_isIso_left, Scheme.Hom.isIso_iff_finrank_eq]
  have h3 := Scheme.Hom.finrank_of_isPullback _ _ _ _ H.flip
  constructor
  · intro h y hy
    have : y ∈ Set.range (pullback.fst Y.hom t) := by rwa [Scheme.Pullback.range_fst]
    obtain ⟨z, rfl⟩ := this
    rw [← h3, h, Pi.one_apply]
  · intro h
    funext z
    rw [h3, Pi.one_apply]
    apply h
    rw [← Set.mem_preimage, ← Scheme.Pullback.range_fst]
    exact ⟨z, rfl⟩
theorem mem_isoLocus_iff (f : X ⟶ Y) [IsFinite f.left] [Flat f.left] (s : S) :
    s ∈ isoLocus f ↔ ∀ y : Y.left, Y.hom y = s → f.left.finrank y = 1 := by
  rw [isoLocus, Set.mem_setOf_eq, isIso_pullback_map_iff_finrank,
    Scheme.range_fromSpecResidueField]
  rfl
theorem compl_isoLocus (f : X ⟶ Y) [IsFinite f.left] [Flat f.left] :
    (isoLocus f)ᶜ = Y.hom '' {y | f.left.finrank y ≠ 1} := by
  ext s
  rw [Set.mem_compl_iff, mem_isoLocus_iff]
  simp only [not_forall, Set.mem_image, Set.mem_setOf_eq]
  tauto
theorem isClopen_isoLocus (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] : IsClopen (isoLocus f) := by
  have := isFinite_left f
  have := etale_left f
  have h : IsClopen {y | f.left.finrank y ≠ 1} :=
    (f.left.isLocallyConstant_finrank.isClopen_fiber 1).compl
  rw [← isClopen_compl_iff, compl_isoLocus]
  exact ⟨Y.hom.isClosedMap _ h.isClosed, Y.hom.isOpenMap _ h.isOpen⟩
def eqLocus (f g : X ⟶ Y) : Set S :=
  {s | (Over.pullback (S.fromSpecResidueField s)).map f =
    (Over.pullback (S.fromSpecResidueField s)).map g}
def agreeι (f g : X ⟶ Y) :
    pullback (pullback.lift f.left g.left ((Over.w f).trans (Over.w g).symm))
      (pullback.diagonal Y.hom) ⟶ X.left :=
  pullback.fst _ _
instance (f g : X ⟶ Y) [LocallyOfFiniteType Y.hom] [FormallyUnramified Y.hom] :
    IsOpenImmersion (agreeι f g) := by
  unfold agreeι; infer_instance
instance (f g : X ⟶ Y) [IsSeparated Y.hom] : IsClosedImmersion (agreeι f g) := by
  unfold agreeι; infer_instance
theorem agreeι_condition (f g : X ⟶ Y) : agreeι f g ≫ f.left = agreeι f g ≫ g.left := by
  have h := pullback.condition
    (f := pullback.lift f.left g.left ((Over.w f).trans (Over.w g).symm))
    (g := pullback.diagonal Y.hom)
  have h1 := h =≫ pullback.fst _ _
  have h2 := h =≫ pullback.snd _ _
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
    pullback.diagonal_snd, Category.comp_id] at h1 h2
  exact h1.trans h2.symm
theorem comp_eq_comp_iff_range (f g : X ⟶ Y) [LocallyOfFiniteType Y.hom]
    [FormallyUnramified Y.hom] {Z : Scheme.{u}} (a : Z ⟶ X.left) :
    a ≫ f.left = a ≫ g.left ↔ Set.range a ⊆ Set.range (agreeι f g) := by
  constructor
  · intro h
    have : pullback.lift a (a ≫ f.left) (by apply pullback.hom_ext <;> simp [h]) ≫ agreeι f g
        = a := pullback.lift_fst _ _ _
    rintro _ ⟨z, rfl⟩
    exact ⟨_, by rw [← Scheme.Hom.comp_apply, this]⟩
  · intro h
    rw [← IsOpenImmersion.lift_fac (agreeι f g) a h, Category.assoc, Category.assoc,
      agreeι_condition]
theorem pullback_map_eq_iff_preimage {T : Scheme.{u}} (t : T ⟶ S) (f g : X ⟶ Y)
    [LocallyOfFiniteType Y.hom] [FormallyUnramified Y.hom] :
    (Over.pullback t).map f = (Over.pullback t).map g ↔
      X.hom ⁻¹' Set.range t ⊆ Set.range (agreeι f g) := by
  rw [← Scheme.Pullback.range_fst, ← comp_eq_comp_iff_range]
  constructor
  · intro h
    rw [← (isPullback_pullback_map t f).w, ← (isPullback_pullback_map t g).w, h]
  · intro h
    ext1
    apply pullback.hom_ext
    · rw [(isPullback_pullback_map t f).w, (isPullback_pullback_map t g).w, h]
    · simp
theorem compl_eqLocus (f g : X ⟶ Y) [LocallyOfFiniteType Y.hom] [FormallyUnramified Y.hom] :
    (eqLocus f g)ᶜ = X.hom '' (Set.range (agreeι f g))ᶜ := by
  ext s
  rw [Set.mem_compl_iff, eqLocus, Set.mem_setOf_eq, pullback_map_eq_iff_preimage,
    Scheme.range_fromSpecResidueField, Set.not_subset]
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, Set.mem_compl_iff]
  tauto
theorem isClopen_eqLocus (f g : X ⟶ Y) [UniversallyOpen X.hom] [UniversallyClosed X.hom]
    [LocallyOfFiniteType Y.hom] [FormallyUnramified Y.hom] [IsSeparated Y.hom] :
    IsClopen (eqLocus f g) := by
  have h : IsClopen (Set.range (agreeι f g))ᶜ :=
    IsClopen.compl ⟨(agreeι f g).isClosedEmbedding.isClosed_range,
      (agreeι f g).isOpenEmbedding.isOpen_range⟩
  rw [← isClopen_compl_iff, compl_eqLocus]
  exact ⟨X.hom.isClosedMap _ h.isClosed, X.hom.isOpenMap _ h.isOpen⟩
def IsSplitOfRank {X S : Scheme.{u}} (p : X ⟶ S) (n : ℕ) : Prop :=
  ∃ s : Fin n → (S ⟶ X), (∀ i, s i ≫ p = 𝟙 S) ∧ Nonempty (IsColimit (Cofan.mk X s))
def complOpen {X S : Scheme.{u}} (σ : S ⟶ X) [IsClosedImmersion σ] : X.Opens :=
  ⟨(Set.range σ)ᶜ, σ.isClosedEmbedding.isClosed_range.isOpen_compl⟩
theorem range_complOpen_ι {X S : Scheme.{u}} (σ : S ⟶ X) [IsClosedImmersion σ] :
    Set.range (complOpen σ).ι = (Set.range σ)ᶜ := Scheme.Opens.range_ι _
instance {X S : Scheme.{u}} (σ : S ⟶ X) [IsClosedImmersion σ] [IsOpenImmersion σ] :
    IsClosedImmersion (complOpen σ).ι := .of_isPreimmersion _ (by
  rw [range_complOpen_ι, isClosed_compl_iff]; exact σ.isOpenEmbedding.isOpen_range)
def isoLocusOpen (f : X ⟶ Y) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    S.Opens := ⟨isoLocus f, (isClopen_isoLocus f).isOpen⟩
def eqLocusOpen (f g : X ⟶ Y) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    S.Opens := ⟨eqLocus f g, (isClopen_eqLocus f g).isOpen⟩
instance (f : X ⟶ Y) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsClosedImmersion (isoLocusOpen f).ι := .of_isPreimmersion _ (by
  rw [Scheme.Opens.range_ι]; exact (isClopen_isoLocus f).isClosed)
instance (f g : X ⟶ Y) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsClosedImmersion (eqLocusOpen f g).ι := .of_isPreimmersion _ (by
  rw [Scheme.Opens.range_ι]; exact (isClopen_eqLocus f g).isClosed)
end GlobalTheory.FinEt


