-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuasiCompactIffLocallyOfFinitePresentation
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuasiCompactIffLocallyOfFinitePresentation
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:26:17.864635+00:00
-- url     : https://prove2.me/theorems/0bf0b81d-ac51-4a4a-b26a-9ac13c8e4698
-- title:
--   Quasi Compact Iff Locally Of Finite Presentation
-- statement:
--   Definitions and structural lemmas for Quasi Compact Iff Locally Of Finite Presentation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuasiCompactIffLocallyOfFinitePresentation.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Theorems.Thm_GlobalTheory_GroupRingConst_powChar_apply
import Theorems.Thm_GlobalTheory_GroupRingConst_pt_single
import Theorems.Thm_GlobalTheory_LaurentConst_hom_ext
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GroupRingConst.powChar_apply
attribute [local simp] GlobalTheory.GroupRingConst.pt_single
attribute [local simp] GlobalTheory.restrictPoints_val


set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G
namespace GlobalTheory.SemiAbelianCompare
section General
theorem isPullback_torsor {S : Scheme.{u}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom q] (h : IsPullback i (toUnit _) q η[B]) :
    IsPullback ((fst T G ≫ i) * snd T G) (snd T G) q q := by
  have hi : i ≫ q = 1 := h.w
  have : Mono i := h.flip.mono_snd_of_mono
  refine IsPullback.of_isLimit'
    ⟨by rw [MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul]⟩
    (PullbackCone.IsLimit.mk _ (fun s => lift (h.lift (s.fst * s.snd⁻¹) (toUnit _) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, mul_inv_cancel]; rfl)) s.snd)
      (fun s => ?_) (fun s => lift_snd _ _) (fun s m h₁ h₂ => ?_))
  · rw [MonObj.comp_mul, lift_fst_assoc, h.lift_fst, lift_snd, inv_mul_cancel_right]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, ← cancel_mono i, h.lift_fst, ← h₁, ← h₂, MonObj.comp_mul,
        mul_inv_cancel_right, Category.assoc]
    · rw [lift_snd, h₂]
theorem quasiCompact_of_isPullback {X Y X' Y' : Scheme.{u}}
    {a : X' ⟶ X} {p : X' ⟶ Y'} {q : X ⟶ Y} {s : Y' ⟶ Y} (h : IsPullback a p q s)
    [Surjective s] (hs : IsOpenMap s) [QuasiCompact p] : QuasiCompact q := by
  refine ⟨fun U hUo hUc => ?_⟩
  have key : ∃ C : Set X, IsCompact C ∧ C ⊆ q ⁻¹' U ∧ q ⁻¹' U ⊆ C := by
    refine hUc.induction_on (p := fun t => ∃ C : Set X, IsCompact C ∧ C ⊆ q ⁻¹' U ∧ q ⁻¹' t ⊆ C)
      ⟨∅, isCompact_empty, Set.empty_subset _, by simp⟩
      (fun t t' htt' ⟨C, h₁, h₂, h₃⟩ => ⟨C, h₁, h₂, (Set.preimage_mono htt').trans h₃⟩)
      (fun t t' ⟨C, h₁, h₂, h₃⟩ ⟨C', h₁', h₂', h₃'⟩ =>
        ⟨C ∪ C', h₁.union h₁', Set.union_subset h₂ h₂', by
          rw [Set.preimage_union]; exact Set.union_subset_union h₃ h₃'⟩) (fun y hy => ?_)
    obtain ⟨y', rfl⟩ := s.surjective y
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y'.isBasis_affineOpens.exists_subset_of_mem_open
      (a := y') (u := s ⁻¹' U) hy (hUo.preimage s.continuous)
    refine ⟨s '' V, mem_nhdsWithin_of_mem_nhds ((hs _ V.isOpen).mem_nhds ⟨y', hyV, rfl⟩),
      a '' (p ⁻¹' V), (QuasiCompact.isCompact_preimage _ V.isOpen hV.isCompact).image a.continuous,
      ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      have := hVU hz
      rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply] at this
    · rintro x ⟨v, hv, hx⟩
      obtain ⟨z, rfl, rfl⟩ := Scheme.exists_preimage_of_isPullback h x v hx.symm
      exact ⟨z, hv, rfl⟩
  obtain ⟨C, h₁, h₂, h₃⟩ := key
  rwa [← h₂.antisymm h₃]
end General
section Exact
variable {S : Scheme.{u}} {X : Type u} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {i : Semi.splitTorus S X ⟶ G} {q : G ⟶ B}
theorem quasiCompact_iff_locallyOfFinitePresentation [Module.Finite ℤ X] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q η[B]) [hf : Flat q.left] [hs : Surjective q.left] :
    QuasiCompact q.left ↔ LocallyOfFinitePresentation q.left := by
  have sq := (isPullback_torsor i q hk).map (Over.forget _)
  constructor
  · intro hq
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFinitePresentation)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq.flip ⟨⟨hs, hf⟩, hq⟩ ?_
    exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (IsPullback.of_hasPullback _ _) (Diag.locallyOfFinitePresentation_hom S X)
  · intro hq
    have h₁ : QuasiCompact ((Over.forget _).map (snd (Semi.splitTorus S X) G)) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback _ _)
        (have := Diag.isAffineHom_hom S X; inferInstance)
    exact @quasiCompact_of_isPullback _ _ _ _ _ _ _ _ sq hs q.left.isOpenMap h₁
end Exact
theorem isAbelianScheme_iff {S : Scheme.{u}} (A : Over S) [GrpObj A] :
    Semi.IsAbelianScheme A ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsAbelianScheme A :=
  ⟨fun h => ⟨h.smooth, h.proper, h.geomConnected, h.comm⟩,
    fun h => ⟨h.comm, h.smooth, h.proper, h.geometricallyConnected⟩⟩
section Field
variable {k : Type u} [Field k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G]
def torusExtensionOfIsShortExact {X : Type u} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {B : Over (Spec (CommRingCat.of k))} [GrpObj B]
    {i : Semi.splitTorus (Spec (CommRingCat.of k)) X ⟶ G} {q : G ⟶ B}
    (hB : IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsAbelianScheme B) (h : IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsShortExact i q) :
    Semi.TorusExtension G where
  X := X
  B := B
  isAbelian := (isAbelianScheme_iff _).2 hB
  q := q
  q_hom := h.isMonHom_q
  q_flat := h.flat
  q_surjective := h.surjective
  q_quasiCompact :=
    have := h.isMonHom_q
    have := h.flat
    have := h.surjective
    (quasiCompact_iff_locallyOfFinitePresentation h.isKernel).2 h.finitePresentation
  i := i
  i_hom := h.isMonHom_i
  isKernel := h.isKernel
end Field
end GlobalTheory.SemiAbelianCompare
namespace GlobalTheory
open SemiAbelianCompare
end GlobalTheory


