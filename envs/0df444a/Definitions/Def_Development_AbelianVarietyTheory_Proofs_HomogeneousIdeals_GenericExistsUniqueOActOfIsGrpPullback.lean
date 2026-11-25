-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:05:44.108826+00:00
-- url     : https://prove2.me/theorems/da78a924-cf91-4474-a4ba-d08a21d1c3b8
-- title:
--   Generic Exists Unique OAct Of Is Grp Pullback
-- statement:
--   Definitions and structural lemmas for Generic Exists Unique OAct Of Is Grp Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
namespace GlobalTheory.StalkLimit
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
abbrev AffNhd {S : Scheme.{u}} (x : S) : Type u := {V : S.Opens // x ∈ V ∧ IsAffineOpen V}
instance {S : Scheme.{u}} (x : S) : IsCofiltered (AffNhd x) := by
  have : Nonempty (AffNhd x) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact ⟨U, hxU, hU⟩
  have : IsDirected (AffNhd x) (· ≥ ·) := ⟨fun V W => by
    obtain ⟨U, h₁, h₂, h₃ : U ≤ V.1 ⊓ W.1⟩ :=
      Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (show x ∈ V.1 ⊓ W.1 from ⟨V.2.1, W.2.1⟩)
    exact ⟨⟨U, h₂, h₁⟩, h₃.trans inf_le_left, h₃.trans inf_le_right⟩⟩
  infer_instance
variable {S X : Scheme.{u}} (x : S) (p : X ⟶ S)
def diagram : AffNhd x ⥤ Scheme.{u} where
  obj V := pullback p V.1.ι
  map {V W} i := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ S.homOfLE i.le) (by
    rw [Category.assoc, Scheme.homOfLE_ι, pullback.condition])
  map_id V := by
    rw [← cancel_mono (pullback.fst p V.1.ι), pullback.lift_fst, Category.id_comp]
  map_comp {U V W} i j := by
    rw [← cancel_mono (pullback.fst p W.1.ι), pullback.lift_fst, Category.assoc, pullback.lift_fst,
      pullback.lift_fst]
theorem diagram_map_fst {V W : AffNhd x} (i : V ⟶ W) :
    (diagram x p).map i ≫ pullback.fst p W.1.ι = pullback.fst p V.1.ι := by
  dsimp only [diagram]
  exact pullback.lift_fst _ _ _
instance {V W : AffNhd x} (i : V ⟶ W) : IsAffineHom ((diagram x p).map i) := by
  have h : IsPullback ((diagram x p).map i) (pullback.snd p V.1.ι) (pullback.snd p W.1.ι) (S.homOfLE i.le) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p W.1.ι)
    rw [diagram_map_fst, Scheme.homOfLE_ι]
    exact IsPullback.of_hasPullback _ _
  have : IsAffine V.1.toScheme := V.2.2
  have : IsAffine W.1.toScheme := W.2.2
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
variable {x p} {X' : Scheme.{u}} {φ : X' ⟶ X} {p' : X' ⟶ Spec (S.presheaf.stalk x)}
def cone (h : IsPullback φ p' p (S.fromSpecStalk x)) : Cone (diagram x p) where
  pt := X'
  π := { app V := pullback.lift φ (p' ≫ V.1.fromSpecStalkOfMem x V.2.1) (by
          rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, h.w])
         naturality V W i := by
          refine (cancel_mono (pullback.fst p W.1.ι)).1 ?_
          simp only [Category.assoc, diagram_map_fst, pullback.lift_fst]
          exact Category.id_comp _ }
end GlobalTheory.StalkLimit
namespace GlobalTheory
open ExtUnique
def IsGenericPointHom {U S : Scheme.{u}} [IsIntegral S] (j : U ⟶ S) : Prop :=
  ∃ e : U ≅ Spec (S.presheaf.stalk (genericPoint S)), e.hom ≫ S.fromSpecStalk (genericPoint S) = j
namespace IsGenericPointHom
theorem fromSpecStalk (S : Scheme.{u}) [IsIntegral S] : IsGenericPointHom (S.fromSpecStalk (genericPoint S)) :=
  ⟨Iso.refl _, Category.id_comp _⟩
variable {U S : Scheme.{u}} [IsIntegral S] {j : U ⟶ S}
end IsGenericPointHom
end GlobalTheory
namespace GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {j : U ⟶ S}
end GlobalTheory.Published.SemiAbelianHomExtension


