-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:05.854589+00:00
-- url     : https://prove2.me/theorems/ee77bbab-af4d-4820-825d-9d4e84eddc4a
-- title:
--   Is Iso To Inter App Pushforward Inclusion
-- statement:
--   Definitions and structural lemmas for Is Iso To Inter App Pushforward Inclusion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Theorems.Thm_GlobalTheory_SheafLES_map_comp
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_hom
import Theorems.Thm_GlobalTheory_SheafLES_res_id
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_map_hom
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_obj_obj
import Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
import Theorems.Thm_P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.SheafLES.map_zero_hom
attribute [local simp] GlobalTheory.SheafLES.res_id
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_map_hom
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_obj_obj
attribute [local simp] P2M_GlobalTheory_SheafLES___map_026ec4bafb10
attribute [local simp] P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf


set_option autoImplicit false
open CategoryTheory Limits Opposite TopologicalSpace
universe w u v' u'
noncomputable section
namespace GlobalTheory
namespace Kempf
variable {X : TopCat.{u}}
section Inter
def interFunctor (W : Opens X) : Opens X ⥤ Opens X where
  obj B := B ⊓ W
  map i := homOfLE (inf_le_inf_right W i.le)
@[simp] lemma interFunctor_obj (W B : Opens X) : (interFunctor W).obj B = B ⊓ W := rfl
def interFunctorIso (W : Opens X) :
    Opens.map W.inclusion' ⋙ W.isOpenEmbedding.functor ≅ interFunctor W :=
  NatIso.ofComponents (fun B ↦ eqToIso (Opens.functor_map_eq_inf W B))
    (fun _ ↦ Subsingleton.elim _ _)
instance isContinuous_interFunctor (W : Opens X) :
    (interFunctor W).IsContinuous (Opens.grothendieckTopology X) (Opens.grothendieckTopology X) :=
  haveI := W.isOpenEmbedding.functor_isContinuous
  Functor.isContinuous_of_iso (interFunctorIso W) _ _
variable (A : Type u') [Category.{v'} A]
def interSheaf (W : Opens X) : X.Sheaf A ⥤ X.Sheaf A :=
  (interFunctor W).sheafPushforwardContinuous A _ _
def toInter (W : Opens X) : 𝟭 (X.Sheaf A) ⟶ interSheaf A W where
  app F := ObjectProperty.homMk
    { app B := F.obj.map (homOfLE (inf_le_left : B.unop ⊓ W ≤ B.unop)).op
      naturality B B' i :=
        (F.obj.map_comp _ _).symm.trans (F.obj.map_comp
          (homOfLE (inf_le_left : B.unop ⊓ W ≤ B.unop)).op ((interFunctor W).op.map i)) }
  naturality F G f := by
    apply Sheaf.hom_ext
    ext B : 2
    exact (f.hom.naturality _).symm
variable {A}
instance isFlasque_interSheaf (W : Opens X) (F : X.Sheaf A) [hF : F.IsFlasque] :
    ((interSheaf A W).obj F).IsFlasque where
  epi _ := hF.epi _
lemma isIso_toInter_app_of_isBasis {𝔅 : Set (Opens X)} (h𝔅 : Opens.IsBasis 𝔅) (W : Opens X)
    (G : X.Sheaf A)
    (h : ∀ B ∈ 𝔅, IsIso (G.obj.map (homOfLE (inf_le_left : B ⊓ W ≤ B)).op)) :
    IsIso ((toInter A W).app G) :=
  TopCat.Sheaf.isIso_iff_isIso_basis (B := fun B : 𝔅 ↦ B.1) (by rwa [Subtype.range_coe])
    fun B ↦ h B.1 B.2
lemma isIso_toInter_app_pushforward {Y : TopCat.{u}} (j : Y ⟶ X) (W : Opens X)
    (hj : ∀ y, j y ∈ W) (G : Y.Sheaf A) :
    IsIso ((toInter A W).app ((TopCat.Sheaf.pushforward A j).obj G)) := by
  refine isIso_toInter_app_of_isBasis (𝔅 := Set.univ) ?_ W _ fun B _ ↦ ?_
  · exact Opens.isBasis_iff_nbhd.2 fun {U} _ hx ↦ ⟨U, trivial, hx, le_rfl⟩
  · have : IsIso ((Opens.map j).map (homOfLE (inf_le_left : B ⊓ W ≤ B))) :=
      ⟨homOfLE fun y hy ↦ ⟨hy, hj y⟩, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    exact inferInstanceAs (IsIso (G.obj.map
      ((Opens.map j).map (homOfLE (inf_le_left : B ⊓ W ≤ B))).op))
instance isIso_toInter_app_pushforward_inclusion' (W : Opens X)
    (G : ((Opens.toTopCat X).obj W).Sheaf A) :
    IsIso ((toInter A W).app ((TopCat.Sheaf.pushforward A W.inclusion').obj G)) :=
  isIso_toInter_app_pushforward W.inclusion' W (fun y ↦ y.2) G
end Inter
section Iso
variable (A : Type u') [Category.{u} A]
def interSheafIso (W : Opens X) :
    W.isOpenEmbedding.sheafPullback A ⋙ TopCat.Sheaf.pushforward A W.inclusion' ≅
      interSheaf A W :=
  haveI := W.isOpenEmbedding.functor_isContinuous
  Functor.sheafPushforwardContinuousComp' (interFunctorIso W) A _ _ _
def interSheafIsoPullback (W : Opens X) :
    TopCat.Sheaf.pullback AddCommGrpCat.{u} W.inclusion' ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} W.inclusion' ≅ interSheaf AddCommGrpCat.{u} W :=
  Functor.isoWhiskerRight (W.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}) _ ≪≫
    interSheafIso _ W
end Iso
section Abelian
instance (W : Opens X) : (interSheaf AddCommGrpCat.{u} W).Additive where
instance (W : Opens X) : (interSheaf AddCommGrpCat.{u} W).IsRightAdjoint :=
  inferInstanceAs ((interFunctor W).sheafPushforwardContinuous AddCommGrpCat.{u} _ _).IsRightAdjoint
variable {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
open SheafLES
end Abelian
end Kempf
end GlobalTheory


