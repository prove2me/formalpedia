-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubsingletonOfSheafPullback
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubsingletonOfSheafPullback
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:37:24.010126+00:00
-- url     : https://prove2.me/theorems/874d82cd-8a34-4fbf-839e-eca5a7e3d268
-- title:
--   Subsingleton Of Sheaf Pullback
-- statement:
--   Definitions and structural lemmas for Subsingleton Of Sheaf Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SubsingletonOfSheafPullback.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
import Theorems.Thm_GlobalTheory_Flasque_injectiveShortComplex_shortExact
import Theorems.Thm_GlobalTheory_Kempf_exists_finite_cover_map_toInter_eq_zero
import Theorems.Thm_GlobalTheory_Kempf_interSheaf_map_hom_app
import Theorems.Thm_GlobalTheory_Kempf_interSheaf_obj_obj_map
import Theorems.Thm_GlobalTheory_Kempf_interSheaf_obj_obj_obj
import Theorems.Thm_GlobalTheory_Kempf_map_eq_zero_of_map_toInter_eq_zero
import Theorems.Thm_GlobalTheory_Kempf_toInter_app_hom_app
import Theorems.Thm_GlobalTheory_QCoh_biprodSectionsEquiv_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_homAppLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_SheafLES_map_f_injective_of_surjective
import Theorems.Thm_GlobalTheory_SheafLES_map_f_one_injective_of_sections_surjective
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_hom
import Theorems.Thm_GlobalTheory_SheafLES_res_id
import Theorems.Thm_GlobalTheory_SheafLES_sections_surjective_of_subsingleton
import Theorems.Thm_GlobalTheory_SheafLES_shortExact_map_toAbSheaf
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_map_hom
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_obj_obj
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_199e9bf4dfbd
import Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
import Theorems.Thm_P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__430f6995ae54
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__c7111a18855b
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__one_of_sections_surjective_1c1eac4c541d
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Kempf.interSheaf_map_hom_app
attribute [local simp] GlobalTheory.Kempf.interSheaf_obj_obj_map
attribute [local simp] GlobalTheory.Kempf.interSheaf_obj_obj_obj
attribute [local simp] GlobalTheory.Kempf.toInter_app_hom_app
attribute [local simp] GlobalTheory.QCoh.biprodSectionsEquiv_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.homAppLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.SheafLES.map_zero_hom
attribute [local simp] GlobalTheory.SheafLES.res_id
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_map_hom
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_obj_obj
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply
attribute [local simp] P2M_GlobalTheory_SheafLES___map_026ec4bafb10
attribute [local simp] P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf


set_option autoImplicit false
open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Topology
universe u
noncomputable section
namespace GlobalTheory
namespace AffineVanishing
section Restriction
variable {X Y : TopCat.{u}} {j : Y ⟶ X} (hj : IsOpenEmbedding j)
lemma shortExact_map_sheafPullback {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) [(hj.sheafPullback AddCommGrpCat.{u}).PreservesZeroMorphisms] :
    (S.map (hj.sheafPullback AddCommGrpCat.{u})).ShortExact := by
  have h₁ : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} j) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map j) AddCommGrpCat.{u} _ _
  have h₂ : PreservesFiniteLimits (hj.sheafPullback AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso (hj.sheafPullbackIso _)
  have h₃ : PreservesFiniteColimits (hj.sheafPullback AddCommGrpCat.{u}) :=
    preservesFiniteColimits_of_natIso (hj.sheafPullbackIso _)
  exact hS.map_of_exact _
lemma subsingleton_of_sheafPullback (V : Opens Y) (n : ℕ) (F : X.Sheaf AddCommGrpCat.{u})
    (h : Subsingleton (Sheaf.H'.{u} ((hj.sheafPullback AddCommGrpCat.{u}).obj F) (n + 1) V)) :
    Subsingleton (Sheaf.H'.{u} F (n + 1) (hj.functor.obj V)) := by
  haveI : (hj.sheafPullback AddCommGrpCat.{u}).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  induction n generalizing F with
  | zero =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    exact SheafLES.subsingleton₁_one_of_sections_surjective.{u} hS _
      (SheafLES.sections_surjective_of_subsingleton.{u} (shortExact_map_sheafPullback hj hS) V h)
      (Flasque.subsingleton_H'_of_isFlasque _ 0 _)
  | succ n ih =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    have hI : (Flasque.injectiveShortComplex F).X₂.IsFlasque := inferInstance
    have hI' : ((hj.sheafPullback AddCommGrpCat.{u}).obj
        (Flasque.injectiveShortComplex F).X₂).IsFlasque := ⟨fun _ ↦ hI.epi _⟩
    exact SheafLES.subsingleton₁.{u} hS (n + 1) _
      (ih _ (SheafLES.subsingleton₃.{u} (shortExact_map_sheafPullback hj hS) (n + 1) V
        (Flasque.subsingleton_H'_of_isFlasque _ (hF := hI') n V) h))
      (Flasque.subsingleton_H'_of_isFlasque _ (n + 1) _)
end Restriction
variable {X Y : Scheme.{u}}
lemma subsingleton_of_restrict (j : Y ⟶ X) [IsOpenImmersion j] (F : X.Modules) (V : Y.Opens)
    (n : ℕ) (h : Subsingleton (cohOn (F.restrict j) V (n + 1))) :
    Subsingleton (cohOn F (j ''ᵁ V) (n + 1)) :=
  subsingleton_of_sheafPullback j.isOpenEmbedding V n ((toAbSheaf X).obj F) h
abbrev interModule (F : X.Modules) (W : X.Opens) : X.Modules :=
  (Scheme.Modules.pushforward W.ι).obj (F.restrict W.ι)
abbrev toInterModule (F : X.Modules) (W : X.Opens) : F ⟶ interModule F W :=
  (Scheme.Modules.restrictAdjunction W.ι).unit.app F
lemma map_toInterModule_eq_zero (F : X.Modules) (W V : X.Opens) (n : ℕ) (α : cohOn F V n)
    (h : SheafLES.map.{u} ((Kempf.toInter AddCommGrpCat.{u} W).app ((toAbSheaf X).obj F)) n V
      (cohOn.toH' F V n α) = 0) :
    cohOn.map ℤ (toInterModule F W) V n α = 0 :=
  haveI : IsIso ((Kempf.toInter AddCommGrpCat.{u} W).app ((toAbSheaf X).obj (interModule F W))) :=
    Kempf.isIso_toInter_app_pushforward (A := AddCommGrpCat.{u}) W.ι.base W (fun y ↦ y.2)
      ((toAbSheaf W).obj (F.restrict W.ι))
  Kempf.map_eq_zero_of_map_toInter_eq_zero.{u} ((toAbSheaf X).map (toInterModule F W)) h
lemma mono_lift_toInterModule (F : X.Modules) {ι : Type u} [Finite ι] (W : ι → X.Opens)
    (hW : ⊤ ≤ iSup W) : Mono (Pi.lift fun i ↦ toInterModule F (W i)) := by
  refine ⟨fun {Z} a b hab ↦ ?_⟩
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext s
  refine QCoh.section_eq_of_cover F (fun i ↦ (W i).ι ''ᵁ ((W i).ι ⁻¹ᵁ U))
    (fun i ↦ (W i).ι.image_preimage_le U) (fun x hx ↦ ?_) _ _ fun i ↦ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hW (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨i, ⟨x, hi⟩, hx, rfl⟩
  · have h : a ≫ toInterModule F (W i) = b ≫ toInterModule F (W i) := by
      simpa using hab =≫ Pi.π _ i
    exact congr(($h).app U s)
lemma subsingleton_top [IsAffine X] (n : ℕ)
    (ih : ∀ q, 0 < q → q < n + 1 → ∀ (G : X.Modules) [G.IsQuasicoherent] (U : X.Opens),
      IsAffineOpen U → Subsingleton (cohOn G U q))
    (F : X.Modules) [F.IsQuasicoherent] : Subsingleton (cohOn F ⊤ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun α ↦ ?_
  obtain ⟨𝔘, h𝔘, hfin, hsup, h0⟩ := Kempf.exists_finite_cover_map_toInter_eq_zero.{u}
    (X := X) (𝔅 := X.affineOpens) X.isBasis_affineOpens
    (fun B hB B' hB' ↦ IsAffineOpen.inf hB hB') ((toAbSheaf X).obj F) ⊤
    (isAffineOpen_top X).isCompact (Nat.le_add_left 1 n)
    (fun q hq hqn B hB ↦ ih q hq hqn F B hB) (cohOn.toH' F ⊤ (n + 1) α)
  haveI : Finite 𝔘 := hfin
  haveI (W : 𝔘) : IsAffine W.1 := h𝔘 W.2
  let φ : F ⟶ ∏ᶜ (fun W : 𝔘 ↦ interModule F W.1) := Pi.lift fun W ↦ toInterModule F W.1
  haveI : Mono φ := mono_lift_toInterModule F (fun W : 𝔘 ↦ W.1) (by
    rw [← sSup_eq_iSup', hsup])
  have hα : cohOn.map ℤ φ ⊤ (n + 1) α = 0 := by
    apply (cohOn.piEquiv ℤ ⊤ (n + 1) _).injective
    ext W
    rw [cohOn.piEquiv_apply, cohOn.map_map, map_zero, Pi.zero_apply, Pi.lift_π]
    exact map_toInterModule_eq_zero F W.1 ⊤ (n + 1) α (h0 W.1 W.2)
  have hS : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
    { exact := ShortComplex.exact_cokernel φ }
  have hT := SheafLES.shortExact_map_toAbSheaf hS
  have hinj : Function.Injective (SheafLES.map.{u} ((toAbSheaf X).map φ) (n + 1) ⊤) := by
    cases n with
    | zero =>
      exact SheafLES.map_f_one_injective_of_sections_surjective.{u} hT ⊤
        (QCoh.surjective_cokernel_π_app φ (isAffineOpen_top X))
    | succ n =>
      refine SheafLES.map_f_injective_of_surjective.{u} hT (n + 1) ⊤ fun y ↦ ⟨0, ?_⟩
      exact @Subsingleton.elim _ (ih (n + 1) n.succ_pos (by omega) (cokernel φ) ⊤
        (isAffineOpen_top X)) _ _
  exact (cohOn.toH' F ⊤ (n + 1)).injective (hinj (hα.trans (by
    rw [map_zero]; exact (map_zero _).symm)))
end AffineVanishing
open AffineVanishing
theorem cohOn.subsingleton_of_isAffineOpen {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (hn : 0 < n) : Subsingleton (cohOn F U n) := by
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    haveI : IsAffine U := hU
    have h := subsingleton_of_restrict U.ι F ⊤ n
      (subsingleton_top n (fun q hq hqn G _ V hV ↦ ih q hqn G hV hq) (F.restrict U.ι))
    rwa [Scheme.Opens.ι_image_top] at h
theorem coh.subsingleton_of_isAffine {X : Scheme.{u}} [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] {n : ℕ} (hn : 0 < n) : Subsingleton (coh F n) :=
  cohOn.subsingleton_of_isAffineOpen F (isAffineOpen_top X) hn
instance coh.subsingleton_succ_of_isAffine {X : Scheme.{u}} [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) : Subsingleton (coh F (n + 1)) :=
  coh.subsingleton_of_isAffine F n.succ_pos
end GlobalTheory


