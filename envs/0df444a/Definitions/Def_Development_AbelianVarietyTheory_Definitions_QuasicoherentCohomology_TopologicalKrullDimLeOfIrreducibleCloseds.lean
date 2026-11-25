-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
-- name    : Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:52.539339+00:00
-- url     : https://prove2.me/theorems/e15cc5d4-0034-5bad-bd43-c1f8a6b9cb1e
-- title:
--   Topological Krull Dim Le Of Irreducible Closeds
-- statement:
--   Definitions and structural lemmas for Topological Krull Dim Le Of Irreducible Closeds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Theorems.Thm_GlobalTheory_QCoh_biprodSectionsEquiv_apply
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_res
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_zero
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_germLinear
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_germLinear_pointOfPrime
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen_iff
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_iff_forall_affine
import Theorems.Thm_GlobalTheory_QCoh_mem_primeCompl_primeIdealOf_iff
import Theorems.Thm_GlobalTheory_QCoh_pointOfPrime_primeIdealOf
import Theorems.Thm_GlobalTheory_QCoh_primeIdealOf_pointOfPrime
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_res_res_ring
import Theorems.Thm_GlobalTheory_QCoh_res_self_ring
import Theorems.Thm_GlobalTheory_QCoh_stalkLinearEquiv_apply
import Theorems.Thm_GlobalTheory_QCoh_stalkLinear_add
import Theorems.Thm_GlobalTheory_QCoh_stalkLinear_zero
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
attribute [local simp] GlobalTheory.QCoh.biprodSectionsEquiv_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.pointOfPrime_primeIdealOf
attribute [local simp] GlobalTheory.QCoh.primeIdealOf_pointOfPrime
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.QCoh.stalkLinearEquiv_apply
attribute [local simp] GlobalTheory.QCoh.stalkLinear_add
attribute [local simp] GlobalTheory.QCoh.stalkLinear_zero
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.SheafLES.map_zero_hom
attribute [local simp] GlobalTheory.SheafLES.res_id
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_map_hom
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_obj_obj
attribute [local simp] P2M_GlobalTheory_SheafLES___map_026ec4bafb10
attribute [local simp] P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
namespace GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
section Finite
class IsFiniteQC (F : X.Modules) : Prop where

  isQuasicoherent : F.IsQuasicoherent

  finite_affine : ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U)
attribute [instance 100] IsFiniteQC.isQuasicoherent
variable (F) in

theorem finite_sections [IsFiniteQC F] (hU : IsAffineOpen U) : Module.Finite Γ(X, U) Γ(F, U) :=
  IsFiniteQC.finite_affine U hU
instance finite_sections_affineOpens [IsFiniteQC F] (U : X.affineOpens) : Module.Finite Γ(X, U) Γ(F, U) :=
  finite_sections F U.2
instance finite_globalSections_of_affine [IsFiniteQC F] [IsAffine X] : Module.Finite Γ(X, ⊤) Γ(F, ⊤) :=
  finite_sections F (isAffineOpen_top X)
theorem exists_affine_mem_le (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact ⟨V, hV, hxV, hVU⟩
theorem exists_affine_mem (x : X) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V :=
  have ⟨V, hV, hx, _⟩ := exists_affine_mem_le (U := ⊤) x trivial
  ⟨V, hV, hx⟩
variable (F) in

theorem finite_stalk_of_finite_sections [F.IsQuasicoherent] (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) Γ(F, U)] (x : U) :
    Module.Finite (X.presheaf.stalk (x : X)) (F.presheaf.stalk (x : X) :) :=
  have := hU.isLocalization_stalk x
  have := isLocalizedModule_germLinear F hU x
  Module.Finite.of_isLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (germLinear F x)
instance finite_stalk [IsFiniteQC F] (x : X) :
    Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x :) := by
  obtain ⟨U, hU, hx⟩ := exists_affine_mem x
  have := finite_sections F hU
  exact finite_stalk_of_finite_sections F hU ⟨x, hx⟩
variable (F) in

theorem finite_sections_basicOpen [F.IsQuasicoherent] (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) Γ(F, U)] (f : Γ(X, U)) :
    Module.Finite Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) :=
  have := hU.isLocalization_basicOpen f
  have := isLocalizedModule_resBasicOpen F hU f
  Module.Finite.of_isLocalizedModule (.powers f) (resBasicOpen F f)
theorem IsFiniteQC.of_forall_exists_affine [F.IsQuasicoherent]
    (h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ Module.Finite Γ(X, U) Γ(F, U)) :
    IsFiniteQC F := by
  refine ⟨inferInstance, fun U hU ↦ ?_⟩
  let s : Set Γ(X, U) := {f | Module.Finite Γ(X, X.basicOpen f) Γ(F, X.basicOpen f)}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨V, hV, hxV, hfin⟩ := h x
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter hU hV x ⟨hx, hxV⟩
    have := finite_sections_basicOpen F hV g
    rw [← e] at this
    exact Opens.mem_iSup.mpr ⟨⟨f, this⟩, hxf⟩
  exact @Module.Finite.of_localizationSpan' _ _ _ _ _ s hs (fun g ↦ Γ(F, X.basicOpen g.1)) _ _
    (fun g ↦ Γ(X, X.basicOpen g.1)) _ _ (fun g ↦ hU.isLocalization_basicOpen g.1) _ _
    (fun g ↦ resBasicOpen F g.1) (fun g ↦ isLocalizedModule_resBasicOpen F hU g.1) fun g ↦ g.2
theorem isFiniteQC_iff_finite_top [IsAffine X] [F.IsQuasicoherent] :
    IsFiniteQC F ↔ Module.Finite Γ(X, ⊤) Γ(F, ⊤) :=
  ⟨fun _ ↦ inferInstance, fun h ↦ .of_forall_exists_affine fun _ ↦
    ⟨⊤, isAffineOpen_top X, trivial, h⟩⟩
theorem IsFiniteQC.of_epi (φ : F ⟶ G) [Epi φ] [IsFiniteQC F] [G.IsQuasicoherent] :
    IsFiniteQC G :=
  ⟨inferInstance, fun U hU ↦
    have := finite_sections F hU
    .of_surjective (appLinear φ U) (surjective_app_of_epi φ hU)⟩
variable (F) in

theorem isNoetherian_sections [IsLocallyNoetherian X] [IsFiniteQC F] (hU : IsAffineOpen U) :
    _root_.IsNoetherian Γ(X, U) Γ(F, U) :=
  have := finite_sections F hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  inferInstance
theorem IsFiniteQC.of_mono [IsLocallyNoetherian X] (φ : F ⟶ G) [Mono φ] [F.IsQuasicoherent]
    [IsFiniteQC G] : IsFiniteQC F :=
  ⟨inferInstance, fun U hU ↦
    have := isNoetherian_sections G hU
    .of_injective (appLinear φ U) (injective_app_of_mono φ U)⟩
instance isFiniteQC_cokernel (φ : F ⟶ G) [F.IsQuasicoherent] [IsFiniteQC G] :
    IsFiniteQC (cokernel φ) :=
  .of_epi (cokernel.π φ)
instance isFiniteQC_image (φ : F ⟶ G) [IsFiniteQC F] [G.IsQuasicoherent] :
    IsFiniteQC (image φ) :=
  .of_epi (factorThruImage φ)
instance isFiniteQC_kernel [IsLocallyNoetherian X] (φ : F ⟶ G) [IsFiniteQC F]
    [G.IsQuasicoherent] : IsFiniteQC (kernel φ) :=
  .of_mono (kernel.ι φ)
section Sums
variable {ι : Type*} [Fintype ι] {A : ι → X.Modules} (p : ∀ i, F ⟶ A i) (q : ∀ i, A i ⟶ F)
theorem sum_app_app (h : ∑ i, p i ≫ q i = 𝟙 F) (s : Γ(F, U)) :
    ∑ i, (q i).app U ((p i).app U s) = s := by
  let e : (F ⟶ F) →+ Γ(F, U) := AddMonoidHom.mk' (fun φ ↦ φ.app U s) fun _ _ ↦ rfl
  have := map_sum e (fun i ↦ p i ≫ q i) Finset.univ
  rw [h] at this
  exact this.symm
theorem isQuasicoherent_of_sum_eq_id (h : ∑ i, p i ≫ q i = 𝟙 F) [∀ i, (A i).IsQuasicoherent] :
    F.IsQuasicoherent := by
  refine (isQuasicoherent_iff_forall_affine F).2 fun U hU f ↦
    (isLocalizedModule_resBasicOpen_iff F f).2 ⟨fun s ↦ ?_, fun t ht ↦ ?_⟩
  · choose n t ht using fun i ↦
      exists_pow_smul_eq_res (A i) hU f (X.basicOpen_le f) rfl ((p i).app _ s)
    refine ⟨∑ i, n i, ∑ i, (q i).app U (f ^ (∑ j, n j - n i) • t i), ?_⟩
    rw [map_sum, ← sum_app_app p q h s, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hi : n i ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    rw [← app_res, Scheme.Modules.map_smul, ← ht, smul_smul, map_pow, ← pow_add,
      Nat.sub_add_cancel hi, Scheme.Modules.Hom.app_smul]
  · choose n hn using fun i ↦ exists_pow_smul_eq_zero (A i) hU f (X.basicOpen_le f) rfl
      ((p i).app _ t) (by rw [← app_res, ht, map_zero])
    refine ⟨∑ i, n i, ?_⟩
    rw [← sum_app_app p q h t, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hi : n i ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    rw [← Scheme.Modules.Hom.app_smul, ← Nat.sub_add_cancel hi, pow_add, mul_smul, hn, smul_zero,
      map_zero]
theorem IsFiniteQC.of_sum_eq_id (h : ∑ i, p i ≫ q i = 𝟙 F) [hA : ∀ i, IsFiniteQC (A i)] :
    IsFiniteQC F := by
  classical
  refine ⟨isQuasicoherent_of_sum_eq_id p q h, fun U hU ↦ ?_⟩
  have (i : ι) := finite_sections (A i) hU
  refine .of_surjective (LinearMap.lsum Γ(X, U) (fun i ↦ Γ(A i, U)) ℕ
    fun i ↦ appLinear (q i) U) fun s ↦ ⟨fun i ↦ (p i).app U s, ?_⟩
  simpa using sum_app_app p q h s
end Sums
theorem IsFiniteQC.of_isColimit_cofan {ι : Type*} [Finite ι] {A : ι → X.Modules}
    [∀ i, IsFiniteQC (A i)] {c : Cofan A} (hc : IsColimit c) : IsFiniteQC c.pt := by
  classical
  have := Fintype.ofFinite ι
  refine .of_sum_eq_id (fun i ↦ Cofan.IsColimit.desc hc fun j ↦
    if h : j = i then eqToHom (h ▸ rfl) else 0) c.inj (Cofan.IsColimit.hom_ext hc _ _ fun j ↦ ?_)
  simp [Preadditive.comp_sum, Cofan.IsColimit.fac_assoc, dite_comp]
theorem IsFiniteQC.of_isLimit_fan {ι : Type*} [Finite ι] {A : ι → X.Modules}
    [∀ i, IsFiniteQC (A i)] {c : Fan A} (hc : IsLimit c) : IsFiniteQC c.pt := by
  classical
  have := Fintype.ofFinite ι
  refine .of_sum_eq_id c.proj (fun i ↦ Fan.IsLimit.lift hc fun j ↦
    if h : i = j then eqToHom (h ▸ rfl) else 0) (Fan.IsLimit.hom_ext hc _ _ fun j ↦ ?_)
  simp [Preadditive.sum_comp, Fan.IsLimit.fac, comp_dite]
instance isFiniteQC_sigmaObj {ι : Type*} [Finite ι] (A : ι → X.Modules) [HasCoproduct A]
    [∀ i, IsFiniteQC (A i)] :
    IsFiniteQC (∐ A) :=
  .of_isColimit_cofan (coproductIsCoproduct A)
instance isFiniteQC_piObj {ι : Type*} [Finite ι] (A : ι → X.Modules) [HasProduct A]
    [∀ i, IsFiniteQC (A i)] :
    IsFiniteQC (∏ᶜ A) :=
  .of_isLimit_fan (productIsProduct A)
instance isFiniteQC_biproduct {ι : Type*} [Finite ι] (A : ι → X.Modules) [HasBiproduct A]
    [∀ i, IsFiniteQC (A i)] :
    IsFiniteQC (⨁ A) :=
  .of_isLimit_fan (biproduct.isLimit A)
instance isFiniteQC_biprod [IsFiniteQC F] [IsFiniteQC G] : IsFiniteQC (F ⊞ G) :=
  .of_sum_eq_id (ι := Bool) (A := fun b ↦ b.casesOn F G)
    (fun b ↦ b.casesOn biprod.fst biprod.snd) (fun b ↦ b.casesOn biprod.inl biprod.inr)
    (by rw [Fintype.sum_bool, add_comm]; exact biprod.total)
    (hA := fun b ↦ b.casesOn ‹IsFiniteQC F› ‹IsFiniteQC G›)
variable (X) in

abbrev structureModule : X.Modules := SheafOfModules.unit X.ringCatSheaf
variable (X) in

abbrev freeModule (ι : Type u) : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) ι
variable (U) in

def structureModuleSectionsEquiv : Γ(structureModule X, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  LinearEquiv.refl Γ(X, U) Γ(X, U)
instance isFiniteQC_structureModule : IsFiniteQC (structureModule X) where
  isQuasicoherent := (isQuasicoherent_iff_forall_affine _).2 fun U hU f ↦
    have := hU.isLocalization_basicOpen f
    inferInstanceAs (IsLocalizedModule (.powers f) (Algebra.linearMap Γ(X, U) Γ(X, X.basicOpen f)))
  finite_affine U _ := inferInstanceAs (Module.Finite Γ(X, U) Γ(X, U))
instance isFiniteQC_freeModule (ι : Type u) [Finite ι] : IsFiniteQC (freeModule X ι) :=
  .of_isColimit_cofan (A := fun _ : ι ↦ structureModule X)
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) ι)
section Restrict
variable {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
variable (F) in

theorem finite_sections_restrict_iff (W : Y.Opens) :
    Module.Finite Γ(Y, W) Γ(F.restrict g, W) ↔ Module.Finite Γ(X, g ''ᵁ W) Γ(F, g ''ᵁ W) := by
  let σ := (g.appIso W).commRingCatIsoToRingEquiv
  constructor <;> intro h
  · have : RingHomSurjective (σ.symm : Γ(Y, W) →+* Γ(X, g ''ᵁ W)) := ⟨σ.symm.surjective⟩
    let l : Γ(F.restrict g, W) →ₛₗ[(σ.symm : Γ(Y, W) →+* Γ(X, g ''ᵁ W))] Γ(F, g ''ᵁ W) :=
      { toFun := (F.restrictAppIso g W).hom
        map_add' := map_add _
        map_smul' := fun _ _ ↦ rfl }
    exact .of_surjective l (ConcreteCategory.bijective_of_isIso (F.restrictAppIso g W).hom).2
  · have : RingHomSurjective (σ : Γ(X, g ''ᵁ W) →+* Γ(Y, W)) := ⟨σ.surjective⟩
    let l : Γ(F, g ''ᵁ W) →ₛₗ[(σ : Γ(X, g ''ᵁ W) →+* Γ(Y, W))] Γ(F.restrict g, W) :=
      { toFun := (F.restrictAppIso g W).inv
        map_add' := map_add _
        map_smul' := fun r s ↦ F.smul_restrictAppIso_inv_apply g W r s }
    exact .of_surjective l (ConcreteCategory.bijective_of_isIso (F.restrictAppIso g W).inv).2
instance isFiniteQC_restrict [IsFiniteQC F] : IsFiniteQC (F.restrict g) :=
  ⟨inferInstance, fun W hW ↦ (finite_sections_restrict_iff F g W).2
    (finite_sections F (hW.image_of_isOpenImmersion g))⟩
end Restrict
end Finite
section Tilde
variable {R : CommRingCat.{u}}
def tildeTopEquiv (M : ModuleCat.{u} R) : M ≃ₗ[R] Γ(tilde M, ⊤) :=
  (tilde.isoTop M).toLinearEquiv
theorem algebraMap_Spec_top_bijective : Function.Bijective (algebraMap R Γ(Spec R, ⊤)) := by
  have : ⇑(algebraMap R Γ(Spec R, ⊤)) = (Scheme.ΓSpecIso R).inv := rfl
  rw [this]
  exact ConcreteCategory.bijective_of_isIso _
theorem isFiniteQC_Spec_iff (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsFiniteQC M ↔ Module.Finite R Γ(M, ⊤) := by
  rw [isFiniteQC_iff_finite_top]
  refine ⟨fun _ ↦ ?_, fun _ ↦ .of_restrictScalars_finite R _ _⟩
  have : Module.Finite R Γ(Spec R, ⊤) :=
    .of_surjective (Algebra.linearMap R _) algebraMap_Spec_top_bijective.2
  exact .trans Γ(Spec R, ⊤) _
theorem isFiniteQC_tilde_iff (M : ModuleCat.{u} R) : IsFiniteQC (tilde M) ↔ Module.Finite R M := by
  rw [isFiniteQC_Spec_iff]
  exact (Module.Finite.equiv_iff (tildeTopEquiv M)).symm
instance isFiniteQC_tilde (M : ModuleCat.{u} R) [Module.Finite R M] : IsFiniteQC (tilde M) :=
  (isFiniteQC_tilde_iff M).2 ‹_›
end Tilde
section FiniteType
set_option backward.isDefEq.respectTransparency false in

theorem exists_presentation_over [F.IsQuasicoherent] (hU : IsAffineOpen U)
    (s : Set Γ(F.restrict hU.fromSpec, ⊤)) (hs : Submodule.span Γ(X, U) s = ⊤)
    (t : Set (s →₀ Γ(X, U))) (ht : Submodule.span Γ(X, U) t =
      LinearMap.ker (Finsupp.linearCombination Γ(X, U) ((↑) : s → Γ(F.restrict hU.fromSpec, ⊤)))) :
    ∃ P : (F.over U).Presentation, P.generators.I = s ∧ P.relations.I = t := by
  let M := F.restrict hU.fromSpec
  have := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let P₁ : M.Presentation := SheafOfModules.Presentation.ofIsIso.{u, u, u} M.fromTildeΓ
    (presentationTilde.{u} _ s hs t ht)
  let iso₁ : Scheme.Modules.restrictFunctor hU.fromSpec ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom ≅ Scheme.Modules.restrictFunctor U.ι :=
    (Scheme.Modules.restrictFunctorComp _ _).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec
  let P₂ : (F.restrict U.ι).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso₁.app F).hom
      (Scheme.Modules.presentationRestrict hU.isoSpec.hom P₁)
  let e := Scheme.Modules.overEquiv U
  have : PreservesColimitsOfSize.{u, u} e.inverse := inferInstance
  let iso₂ : e.inverse.obj (F.restrict U.ι) ≅ F.over U :=
    e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app F).symm ≪≫
      (e.unitIso.app (F.over U)).symm
  exact ⟨SheafOfModules.Presentation.ofIsIso.{u, u, u} iso₂.hom
    (P₂.map e.inverse (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm), rfl, rfl⟩
set_option backward.isDefEq.respectTransparency false in

instance IsFiniteQC.isFiniteType [IsFiniteQC F] : F.IsFiniteType := by
  have H (U : X.affineOpens) : ∃ σ : (F.over U.1).GeneratingSections, σ.IsFiniteType := by
    obtain ⟨s, hs⟩ := ((isFiniteQC_Spec_iff (F.restrict U.2.fromSpec)).1 inferInstance).fg_top
    obtain ⟨P, hP, -⟩ := exists_presentation_over U.2 (F := F) s hs _ (Submodule.span_eq _)
    exact ⟨P.generators, ⟨hP ▸ inferInstance⟩⟩
  choose σ hσ using H
  let q : SheafOfModules.LocalGeneratorsData.{u, u, u, u} (R := X.ringCatSheaf) F :=
    { I := ↥X.affineOpens, X := fun U ↦ U.1, generators := σ
      coversTop := by rw [Opens.coversTop_iff]; exact iSup_affineOpens_eq_top X }
  have hq : q.IsFiniteType :=
    SheafOfModules.LocalGeneratorsData.IsFiniteType.mk.{u, u, u, u} (p := q) hσ
  exact SheafOfModules.IsFiniteType.mk.{u, u, u} (Exists.intro q hq)
end FiniteType
section Support
variable (F) in

def support : Set X := {x | Nontrivial (F.presheaf.stalk x :)}
variable (F) in

def restrictStalkAddEquiv {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] (y : Y) :
    ((F.restrict g).presheaf.stalk y :) ≃+ (F.presheaf.stalk (g y) :) :=
  ((Scheme.Modules.restrictStalkNatIso g y).app F).addCommGroupIsoToAddEquiv
theorem structureModuleSectionsEquiv_res (h : V ≤ U) (s : Γ(structureModule X, U)) :
    structureModuleSectionsEquiv V ((structureModule X).presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (structureModuleSectionsEquiv U s) := rfl
theorem germ_smul_germ_one (x : X) (hx : x ∈ U) (s : Γ(structureModule X, U)) :
    X.presheaf.germ U x hx (structureModuleSectionsEquiv U s) •
      (structureModule X).presheaf.germ ⊤ x trivial ((structureModuleSectionsEquiv ⊤).symm 1) =
      (structureModule X).presheaf.germ U x hx s := by
  rw [← (structureModule X).presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hx, ← germ_smul]
  congr 1
  apply (structureModuleSectionsEquiv U).injective
  rw [map_smul, structureModuleSectionsEquiv_res, LinearEquiv.apply_symm_apply, map_one,
    smul_eq_mul, mul_one]
def structureModuleStalkEquiv (x : X) :
    ((structureModule X).presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton (X.presheaf.stalk x) _
    ((structureModule X).presheaf.germ ⊤ x trivial
      ((structureModuleSectionsEquiv ⊤).symm 1))) <| by
      refine ⟨(injective_iff_map_eq_zero _).2 fun r hr ↦ ?_, fun t ↦ ?_⟩
      · obtain ⟨U, hx, f, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨s, rfl⟩ := (structureModuleSectionsEquiv U).surjective f
        rw [LinearMap.toSpanSingleton_apply, germ_smul_germ_one] at hr
        obtain ⟨W, hW, i, j, e⟩ := (structureModule X).presheaf.germ_eq x hx hx s 0
          (by rw [hr, map_zero])
        rw [map_zero] at e
        rw [← X.presheaf.germ_res_apply (homOfLE i.le) x hW, ← structureModuleSectionsEquiv_res]
        have e' : (structureModule X).presheaf.map (homOfLE i.le).op s = 0 := e
        rw [e', map_zero, map_zero]
      · obtain ⟨U, hx, s, rfl⟩ := (structureModule X).presheaf.exists_germ_eq t
        exact ⟨_, germ_smul_germ_one x hx s⟩).symm
@[simp]
theorem structureModuleStalkEquiv_germ (x : X) (hx : x ∈ U) (s : Γ(structureModule X, U)) :
    structureModuleStalkEquiv x ((structureModule X).presheaf.germ U x hx s) =
      X.presheaf.germ U x hx (structureModuleSectionsEquiv U s) := by
  rw [structureModuleStalkEquiv, LinearEquiv.symm_apply_eq]
  exact (germ_smul_germ_one x hx s).symm
@[simp]
theorem support_structureModule : support (structureModule X) = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ (structureModuleStalkEquiv x).toEquiv.nontrivial
theorem support_tilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    support (tilde M) = Module.support R M := by
  refine Set.ext fun x : PrimeSpectrum.Top R ↦ ?_
  have := x.isPrime
  exact (IsLocalizedModule.iso x.asIdeal.primeCompl
    (tilde.toStalk M x).hom).toEquiv.nontrivial_congr.symm
end Support
section Dimension
variable (F) in

def suppDim : WithBot ℕ∞ := topologicalKrullDim (support F)
@[simp]
theorem suppDim_structureModule : suppDim (structureModule X) = topologicalKrullDim X := by
  rw [suppDim, support_structureModule]
  exact (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
theorem suppDim_tilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R) [Module.Finite R M] :
    suppDim (tilde M) = Module.supportDim R M := by
  rw [suppDim, support_tilde, Module.supportDim, Module.support_eq_zeroLocus,
    Order.krullDim_eq_of_orderIso (PrimeSpectrum.zeroLocusEquivIrreducibleCloseds _),
    Order.krullDim_orderDual]
  rfl
end Dimension
section Associated
variable (F) in

def assPoints : Set X :=
  {x | maximalIdeal (X.presheaf.stalk x) ∈
    associatedPrimes (X.presheaf.stalk x) (F.presheaf.stalk x :)}
variable [IsLocallyNoetherian X]
variable (F) in

theorem mem_associatedPrimes_stalk_iff [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U)
    (Q : Ideal (X.presheaf.stalk (x : X))) :
    Q ∈ associatedPrimes (X.presheaf.stalk (x : X)) (F.presheaf.stalk (x : X) :) ↔
      Q.comap (algebraMap Γ(X, U) _) ∈ associatedPrimes Γ(X, U) Γ(F, U) := by
  have := hU.isLocalization_stalk x
  have := isLocalizedModule_germLinear F hU x
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  rw [← Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    (hU.primeIdealOf x).asIdeal.primeCompl _ (germLinear F x)]
  rfl
theorem mem_assPoints_iff_primeIdealOf [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    (x : X) ∈ assPoints F ↔ (hU.primeIdealOf x).asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) := by
  have := hU.isLocalization_stalk x
  rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk (x : X))
    (hU.primeIdealOf x).asIdeal]
  exact mem_associatedPrimes_stalk_iff F hU x _
omit [IsLocallyNoetherian X] in

theorem assPoints_tilde {R : CommRingCat.{u}} [IsNoetherianRing R] (M : ModuleCat.{u} R) :
    assPoints (tilde M) = PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M := by
  refine Set.ext fun x : Spec R ↦ ?_
  have hb := algebraMap_Spec_top_bijective (R := R)
  have : IsLocalization (Submonoid.powers (1 : R)) Γ(Spec R, ⊤) :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one hb
  have : IsLocalizedModule (Submonoid.powers (1 : R)) (tildeTopEquiv M).toLinearMap :=
    IsLocalizedModule.Away.mk_of_addCommGroup (by rw [map_one]; exact isUnit_one)
      (fun s ↦ ⟨0, (tildeTopEquiv M).symm s, by simp⟩) fun t ht ↦ ⟨0, by simpa using ht⟩
  refine (mem_assPoints_iff_primeIdealOf (isAffineOpen_top (Spec R)) ⟨x, trivial⟩).trans ?_
  rw [← Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    (Submonoid.powers (1 : R)) _ (tildeTopEquiv M).toLinearMap]
  have e : ((isAffineOpen_top (Spec R)).primeIdealOf ⟨x, trivial⟩).asIdeal.comap
      (algebraMap R Γ(Spec R, ⊤)) = x.asIdeal := by
    ext r
    rw [Ideal.mem_comap, ← not_iff_not]
    refine (mem_primeCompl_primeIdealOf_iff (isAffineOpen_top (Spec R)) ⟨x, trivial⟩ _).trans ?_
    have : (Spec R).basicOpen (algebraMap R Γ(Spec R, ⊤) r) = PrimeSpectrum.basicOpen r :=
      basicOpen_eq_of_affine r
    rw [this]
    rfl
  rw [Set.mem_preimage, e]
  rfl
end Associated
section Fibre
instance residueFieldAlgebra (x : X) : Algebra (X.presheaf.stalk x) (X.residueField x) :=
  inferInstanceAs (Algebra (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x)))
instance residueFieldAlgebraSections (x : U) : Algebra Γ(X, U) (X.residueField (x : X)) :=
  (X.evaluation U x x.2).hom.toAlgebra
instance isScalarTower_residueField (x : U) :
    IsScalarTower Γ(X, U) (X.presheaf.stalk (x : X)) (X.residueField (x : X)) :=
  .of_algebraMap_eq fun _ ↦ rfl
variable (F) in

abbrev fibre (x : X) : Type u := X.residueField x ⊗[X.presheaf.stalk x] (F.presheaf.stalk x :)
variable (F) in

def fibreMk (x : X) : (F.presheaf.stalk x :) →ₗ[X.presheaf.stalk x] fibre F x :=
  TensorProduct.mk _ _ _ 1
theorem fibreMk_apply (x : X) (t : (F.presheaf.stalk x :)) : fibreMk F x t = 1 ⊗ₜ t := rfl
variable (F) in

def fibreEquivQuotient (x : X) : fibre F x ≃ₗ[X.presheaf.stalk x]
    ((F.presheaf.stalk x :) ⧸ (maximalIdeal (X.presheaf.stalk x) • ⊤ :
      Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :))) :=
  quotTensorEquivQuotSMul _ (maximalIdeal (X.presheaf.stalk x))
@[simp]
theorem fibreEquivQuotient_fibreMk (x : X) (t : (F.presheaf.stalk x :)) :
    fibreEquivQuotient F x (fibreMk F x t) = Submodule.Quotient.mk t :=
  quotTensorEquivQuotSMul_mk_one_tmul _ t
variable (F) in

def fibreEval (x : U) : Γ(F, U) →ₗ[Γ(X, U)] fibre F x :=
  (fibreMk F x).restrictScalars Γ(X, U) ∘ₗ germLinear F x
theorem fibreEval_apply (x : U) (s : Γ(F, U)) :
    fibreEval F x s = fibreMk F x (F.presheaf.germ U x x.2 s) := rfl
def fibreMap (φ : F ⟶ G) (x : X) : fibre F x →ₗ[X.residueField x] fibre G x :=
  (stalkLinear φ x).baseChange (X.residueField x)
@[simp]
theorem fibreMap_fibreMk (φ : F ⟶ G) (x : X) (t : (F.presheaf.stalk x :)) :
    fibreMap φ x (fibreMk F x t) = fibreMk G x (stalkLinear φ x t) := rfl
@[simp]
theorem fibreMap_fibreEval (φ : F ⟶ G) (x : U) (s : Γ(F, U)) :
    fibreMap φ x (fibreEval F x s) = fibreEval G x (φ.app U s) := by
  rw [fibreEval_apply, fibreEval_apply, fibreMap_fibreMk, stalkLinear_germ]
@[simp]
theorem fibreMap_id (x : X) : fibreMap (𝟙 F) x = LinearMap.id := by
  rw [fibreMap, stalkLinear_id, LinearMap.baseChange_id]
@[simp]
theorem fibreMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) (x : X) :
    fibreMap (φ ≫ ψ) x = fibreMap ψ x ∘ₗ fibreMap φ x := by
  rw [fibreMap, stalkLinear_comp, LinearMap.baseChange_comp]; rfl
@[simp]
theorem fibreMap_add (φ ψ : F ⟶ G) (x : X) :
    fibreMap (φ + ψ) x = fibreMap φ x + fibreMap ψ x := by
  rw [fibreMap, stalkLinear_add, LinearMap.baseChange_add]; rfl
@[simp]
theorem fibreMap_zero (x : X) : fibreMap (0 : F ⟶ G) x = 0 := by
  rw [fibreMap, stalkLinear_zero, LinearMap.baseChange_zero]
def fibreEquiv (e : F ≅ G) (x : X) : fibre F x ≃ₗ[X.residueField x] fibre G x :=
  (stalkLinearEquiv e x).baseChange _ (X.residueField x) _ _
@[simp]
theorem fibreEquiv_apply (e : F ≅ G) (x : X) (t : fibre F x) :
    fibreEquiv e x t = fibreMap e.hom x t := rfl
instance finite_fibre [IsFiniteQC F] (x : X) : Module.Finite (X.residueField x) (fibre F x) :=
  inferInstance
def structureModuleFibreEquiv (x : X) :
    fibre (structureModule X) x ≃ₗ[X.residueField x] X.residueField x :=
  ((structureModuleStalkEquiv x).baseChange _ (X.residueField x) _ _).trans
    (AlgebraTensorModule.rid _ _ _)
@[simp]
theorem structureModuleFibreEquiv_fibreEval (x : U) (s : Γ(structureModule X, U)) :
    structureModuleFibreEquiv (x : X) (fibreEval (structureModule X) x s) =
      X.evaluation U x x.2 (structureModuleSectionsEquiv U s) := by
  rw [fibreEval_apply, fibreMk_apply, structureModuleFibreEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, structureModuleStalkEquiv_germ, AlgebraTensorModule.rid_tmul,
    ← Algebra.algebraMap_eq_smul_one]
  rfl
end Fibre
section Flat
variable {R : Type*} [CommRing R] (ρ : R →+* Γ(X, ⊤))
variable (U) in

def baseHom : R →+* Γ(X, U) := (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp ρ
@[simp]
theorem res_baseHom (h : V ≤ U) (r : R) :
    X.presheaf.map (homOfLE h).op (baseHom U ρ r) = baseHom V ρ r :=
  res_res_ring le_top h (ρ r)
@[simp]
theorem baseHom_top : baseHom ⊤ ρ = ρ := RingHom.ext fun r ↦ res_self_ring le_top (ρ r)
@[simp]
theorem germ_baseHom (x : X) (hx : x ∈ U) (r : R) :
    X.presheaf.germ U x hx (baseHom U ρ r) = X.presheaf.germ ⊤ x trivial (ρ r) :=
  X.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hx (ρ r)
variable (F U) in

abbrev baseModule : Module R Γ(F, U) := Module.compHom _ (baseHom U ρ)
variable (F) in

abbrev baseModuleStalk (x : X) : Module R (F.presheaf.stalk x :) :=
  Module.compHom _ ((X.presheaf.germ ⊤ x trivial).hom.comp ρ)
def structureRingHom {R : CommRingCat.{u}} (f : X ⟶ Spec R) : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom
variable (F) in

def IsFlatOver : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    letI := baseModule F U ρ
    Module.Flat R Γ(F, U)
variable {ρ}
theorem IsFlatOver.flat (h : IsFlatOver F ρ) (hU : IsAffineOpen U) [m : Module R Γ(F, U)]
    (hm : ∀ (r : R) (s : Γ(F, U)), r • s = baseHom U ρ r • s) : Module.Flat R Γ(F, U) := by
  obtain rfl : m = baseModule F U ρ := Module.ext' _ _ hm
  exact h U hU
theorem flat_of_isLocalizedModule_of_flat {A S M N : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M] [AddCommGroup N] [Module A N]
    [Module S N] [IsScalarTower A S N] (T : Submonoid S) (f : M →ₗ[S] N) [IsLocalizedModule T f]
    [h : Module.Flat A M] : Module.Flat A N := by
  rw [Module.Flat.iff_lTensor_injectiveₛ] at h ⊢
  intro P _ _ Q
  have := IsLocalizedModule.map_injective T (AlgebraTensorModule.rTensor A Q f)
    (AlgebraTensorModule.rTensor A P f) (AlgebraTensorModule.lTensor S M Q.subtype) (h Q)
  rw [IsLocalizedModule.map_lTensor] at this
  exact this
variable (F ρ) in

theorem flat_sections_iff_stalk [F.IsQuasicoherent] (hU : IsAffineOpen U) :
    (letI := baseModule F U ρ
     Module.Flat R Γ(F, U)) ↔ ∀ x ∈ U,
      letI := baseModuleStalk F ρ x
      Module.Flat R (F.presheaf.stalk x :) := by
  letI := baseModule F U ρ
  letI := (baseHom U ρ).toAlgebra
  haveI : IsScalarTower R Γ(X, U) Γ(F, U) := .of_algebraMap_smul fun _ _ ↦ rfl
  have hst (x : U) : letI := baseModuleStalk F ρ x
      IsScalarTower R Γ(X, U) (F.presheaf.stalk (x : X) :) :=
    letI := baseModuleStalk F ρ x
    .of_algebraMap_smul fun r t ↦ congrArg (· • t) (germ_baseHom ρ x x.2 r)
  constructor
  · intro h x hx
    obtain ⟨x, rfl⟩ : ∃ x' : U, x' = x := ⟨⟨x, hx⟩, rfl⟩
    letI := baseModuleStalk F ρ x
    have := hst x
    have := isLocalizedModule_germLinear F hU x
    exact flat_of_isLocalizedModule_of_flat (hU.primeIdealOf x).asIdeal.primeCompl
      (germLinear F x)
  · intro h
    exact @Module.flat_of_isLocalized_maximal R Γ(X, U) _ _ _ Γ(F, U) _ _ _ _
      (fun P hP ↦ (F.presheaf.stalk (pointOfPrime hU ⟨P, hP.isPrime⟩ : X) :)) _
      (fun P hP ↦ baseModuleStalk F ρ _) _ (fun P hP ↦ hst _)
      (fun P hP ↦ germLinear F (pointOfPrime hU ⟨P, hP.isPrime⟩))
      (fun P hP ↦ isLocalizedModule_germLinear_pointOfPrime F hU P)
      fun P hP ↦ h _ (pointOfPrime hU ⟨P, hP.isPrime⟩).2
theorem isFlatOver_iff_stalk [F.IsQuasicoherent] :
    IsFlatOver F ρ ↔ ∀ x : X,
      letI := baseModuleStalk F ρ x
      Module.Flat R (F.presheaf.stalk x :) := by
  refine ⟨fun h x ↦ ?_, fun h U hU ↦ (flat_sections_iff_stalk F ρ hU).2 fun x _ ↦ h x⟩
  obtain ⟨U, hU, hx⟩ := exists_affine_mem x
  exact (flat_sections_iff_stalk F ρ hU).1 (h U hU) x hx
theorem IsFlatOver.of_forall_exists_affine [F.IsQuasicoherent]
    (h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      letI := baseModule F U ρ
      Module.Flat R Γ(F, U)) : IsFlatOver F ρ :=
  isFlatOver_iff_stalk.2 fun x ↦
    have ⟨_, hU, hx, hf⟩ := h x
    (flat_sections_iff_stalk F ρ hU).1 hf x hx
variable (ρ) in

def sectionsBaseLinear (φ : F ⟶ G) (U : X.Opens) :
    letI := baseModule F U ρ
    letI := baseModule G U ρ
    Γ(F, U) →ₗ[R] Γ(G, U) :=
  letI := baseModule F U ρ
  letI := baseModule G U ρ
  { toFun := φ.app U
    map_add' := map_add _
    map_smul' := fun r s ↦ φ.app_smul (baseHom U ρ r) s }
theorem isFlatOver_Spec_iff {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsFlatOver M (Scheme.ΓSpecIso R).inv.hom ↔ Module.Flat R Γ(M, ⊤) :=
  ⟨fun h ↦ h ⊤ (isAffineOpen_top _),
    fun h ↦ .of_forall_exists_affine fun _ ↦ ⟨⊤, isAffineOpen_top _, trivial, h⟩⟩
theorem isFlatOver_tilde_iff {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    IsFlatOver (tilde M) (Scheme.ΓSpecIso R).inv.hom ↔ Module.Flat R M := by
  rw [isFlatOver_Spec_iff]
  exact (Module.Flat.equiv_iff (tildeTopEquiv M)).symm
end Flat
section Examples
abbrev tildeIntQuotient (I : Ideal ℤ) : (Spec (CommRingCat.of ℤ)).Modules :=
  tilde (R := CommRingCat.of ℤ) (ModuleCat.of ℤ (ℤ ⧸ I))
example (I : Ideal ℤ) : IsFiniteQC (tildeIntQuotient I) :=
  (isFiniteQC_tilde_iff _).2 (inferInstanceAs (Module.Finite ℤ (ℤ ⧸ I)))
example (I : Ideal ℤ) [hI : I.IsPrime] :
    assPoints (tildeIntQuotient I) = {(⟨I, hI⟩ : PrimeSpectrum ℤ)} := by
  have : IsNoetherianRing (CommRingCat.of ℤ) := inferInstanceAs (IsNoetherianRing ℤ)
  rw [assPoints_tilde]
  change PrimeSpectrum.asIdeal ⁻¹' associatedPrimes ℤ (ℤ ⧸ I) = {(⟨I, hI⟩ : PrimeSpectrum ℤ)}
  rw [associatedPrimes.eq_singleton_of_isPrimary hI.isPrimary, hI.radical]
  ext P
  simp [PrimeSpectrum.ext_iff]
example (I : Ideal ℤ) [hI : I.IsMaximal] : suppDim (tildeIntQuotient I) = 0 ∧
    suppDim (structureModule (Spec (CommRingCat.of ℤ))) = 1 := by
  constructor
  · have : Module.Finite (CommRingCat.of ℤ) (ModuleCat.of ℤ (ℤ ⧸ I)) :=
      inferInstanceAs (Module.Finite ℤ (ℤ ⧸ I))
    rw [suppDim_tilde]
    refine (Module.supportDim_quotient_eq_ringKrullDim I).trans ?_
    letI := Ideal.Quotient.field I
    exact ringKrullDim_eq_zero_of_field _
  · rw [suppDim_structureModule]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim ℤ).trans
      (IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField)
example : IsFlatOver (tilde (R := CommRingCat.of ℤ) (ModuleCat.of ℤ ℚ))
      (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom ∧
    ¬ IsFlatOver (tildeIntQuotient (Ideal.span {2})) (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom := by
  refine ⟨(isFlatOver_tilde_iff _).2 (IsLocalization.flat ℚ (nonZeroDivisors ℤ)), fun h ↦ ?_⟩
  have h : Module.Flat ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)}) := (isFlatOver_tilde_iff _).1 h
  have h1 : (1 : ℤ ⧸ Ideal.span {(2 : ℤ)}) = 0 :=
    (Module.Flat.isSMulRegular_of_nonZeroDivisors (r := (2 : ℤ))
      (mem_nonZeroDivisors_of_ne_zero two_ne_zero)).right_eq_zero_of_smul (by
        rw [← Algebra.algebraMap_eq_smul_one]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
  have := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
  omega
example (x : X) : Module.finrank (X.residueField x) (fibre (structureModule X) x) = 1 := by
  rw [(structureModuleFibreEquiv x).finrank_eq, Module.finrank_self]
end Examples
end GlobalTheory.QCoh


