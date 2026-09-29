-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/54eb4e13-d304-5a22-a80b-8469d4e7939a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_Module_Flat_exists_mem_smul_top_map_eq_of_ker_baseChange_le_range
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_ofModules_pullback_fst_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_iso_hom_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace C1LSol
open TensorProduct

theorem one_tmul_eq_zero_iff {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (hA : Function.Surjective (algebraMap R A)) {M : Type u} [AddCommGroup M] [Module R M] (m : M) :
    (1 : A) ⊗ₜ[R] m = 0 ↔ m ∈ RingHom.ker (algebraMap R A) • (⊤ : Submodule R M) := by
  let e : (R ⧸ RingHom.ker (algebraMap R A)) ≃ₐ[R] A :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R A) (fun b => hA b)
  let T : A ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker (algebraMap R A) • (⊤ : Submodule R M)) :=
    (TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl R M)).trans
      (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker (algebraMap R A)))
  have he1 : e.symm.toLinearEquiv (1 : A) = Ideal.Quotient.mk _ 1 := by
    rw [AlgEquiv.toLinearEquiv_apply, map_one]; rfl
  have hT : T ((1 : A) ⊗ₜ[R] m) = Submodule.Quotient.mk m := by
    show TensorProduct.quotTensorEquivQuotSMul M _ (TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl R M) ((1 : A) ⊗ₜ[R] m)) = _
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, he1, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [← Submodule.Quotient.mk_eq_zero, ← hT, map_eq_zero_iff _ T.injective]

end C1LSol

theorem solution
    {R R₀ k : Type u} [CommRing R] [IsLocalRing R] [CommRing R₀] [Field k]
    (π : R →+* R₀) (hπ : Function.Surjective π) (hsmall : RingHom.ker π * IsLocalRing.maximalIdeal R = ⊥)
    (s : R →+* k) (hs : Function.Surjective s) (hsk : RingHom.ker s = IsLocalRing.maximalIdeal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of R₀)) (g : X₀ ⟶ X)
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (.of k)) (gk : Xk ⟶ X)
    (hgk : IsPullback gk fk f (Spec.map (CommRingCat.ofHom s)))
    (𝓜 : X.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (hvan : ∀ 𝒰 : Xk.OrderedAffineCover,
      Subsingleton ((OModulePresheaf.ofModules fk ((Scheme.Modules.pullback gk).obj 𝓜)).HSucc 𝒰 0))
    (s₀ : Γ((Scheme.Modules.pullback g).obj 𝓜, g ⁻¹ᵁ ⊤)) :
    ∃ σ : Γ(𝓜, ⊤), Scheme.Modules.pullbackLocalSection g σ = s₀ := by
  classical
  letI algR₀ : Algebra R R₀ := π.toAlgebra
  letI algk : Algebra R k := s.toAlgebra
  have hsalg : (algebraMap R k : R →+* k) = s := rfl
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨𝒰⟩ := AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_compactSpace_univ X
  have htriv := h𝓜.exists_trivialization

  haveI hfl : ∀ i : ℕ, Module.Flat R ((OModulePresheaf.ofModules f 𝓜).cochain 𝒰 i) := fun i =>
    AlgebraicGeometry.OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial f 𝓜 htriv 𝒰 i
  have hdd : ∀ w, (OModulePresheaf.ofModules f 𝓜).d 𝒰 1 ((OModulePresheaf.ofModules f 𝓜).d 𝒰 0 w) = 0 := fun w =>
    LinearMap.congr_fun (AlgebraicGeometry.OModulePresheaf.d_comp_d (OModulePresheaf.ofModules f 𝓜) 𝒰 0) w

  obtain ⟨E, hEd, hEf⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial f 𝒰 𝓜 htriv R₀
  obtain ⟨⟨-, hφk⟩, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial f 𝒰 𝓜 htriv k

  have hvan' : Subsingleton ((OModulePresheaf.ofModules (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R k))
      ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R k))).obj 𝓜)).HSucc
        (𝒰.baseChange f k) 0) :=
    AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_ofModules_pullback_fst_of_isPullback
      f (Scheme.TwoAffineOpenCover.specMap R k) fk gk hgk 𝓜 h𝓜 0 hvan (𝒰.baseChange f k)
  have hex : LinearMap.ker (((OModulePresheaf.ofModules f 𝓜).d 𝒰 1).baseChange k) ≤ LinearMap.range (((OModulePresheaf.ofModules f 𝓜).d 𝒰 0).baseChange k) := by
    obtain ⟨φ, hφs, hφker⟩ := hφk 0
    intro z hz
    have hz0 : (⟨z, hz⟩ : LinearMap.ker (((OModulePresheaf.ofModules f 𝓜).d 𝒰 (0 + 1)).baseChange k)) ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
    rw [hφker] at hz0
    exact hz0

  refine AlgebraicGeometry.Scheme.Modules.exists_pullbackLocalSection_eq_of_iso_hom_comp_eq
    (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀)) hg.isoPullback g hg.isoPullback_hom_fst 𝓜 ?_ s₀
  intro y
  have htop : (⊤ : (pullback f (Scheme.TwoAffineOpenCover.specMap R R₀)).Opens) ≤ (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀)) ⁻¹ᵁ ⊤ :=
    (Scheme.Hom.preimage_top (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).ge

  let yT : Γ(((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜), ⊤) := ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜).presheaf.map (homOfLE htop).op y
  let c₀ : (OModulePresheaf.ofModules (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R R₀)) ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜)).cochain (𝒰.baseChange f R₀) 0 := fun t => (OModulePresheaf.ofModules (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R R₀)) ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜)).res (le_top : (𝒰.baseChange f R₀).inter t ≤ ⊤) yT
  have hc₀t : ∀ t, c₀ t = ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜).presheaf.map (homOfLE (le_top : (𝒰.baseChange f R₀).inter t ≤ ⊤)).op yT := fun t => rfl
  have hc₀ : (OModulePresheaf.ofModules (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R R₀)) ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜)).d (𝒰.baseChange f R₀) 0 c₀ = 0 := by
    funext t
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, Pi.zero_apply]
    rw [OModulePresheaf.res_res, OModulePresheaf.res_res]
    exact add_neg_cancel _

  have hEyb : E 0 ((E 0).symm c₀) = c₀ := (E 0).apply_symm_apply c₀
  have hdyb : ((OModulePresheaf.ofModules f 𝓜).d 𝒰 0).baseChange R₀ ((E 0).symm c₀) = 0 := by
    apply (E (0 + 1)).injective
    rw [map_zero]
    have := LinearMap.congr_fun (hEd 0) ((E 0).symm c₀)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at this
    rw [this, hEyb, hc₀]
  obtain ⟨x, hx⟩ := TensorProduct.mk_surjective R ((OModulePresheaf.ofModules f 𝓜).cochain 𝒰 0) R₀ hπ ((E 0).symm c₀)
  have hx' : (1 : R₀) ⊗ₜ[R] x = (E 0).symm c₀ := hx
  have hdx0 : (1 : R₀) ⊗ₜ[R] ((OModulePresheaf.ofModules f 𝓜).d 𝒰 0 x) = 0 := by
    rw [← LinearMap.baseChange_tmul, hx', hdyb]
  have hmem : (OModulePresheaf.ofModules f 𝓜).d 𝒰 0 x ∈ RingHom.ker π • (⊤ : Submodule R ((OModulePresheaf.ofModules f 𝓜).cochain 𝒰 1)) :=
    (C1LSol.one_tmul_eq_zero_iff (A := R₀) hπ _).mp hdx0

  have hI : RingHom.ker π * RingHom.ker (algebraMap R k) = ⊥ := by rw [hsalg, hsk]; exact hsmall
  obtain ⟨b, hb, hdb⟩ := Module.Flat.exists_mem_smul_top_map_eq_of_ker_baseChange_le_range k
    (hs : Function.Surjective (algebraMap R k)) (RingHom.ker π) hI
    ((OModulePresheaf.ofModules f 𝓜).d 𝒰 0) ((OModulePresheaf.ofModules f 𝓜).d 𝒰 1) hex ((OModulePresheaf.ofModules f 𝓜).d 𝒰 0 x) hmem (hdd x)
  have hb0 : (1 : R₀) ⊗ₜ[R] b = 0 := (C1LSol.one_tmul_eq_zero_iff (A := R₀) hπ b).mpr hb
  have hdx' : (OModulePresheaf.ofModules f 𝓜).d 𝒰 0 (x - b) = 0 := by rw [map_sub, hdb, sub_self]
  have hx'yb : (1 : R₀) ⊗ₜ[R] (x - b) = (E 0).symm c₀ := by rw [TensorProduct.tmul_sub, hb0, sub_zero, hx']

  obtain ⟨σ, hσ, -⟩ :=
    (AlgebraicGeometry.OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique f 𝓜 𝒰 (x - b)).mp hdx'
  refine ⟨σ, ?_⟩

  let zT : Γ(((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜), ⊤) := ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜).presheaf.map (homOfLE htop).op (Scheme.Modules.pullbackLocalSection (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀)) σ)
  have key : ∀ t : (𝒰.baseChange f R₀).Idx 0, c₀ t = ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜).presheaf.map (homOfLE (le_top : (𝒰.baseChange f R₀).inter t ≤ ⊤)).op zT := by
    intro t
    rw [← hEyb, ← hx'yb, hEf 0 1 (x - b) t, one_smul, hσ t]
    show (OModulePresheaf.ofModules (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R R₀)) ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜)).res (𝒰.baseChange_inter_le f R₀ t)
        (Scheme.Modules.pullbackLocalSection (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀)) (𝓜.presheaf.map (homOfLE le_top).op σ)) = _
    rw [← Scheme.Modules.map_homOfLE_pullbackLocalSection (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀)) (le_top : 𝒰.inter t ≤ ⊤) σ]
    show ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜).presheaf.map _ (((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜).presheaf.map _ (Scheme.Modules.pullbackLocalSection (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀)) σ)) =
      ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜).presheaf.map _ (((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜).presheaf.map _ (Scheme.Modules.pullbackLocalSection (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀)) σ))
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← CategoryTheory.ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    rfl
  obtain ⟨z, -, huniq⟩ := (AlgebraicGeometry.OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique
    (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R R₀)) ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜) (𝒰.baseChange f R₀) c₀).mp hc₀
  have hzy : yT = z := huniq yT hc₀t
  have hzz : zT = z := huniq zT key
  have hTT : zT = yT := hzz.trans hzy.symm

  have hback : ∀ w : Γ(((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜), (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀)) ⁻¹ᵁ ⊤),
      ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜).presheaf.map (homOfLE (le_top : (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀)) ⁻¹ᵁ ⊤ ≤ ⊤)).op (((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜).presheaf.map (homOfLE htop).op w) = w := by
    intro w
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
    show ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜).presheaf.map ((homOfLE htop) ≫ (homOfLE (le_top : (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀)) ⁻¹ᵁ ⊤ ≤ ⊤))).op w = w
    rw [Subsingleton.elim ((homOfLE htop) ≫ (homOfLE (le_top : (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀)) ⁻¹ᵁ ⊤ ≤ ⊤))) (𝟙 _), op_id,
      ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀))).obj 𝓜).presheaf.map_id]
    rfl
  have h1 := hback (Scheme.Modules.pullbackLocalSection (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R R₀)) σ)
  have h2 := hback y
  exact h1.symm.trans ((congrArg _ hTT).trans h2)

end S_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc (solution)
