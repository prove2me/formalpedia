-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_iso_pullback_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/e68d15f0-0d7e-5ab6-a7cc-a39568512555

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_iso_pullback_of_isIso
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace P2mAutInv

p2m_open "AlgebraicGeometry.OModulePresheaf TensorProduct"

theorem cechEquiv_of_affHom_inverse
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} [IsSeparated π]
    {F G : OModulePresheaf π} (φ : AffHom F G) (ψ : AffHom G F)
    (h₁ : ∀ (U : V.affineOpens) (x : F.obj U.1), ψ.app U (φ.app U x) = x)
    (h₂ : ∀ (U : V.affineOpens) (y : G.obj U.1), φ.app U (ψ.app U y) = y)
    (K : V.OrderedAffineCover) :
    Nonempty (F.H0 K ≃ₗ[R] G.H0 K) ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] G.HSucc K i) := by
  have hc₁ : ∀ (i : ℕ) (f : F.cochain K i), ψ.cochainMap K i (φ.cochainMap K i f) = f := by
    intro i f; funext s; simp only [AffHom.cochainMap_apply, h₁]
  have hc₂ : ∀ (i : ℕ) (g : G.cochain K i), φ.cochainMap K i (ψ.cochainMap K i g) = g := by
    intro i g; funext s; simp only [AffHom.cochainMap_apply, h₂]
  refine ⟨⟨LinearEquiv.ofLinear (φ.H0Map K) (ψ.H0Map K) ?_ ?_⟩, fun i => ⟨LinearEquiv.ofLinear (φ.HSuccMap K i) (ψ.HSuccMap K i) ?_ ?_⟩⟩
  · refine LinearMap.ext fun x => Subtype.ext ?_
    show φ.cochainMap K 0 (ψ.cochainMap K 0 x.1) = x.1
    exact hc₂ 0 x.1
  · refine LinearMap.ext fun x => Subtype.ext ?_
    show ψ.cochainMap K 0 (φ.cochainMap K 0 x.1) = x.1
    exact hc₁ 0 x.1
  · refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [LinearMap.comp_apply, AffHom.HSuccMap_mk, AffHom.HSuccMap_mk, LinearMap.id_apply]
      congr 1
      exact Subtype.ext (hc₂ (i + 1) x.1)
  · refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [LinearMap.comp_apply, AffHom.HSuccMap_mk, AffHom.HSuccMap_mk, LinearMap.id_apply]
      congr 1
      exact Subtype.ext (hc₁ (i + 1) x.1)

section twistIso

variable {R : Type u} [CommRing R] {P P' : Scheme.{u}} (π' : P' ⟶ Spec (CommRingCat.of R))
  (Φ : P ⟶ P') [IsIso Φ] (N : P'.Modules)

abbrev eU (U : P'.Opens) : Γ(P', U) →+* Γ(P, Φ ⁻¹ᵁ U) := (Φ.appLE U (Φ ⁻¹ᵁ U) le_rfl).hom

theorem eU_eq (U : P'.Opens) : eU Φ U = (Φ.app U).hom := by
  change (Φ.appLE U (Φ ⁻¹ᵁ U) le_rfl).hom = (Φ.app U).hom
  rw [Scheme.Hom.app_eq_appLE]

theorem eU_bijective (U : P'.Opens) : Function.Bijective (eU Φ U) := by
  rw [eU_eq]
  exact ConcreteCategory.bijective_of_isIso (Φ.app U)

noncomputable def eEquiv (U : P'.Opens) : Γ(P', U) ≃+* Γ(P, Φ ⁻¹ᵁ U) :=
  RingEquiv.ofBijective (eU Φ U) (eU_bijective Φ U)

theorem pf_smul (U : P'.Opens) (a : Γ(P', U)) (b : (OModulePresheaf.pushforwardUnit π' Φ).obj U) :
    a • b = (show (OModulePresheaf.pushforwardUnit π' Φ).obj U from eU Φ U a * (show Γ(P, Φ ⁻¹ᵁ U) from b)) := rfl

def onePf (U : P'.Opens) : (OModulePresheaf.pushforwardUnit π' Φ).obj U := (1 : Γ(P, Φ ⁻¹ᵁ U))

theorem eU_mul_onePf (U : P'.Opens) (a : (P'.presheaf.obj (Opposite.op U))) :
    a • onePf π' Φ U = (eU Φ U a : (OModulePresheaf.pushforwardUnit π' Φ).obj U) := by
  change eU Φ U a * 1 = eU Φ U a
  exact mul_one _

noncomputable def fwd (U : P'.Opens) :
    (OModulePresheaf.ofModules π' N).obj U →ₗ[R] ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π' U
  { toFun := fun m => (show ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U from onePf π' Φ U ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] m)
    map_add' := fun x y => TensorProduct.tmul_add _ x y
    map_smul' := fun r m => by
      show onePf π' Φ U ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] (algebraMap R (P'.presheaf.obj (Opposite.op U)) r • m) =
        algebraMap R (P'.presheaf.obj (Opposite.op U)) r • (onePf π' Φ U ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] m)
      rw [TensorProduct.tmul_smul] }

theorem fwd_apply (U : P'.Opens) (m : (OModulePresheaf.ofModules π' N).obj U) :
    fwd π' Φ N U m = (onePf π' Φ U ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] m : ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U) := rfl

theorem fwd_smul_sections (U : P'.Opens) (a : (P'.presheaf.obj (Opposite.op U))) (m : (OModulePresheaf.ofModules π' N).obj U) :
    fwd π' Φ N U (a • m) = a • fwd π' Φ N U m := by
  rw [fwd_apply, fwd_apply, TensorProduct.tmul_smul]
  rfl

noncomputable def bwdBil (U : P'.Opens) :
    (OModulePresheaf.pushforwardUnit π' Φ).obj U →ₗ[(P'.presheaf.obj (Opposite.op U))]
      ((OModulePresheaf.ofModules π' N).obj U →ₗ[(P'.presheaf.obj (Opposite.op U))] (OModulePresheaf.ofModules π' N).obj U) :=
  LinearMap.mk₂ (P'.presheaf.obj (Opposite.op U))
    (fun (b : (OModulePresheaf.pushforwardUnit π' Φ).obj U) (m : (OModulePresheaf.ofModules π' N).obj U) =>
      (eEquiv Φ U).symm (show Γ(P, Φ ⁻¹ᵁ U) from b) • m)
    (fun b₁ b₂ m => by
      show (eEquiv Φ U).symm ((show Γ(P, Φ ⁻¹ᵁ U) from b₁) + (show Γ(P, Φ ⁻¹ᵁ U) from b₂)) • m = _
      rw [map_add, add_smul])
    (fun a b m => by
      show (eEquiv Φ U).symm (eU Φ U a * (show Γ(P, Φ ⁻¹ᵁ U) from b)) • m = a • ((eEquiv Φ U).symm _ • m)
      rw [map_mul, show (eEquiv Φ U).symm (eU Φ U a) = a from (eEquiv Φ U).symm_apply_apply a, mul_smul])
    (fun b m₁ m₂ => smul_add _ _ _)
    (fun a b m => by rw [smul_comm])

noncomputable def bwd (U : P'.Opens) :
    ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U →ₗ[R] (OModulePresheaf.ofModules π' N).obj U :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π' U
  { toFun := TensorProduct.lift (bwdBil π' Φ N U)
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r t => by
      show TensorProduct.lift (bwdBil π' Φ N U) (algebraMap R (P'.presheaf.obj (Opposite.op U)) r • t) =
        r • TensorProduct.lift (bwdBil π' Φ N U) t
      have h := (TensorProduct.lift (bwdBil π' Φ N U)).map_smul (algebraMap R (P'.presheaf.obj (Opposite.op U)) r) t
      exact h.trans (algebraMap_smul _ r _) }

theorem bwd_tmul (U : P'.Opens) (b : (OModulePresheaf.pushforwardUnit π' Φ).obj U) (m : (OModulePresheaf.ofModules π' N).obj U) :
    bwd π' Φ N U (b ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] m : ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U) =
      ((eEquiv Φ U).symm b) • m := by
  show TensorProduct.lift (bwdBil π' Φ N U) (b ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] m) = _
  rw [TensorProduct.lift.tmul]; rfl

theorem bwd_fwd (U : P'.Opens) (m : (OModulePresheaf.ofModules π' N).obj U) : bwd π' Φ N U (fwd π' Φ N U m) = m := by
  rw [fwd_apply, bwd_tmul]
  change (eEquiv Φ U).symm 1 • m = m
  rw [map_one, one_smul]

theorem fwd_bwd (U : P'.Opens) (t : ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U) :
    fwd π' Φ N U (bwd π' Φ N U t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ((fwd π' Φ N U).comp (bwd π' Φ N U)).map_zero
  | tmul b m =>
    rw [bwd_tmul, fwd_smul_sections, fwd_apply]
    change ((((eEquiv Φ U).symm b) • onePf π' Φ U) ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] m :
      ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U) = _
    rw [eU_mul_onePf]
    congr 1
    exact (eEquiv Φ U).apply_symm_apply b
  | add x y hx hy =>
    refine (((fwd π' Φ N U).comp (bwd π' Φ N U)).map_add x y).trans ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hx, hy]
    rfl

noncomputable def fwdHom : AffHom (OModulePresheaf.ofModules π' N) ((OModulePresheaf.pushforwardUnit π' Φ).twist N) where
  app U := fwd π' Φ N U.1
  app_smul U a m := fwd_smul_sections π' Φ N U.1 a m
  naturality {U U'} h := by
    refine LinearMap.ext fun m => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, fwd_apply, fwd_apply]
    rw [OModulePresheaf.twist_res_tmul]
    congr 1
    symm
    change (P.presheaf.map (homOfLE _).op).hom 1 = 1
    exact map_one _

noncomputable def bwdHom : AffHom ((OModulePresheaf.pushforwardUnit π' Φ).twist N) (OModulePresheaf.ofModules π' N) where
  app U := bwd π' Φ N U.1
  app_smul U a t := by
    have hinj : Function.Injective (fwd π' Φ N U.1) :=
      Function.LeftInverse.injective (g := bwd π' Φ N U.1) (bwd_fwd π' Φ N U.1)
    apply hinj
    have hs : ∀ m : (OModulePresheaf.ofModules π' N).obj U.1, fwd π' Φ N U.1 (a • m) = a • fwd π' Φ N U.1 m :=
      (fwdHom π' Φ N).app_smul U a
    rw [hs, fwd_bwd, fwd_bwd]
  naturality {U U'} h := by
    refine LinearMap.ext fun t => ?_
    have hinj : Function.Injective (fwd π' Φ N U.1) :=
      Function.LeftInverse.injective (g := bwd π' Φ N U.1) (bwd_fwd π' Φ N U.1)
    apply hinj
    rw [LinearMap.comp_apply, LinearMap.comp_apply, fwd_bwd]
    have hn : fwd π' Φ N U.1 ((OModulePresheaf.ofModules π' N).res h (bwd π' Φ N U'.1 t)) =
        ((OModulePresheaf.pushforwardUnit π' Φ).twist N).res h (fwd π' Φ N U'.1 (bwd π' Φ N U'.1 t)) :=
      congrArg (fun f => f (bwd π' Φ N U'.1 t)) ((fwdHom π' Φ N).naturality h)
    rw [hn, fwd_bwd]

end twistIso

theorem cechEquiv_twist_pushforwardUnit_of_isIso
    {R : Type u} [CommRing R] {P P' : Scheme.{u}} (π' : P' ⟶ Spec (CommRingCat.of R)) [IsSeparated π']
    (Φ : P ⟶ P') [IsIso Φ] (N : P'.Modules) (𝔚' : P'.OrderedAffineCover) :
    Nonempty (((OModulePresheaf.pushforwardUnit π' Φ).twist N).H0 𝔚' ≃ₗ[R] (OModulePresheaf.ofModules π' N).H0 𝔚') ∧
      ∀ i : ℕ, Nonempty (((OModulePresheaf.pushforwardUnit π' Φ).twist N).HSucc 𝔚' i ≃ₗ[R]
        (OModulePresheaf.ofModules π' N).HSucc 𝔚' i) :=
  cechEquiv_of_affHom_inverse (bwdHom π' Φ N) (fwdHom π' Φ N)
    (fun U t => fwd_bwd π' Φ N U.1 t) (fun U m => bwd_fwd π' Φ N U.1 m) 𝔚'

end P2mAutInv

end

open P2mAutInv in
theorem solution
    {R : Type u} [CommRing R] {P P' : Scheme.{u}} (π' : P' ⟶ Spec (CommRingCat.of R)) [IsSeparated π']
    (Φ : P ⟶ P') [IsIso Φ]
    (N' : P'.Modules) (hN' : Scheme.Modules.IsInvertible N')
    (N : P.Modules) (e : N ≅ (Scheme.Modules.pullback Φ).obj N')
    (𝔚' : P'.OrderedAffineCover)
    (h : (OModulePresheaf.ofModules π' N').H0 𝔚' = ⊥ ∧ ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules π' N').HSucc 𝔚' j))
    (𝔚 : P.OrderedAffineCover) :
    (OModulePresheaf.ofModules (Φ ≫ π') N).H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules (Φ ≫ π') N).HSucc 𝔚 j) := by
  classical
  have htriv := hN'.exists_trivialization
  have htrivP : ∀ x : P, ∃ U : P.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pullback Φ).obj N') ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := (hN'.pullback Φ).exists_trivialization
  haveI : IsSeparated (Φ ≫ π') := inferInstance

  obtain ⟨⟨a0⟩, aS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso (Φ ≫ π') e 𝔚

  have hq := OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial (Φ ≫ π') ((Scheme.Modules.pullback Φ).obj N') htrivP
  obtain ⟨⟨e0⟩, eS⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated (Φ ≫ π')
    ((Scheme.Modules.pullback Φ).obj N') hq 𝔚 (𝔚'.comap Φ)

  obtain ⟨⟨f0⟩, fS⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit π' Φ 𝔚' N' htriv

  obtain ⟨⟨g0⟩, gS⟩ := cechEquiv_twist_pushforwardUnit_of_isIso π' Φ N' 𝔚'
  refine ⟨?_, fun j => ?_⟩
  · have E := ((a0.trans e0).trans f0).trans g0
    haveI hs' : Subsingleton ((OModulePresheaf.ofModules π' N').H0 𝔚') := by
      rw [h.1]; infer_instance
    haveI hs : Subsingleton ((OModulePresheaf.ofModules (Φ ≫ π') N).H0 𝔚) := E.toEquiv.subsingleton
    exact (Submodule.eq_bot_iff _).mpr fun x hx =>
      congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : (OModulePresheaf.ofModules (Φ ≫ π') N).H0 𝔚) ⟨0, Submodule.zero_mem _⟩)
  · obtain ⟨a⟩ := aS j; obtain ⟨e'⟩ := eS j; obtain ⟨f'⟩ := fS j; obtain ⟨g'⟩ := gS j
    haveI := h.2 j
    exact (((a.trans e').trans f').trans g').toEquiv.subsingleton

end S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_iso_pullback_of_isIso
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_iso_pullback_of_isIso (solution)
