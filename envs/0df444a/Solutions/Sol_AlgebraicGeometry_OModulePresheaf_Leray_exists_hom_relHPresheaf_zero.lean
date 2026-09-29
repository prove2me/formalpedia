-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.Leray.exists_hom_relHPresheaf_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b290fe72-fdbe-5f34-bd8e-ac5fd69f390b

import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero.AlgebraicGeometry TopologicalSpace Opposite"

noncomputable section

set_option autoImplicit false

section

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Spec Scheme Scheme.Hom.appLE_map OModulePresheaf.Leray.relAug OModulePresheaf.Leray.relAltd OModulePresheaf.Leray.pullOpen OModulePresheaf.Leray.relHPresheaf Scheme.OrderedAffineCover OModulePresheaf Scheme.OrderedAffineCoverOf Scheme.OrderedAffineCoverOf.moduleSections OModulePresheaf.Hom"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "Leray.relAug Leray.relAltd Leray.pullOpen Leray.relHPresheaf res_res d res mk module obj moduleSections Hom"
namespace Leray
p2m_export "AlgebraicGeometry.OModulePresheaf.Leray" "relAug relAltd relAltd_apply' relAltHB pullOpen relHPresheaf"
namespace RelHZero
p2m_open "AlgebraicGeometry.OModulePresheaf.Leray AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}

theorem res_res {O₁ O₂ O₃ : V'.Opens} (h₂₁ : O₂ ≤ O₁) (h₃₂ : O₃ ≤ O₂) (x : Γ(V', O₁)) :
    (V'.presheaf.map (homOfLE h₃₂).op).hom ((V'.presheaf.map (homOfLE h₂₁).op).hom x)
      = (V'.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_self {O : V'.Opens} (h : O ≤ O) (x : Γ(V', O)) :
    (V'.presheaf.map (homOfLE h).op).hom x = x := by
  rw [Subsingleton.elim (homOfLE h).op (𝟙 (op O)), V'.presheaf.map_id]
  rfl

variable (K' : Scheme.OrderedAffineCover V')

theorem idx_zero_ext {σ τ : K'.Idx 0} (h : σ.1 0 = τ.1 0) : σ = τ :=
  Subtype.ext (funext fun j => by rw [Fin.fin_one_eq_zero j]; exact h)

theorem inter_zero (σ : K'.Idx 0) : K'.inter σ = K'.U (σ.1 0) :=
  le_antisymm (K'.inter_le σ 0)
    (show K'.U (σ.1 0) ≤ ⨅ j, K'.U (σ.1 j) from le_iInf fun j => by rw [Fin.fin_one_eq_zero j])

variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) (U : Z.Opens)

theorem relCover_le :
    (⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U
      ≤ ⨆ τ : K'.Idx 0, K'.inter τ ⊓ (Opens.map p.base).obj U := by
  rw [← iSup_inf_eq]
  refine inf_le_inf_right _ (K'.iSup_eq_top.ge.trans (iSup_le fun i => ?_))
  let τ : K'.Idx 0 := ⟨fun _ => i, fun a b hab => absurd hab (by rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; exact lt_irrefl _)⟩
  exact le_iSup_of_le (f := fun τ : K'.Idx 0 => K'.inter τ) τ (inter_zero K' τ).ge

theorem ker_relAltd_zero :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    LinearMap.ker (relAltd p πZ K' U 0) = LinearMap.range (relAug p πZ K' U) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine le_antisymm (fun z hz => ?_) (fun _ ⟨w, hw⟩ => hw ▸ ?_)
  ·
    have hkey : ∀ (σ σ' : K'.Idx 0), σ' = σ → ∀ {O : V'.Opens}
        (hσ : O ≤ K'.inter σ ⊓ (Opens.map p.base).obj U)
        (hσ' : O ≤ K'.inter σ' ⊓ (Opens.map p.base).obj U),
        (V'.presheaf.map (homOfLE hσ').op).hom (z σ')
          = (V'.presheaf.map (homOfLE hσ).op).hom (z σ) := by
      rintro σ _ rfl O hσ hσ'; rfl

    have hcore : ∀ (a b : K'.ι), a < b → ∀ (σ τ : K'.Idx 0),
        σ.1 0 = a → τ.1 0 = b → ∀ {O : V'.Opens}
        (hOσ : O ≤ K'.inter σ ⊓ (Opens.map p.base).obj U)
        (hOτ : O ≤ K'.inter τ ⊓ (Opens.map p.base).obj U),
        O ≤ (K'.U a ⊓ K'.U b) ⊓ (Opens.map p.base).obj U →
        (V'.presheaf.map (homOfLE hOσ).op).hom (z σ)
          = (V'.presheaf.map (homOfLE hOτ).op).hom (z τ) := by
      intro a b hab σ τ hσ hτ O hOσ hOτ hOab
      let ρ : K'.Idx 1 := ⟨![a, b], by
        intro c d hcd; fin_cases c <;> fin_cases d <;> simp_all⟩
      have h00 : Fin.succAbove (0 : Fin 2) 0 = 1 := by decide
      have h10 : Fin.succAbove (1 : Fin 2) 0 = 0 := by decide
      have hρ0 : K'.face ρ 0 = τ := idx_zero_ext K'
        (show (![a, b] : Fin 2 → K'.ι) (Fin.succAbove 0 0) = τ.1 0 by rw [h00]; exact hτ.symm)
      have hρ1 : K'.face ρ 1 = σ := idx_zero_ext K'
        (show (![a, b] : Fin 2 → K'.ι) (Fin.succAbove 1 0) = σ.1 0 by rw [h10]; exact hσ.symm)
      have hOρ : O ≤ K'.inter ρ ⊓ (Opens.map p.base).obj U :=
        le_inf (hOab.trans (inf_le_left.trans (le_iInf fun j => by
          fin_cases j; exacts [inf_le_left, inf_le_right]))) (hOσ.trans inf_le_right)
      have hk := congrFun (LinearMap.mem_ker.mp hz) ρ
      rw [relAltd_apply', Fin.sum_univ_two, Pi.zero_apply, Fin.val_zero,
        Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul, ← sub_eq_add_neg] at hk
      have key := congrArg (V'.presheaf.map (homOfLE hOρ).op).hom (sub_eq_zero.mp hk)
      rw [res_res, res_res,
        hkey τ _ hρ0 hOτ (hOρ.trans (inf_le_inf_right _ (K'.inter_le_inter_face ρ 0))),
        hkey σ _ hρ1 hOσ (hOρ.trans (inf_le_inf_right _ (K'.inter_le_inter_face ρ 1)))]
        at key
      exact key.symm
    have hcompat : TopCat.Presheaf.IsCompatible V'.sheaf.1
        (fun τ => K'.inter τ ⊓ (Opens.map p.base).obj U) z := by
      intro σ τ
      have hOab : (K'.inter σ ⊓ (Opens.map p.base).obj U) ⊓
            (K'.inter τ ⊓ (Opens.map p.base).obj U)
          ≤ (K'.U (σ.1 0) ⊓ K'.U (τ.1 0)) ⊓ (Opens.map p.base).obj U :=
        le_inf (inf_le_inf (inf_le_left.trans (inter_zero K' σ).le)
          (inf_le_left.trans (inter_zero K' τ).le)) (inf_le_left.trans inf_le_right)
      rcases lt_trichotomy (σ.1 0) (τ.1 0) with h | h | h
      · exact hcore _ _ h σ τ rfl rfl inf_le_left inf_le_right hOab
      · exact hkey τ σ (idx_zero_ext K' h) inf_le_right inf_le_left
      · exact (hcore _ _ h τ σ rfl rfl inf_le_right inf_le_left
          (hOab.trans (inf_le_inf_right _ (inf_comm _ _).le))).symm
    obtain ⟨w, hw, -⟩ := V'.sheaf.existsUnique_gluing'
      (fun τ => K'.inter τ ⊓ (Opens.map p.base).obj U)
      ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U)
      (fun τ => homOfLE (inf_le_inf_right _ le_top))
      (relCover_le K' p U) z hcompat
    exact ⟨w, funext hw⟩
  ·
    refine LinearMap.mem_ker.mpr (funext fun ρ => ?_)
    rw [relAltd_apply', Fin.sum_univ_two, Pi.zero_apply, Fin.val_zero,
      Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul]
    refine add_neg_eq_zero.mpr ?_
    show (V'.presheaf.map _).hom ((V'.presheaf.map _).hom w)
      = (V'.presheaf.map _).hom ((V'.presheaf.map _).hom w)
    rw [res_res, res_res]

theorem relAug_injective :
    Function.Injective (relAug p πZ K' U) := fun w₁ w₂ hw =>
  V'.sheaf.eq_of_locally_eq'
    (fun τ => K'.inter τ ⊓ (Opens.map p.base).obj U)
    ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U)
    (fun _ => homOfLE (inf_le_inf_right _ le_top))
    (relCover_le K' p U) w₁ w₂ fun τ => congrFun hw τ

def toRelH :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (pullOpen p πZ (⊤ : V'.Opens)).obj U →ₗ[R] (relHPresheaf p πZ K' 0).obj U :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  (relAltHB p πZ K' U 0).mkQ ∘ₗ
    ((relAug p πZ K' U).codRestrict _ fun w => (ker_relAltd_zero K' p πZ U).ge ⟨w, rfl⟩)

theorem toRelH_apply (w : (pullOpen p πZ (⊤ : V'.Opens)).obj U) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    toRelH K' p πZ U w
      = Submodule.Quotient.mk ⟨relAug p πZ K' U w, (ker_relAltd_zero K' p πZ U).ge ⟨w, rfl⟩⟩ :=
  rfl

theorem toRelH_bijective : Function.Bijective (toRelH K' p πZ U) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  have hbot : relAltHB p πZ K' U 0 = ⊥ := rfl
  constructor
  · intro w₁ w₂ h
    rw [toRelH_apply, toRelH_apply] at h
    have h' := (Submodule.Quotient.eq (relAltHB p πZ K' U 0)).mp h
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at h'
    exact relAug_injective K' p πZ U (congrArg Subtype.val h')
  · intro z
    induction z using Quotient.inductionOn' with | _ x => ?_
    obtain ⟨w, hw⟩ := (ker_relAltd_zero K' p πZ U).le x.2
    exact ⟨w, congrArg Submodule.Quotient.mk (Subtype.ext hw)⟩

theorem toRelH_smul (a : Γ(Z, U)) (w : (pullOpen p πZ (⊤ : V'.Opens)).obj U) :
    toRelH K' p πZ U (a • w) = a • toRelH K' p πZ U w := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun τ => ?_))
  have hstep : ∀ (x : Γ(V', (⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U)),
      (V'.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj U)
          (le_top : K'.inter τ ≤ ⊤))).op).hom
        ((p.appLE U ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) inf_le_right).hom a * x)
      = (p.appLE U (K'.inter τ ⊓ (Opens.map p.base).obj U) inf_le_right).hom a
          * (V'.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj U)
              (le_top : K'.inter τ ≤ ⊤))).op).hom x := fun x => by
    rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  exact hstep w

theorem toRelH_res {U U' : Z.Opens} (h : U ≤ U') (w : (pullOpen p πZ (⊤ : V'.Opens)).obj U') :
    toRelH K' p πZ U ((pullOpen p πZ (⊤ : V'.Opens)).res h w)
      = (relHPresheaf p πZ K' 0).res h (toRelH K' p πZ U' w) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun τ => ?_))
  show (V'.presheaf.map _).hom ((V'.presheaf.map _).hom w)
    = (V'.presheaf.map _).hom ((V'.presheaf.map _).hom w)
  rw [res_res, res_res]

def relHEquiv :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (relHPresheaf p πZ K' 0).obj U ≃ₗ[R] (pullOpen p πZ (⊤ : V'.Opens)).obj U :=
  (LinearEquiv.ofBijective (toRelH K' p πZ U) (toRelH_bijective K' p πZ U)).symm

theorem toRelH_relHEquiv (z : (relHPresheaf p πZ K' 0).obj U) :
    toRelH K' p πZ U (relHEquiv K' p πZ U z) = z :=
  (LinearEquiv.ofBijective (toRelH K' p πZ U) (toRelH_bijective K' p πZ U)).apply_symm_apply z

theorem relHEquiv_toRelH (w : (pullOpen p πZ (⊤ : V'.Opens)).obj U) :
    relHEquiv K' p πZ U (toRelH K' p πZ U w) = w :=
  (LinearEquiv.ofBijective (toRelH K' p πZ U) (toRelH_bijective K' p πZ U)).symm_apply_apply w

def relHZeroHom :
    OModulePresheaf.Hom (relHPresheaf p πZ K' 0) (pullOpen p πZ (⊤ : V'.Opens)) where
  app U := (relHEquiv K' p πZ U).toLinearMap
  app_smul U a z := by
    obtain ⟨w, rfl⟩ := (toRelH_bijective K' p πZ U).2 z
    show relHEquiv K' p πZ U (a • toRelH K' p πZ U w) = a • relHEquiv K' p πZ U (toRelH K' p πZ U w)
    rw [← toRelH_smul, relHEquiv_toRelH, relHEquiv_toRelH]
  naturality {U U'} h := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨w, rfl⟩ := (toRelH_bijective K' p πZ U').2 z
    show relHEquiv K' p πZ U ((relHPresheaf p πZ K' 0).res h (toRelH K' p πZ U' w))
      = (pullOpen p πZ (⊤ : V'.Opens)).res h (relHEquiv K' p πZ U' (toRelH K' p πZ U' w))
    rw [← toRelH_res, relHEquiv_toRelH, relHEquiv_toRelH]

theorem relHZeroHom_app (U : Z.Opens) (z : (relHPresheaf p πZ K' 0).obj U) :
    (relHZeroHom K' p πZ).app U z = relHEquiv K' p πZ U z := rfl

theorem relAug_relHZeroHom_mk (U : Z.Opens)
    (x : letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
      ↥(LinearMap.ker (relAltd p πZ K' U 0))) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relAug p πZ K' U ((relHZeroHom K' p πZ).app U (Submodule.Quotient.mk x)) = x.1 := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  have hbot : relAltHB p πZ K' U 0 = ⊥ := rfl
  set w := (relHZeroHom K' p πZ).app U (Submodule.Quotient.mk x) with hw
  have h1 : toRelH K' p πZ U w = Submodule.Quotient.mk x := toRelH_relHEquiv K' p πZ U _
  rw [toRelH_apply] at h1
  have h2 := (Submodule.Quotient.eq (relAltHB p πZ K' U 0)).mp h1
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at h2
  exact congrArg Subtype.val h2

end AlgebraicGeometry.OModulePresheaf.Leray.RelHZero

end

end

open _root_.AlgebraicGeometry.OModulePresheaf.Leray _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero.AlgebraicGeometry.OModulePresheaf.Leray in

theorem solution
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    (K' : V'.OrderedAffineCover) :
    ∃ φ : OModulePresheaf.Hom (OModulePresheaf.Leray.relHPresheaf p πZ K' 0)
        (OModulePresheaf.Leray.pullOpen p πZ (⊤ : V'.Opens)),
      (∀ U : Z.Opens, Function.Bijective (φ.app U)) ∧
      ∀ (U : Z.Opens) (x : LinearMap.ker (OModulePresheaf.Leray.relAltd p πZ K' U 0)),
        OModulePresheaf.Leray.relAug p πZ K' U (φ.app U (Submodule.Quotient.mk x)) = x.1 :=
  ⟨RelHZero.relHZeroHom K' p πZ, fun U => (RelHZero.relHEquiv K' p πZ U).bijective,
    RelHZero.relAug_relHZeroHom_mk K' p πZ⟩

end S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero (solution)
