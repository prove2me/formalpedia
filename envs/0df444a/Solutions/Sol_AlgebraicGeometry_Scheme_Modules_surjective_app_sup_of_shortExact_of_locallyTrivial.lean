-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.surjective_app_sup_of_shortExact_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/60fae99c-f5ad-547e-b988-f640de6a595b

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_sup_of_shortExact_of_locallyTrivial
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod"
p2m_attr_erase "instance" "SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_sup_of_shortExact_of_locallyTrivial.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.pullback Scheme IsAffineOpen Scheme.Modules Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Hom Γ Hom.naturality Modules Opens PresheafOfModules Modules.exists_app_eq_of_exact_of_app_eq_zero Modules.surjective_app_of_shortExact_of_locallyTrivial"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom isSheaf exists_app_eq_of_exact_of_app_eq_zero surjective_app_of_shortExact_of_locallyTrivial"
namespace SupSurj
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (m : Γ(M, V)) :
    N.presheaf.map i.op (φ.app V m) = φ.app U (M.presheaf.map i.op m) := by
  have h := PresheafOfModules.Hom.naturality φ.val i.op
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) m
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h'
  exact h'.symm

theorem comp_app_apply {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) (m : Γ(M, U)) :
    (φ ≫ ψ).app U m = ψ.app U (φ.app U m) := rfl

theorem zero_app_apply {M N : X.Modules} (U : X.Opens) (m : Γ(M, U)) : (0 : M ⟶ N).app U m = 0 := rfl

theorem fg_app_apply (S : ShortComplex X.Modules) (U : X.Opens) (m : Γ(S.X₁, U)) :
    S.g.app U (S.f.app U m) = 0 := by
  rw [← comp_app_apply, S.zero, zero_app_apply]

noncomputable abbrev rM (M : X.Modules) {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) :=
  fun y => M.presheaf.map (homOfLE h).op y

theorem rM_rM (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    rM M h₃₂ (rM M h₂₁ y) = rM M (h₃₂.trans h₂₁) y := by
  show (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

theorem map_eq_rM (M : X.Modules) {V W : X.Opens} (i : V ⟶ W) (y : Γ(M, W)) :
    M.presheaf.map i.op y = rM M (leOfHom i) y := by
  rw [Subsingleton.elim i (homOfLE (leOfHom i))]

theorem rM_app {M N : X.Modules} (φ : M ⟶ N) {V W : X.Opens} (h : V ≤ W) (m : Γ(M, W)) :
    rM N h (φ.app W m) = φ.app V (rM M h m) :=
  app_naturality φ (homOfLE h) m

theorem rM_sub (M : X.Modules) {V W : X.Opens} (h : V ≤ W) (y z : Γ(M, W)) :
    rM M h (y - z) = rM M h y - rM M h z := map_sub _ _ _

noncomputable def F (M : X.Modules) : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

def U2 (W₀ W₁ : X.Opens) : Bool → X.Opens := fun b => cond b W₁ W₀

theorem iSup_U2 (W₀ W₁ : X.Opens) : iSup (U2 W₀ W₁) = W₀ ⊔ W₁ := by
  apply le_antisymm
  · exact iSup_le fun b => by cases b <;> simp [U2]
  · exact sup_le (le_iSup (U2 W₀ W₁) false) (le_iSup (U2 W₀ W₁) true)

theorem exists_glue (M : X.Modules) (W₀ W₁ : X.Opens) (p0 : Γ(M, W₀)) (p1 : Γ(M, W₁))
    (hp : rM M (inf_le_left : W₀ ⊓ W₁ ≤ W₀) p0 = rM M (inf_le_right : W₀ ⊓ W₁ ≤ W₁) p1) :
    ∃ s : Γ(M, W₀ ⊔ W₁), rM M (le_sup_left : W₀ ≤ W₀ ⊔ W₁) s = p0 ∧ rM M (le_sup_right : W₁ ≤ W₀ ⊔ W₁) s = p1 := by
  let sf : ∀ b : Bool, (F M).1.obj (op (U2 W₀ W₁ b)) := fun b => match b with
    | false => p0
    | true => p1
  have hcomp : TopCat.Presheaf.IsCompatible (F M).1 (U2 W₀ W₁) sf := by
    intro i j
    show M.presheaf.map _ (sf i) = M.presheaf.map _ (sf j)
    rw [map_eq_rM, map_eq_rM]
    cases i <;> cases j
    · rfl
    · exact hp
    · show rM M (inf_le_left : W₁ ⊓ W₀ ≤ W₁) p1 = rM M (inf_le_right : W₁ ⊓ W₀ ≤ W₀) p0
      have h10 : W₁ ⊓ W₀ ≤ W₀ ⊓ W₁ := le_of_eq (inf_comm _ _)
      rw [← rM_rM M inf_le_right h10, ← rM_rM M inf_le_left h10, hp]
    · rfl
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F M) (U2 W₀ W₁) (W₀ ⊔ W₁)
    (fun b => homOfLE (by cases b <;> simp [U2])) (iSup_U2 W₀ W₁).ge sf hcomp
  exact ⟨s, hs false, hs true⟩

theorem eq_of_rM_eq (M : X.Modules) (W₀ W₁ : X.Opens) (s t : Γ(M, W₀ ⊔ W₁))
    (h0 : rM M (le_sup_left : W₀ ≤ W₀ ⊔ W₁) s = rM M (le_sup_left : W₀ ≤ W₀ ⊔ W₁) t)
    (h1 : rM M (le_sup_right : W₁ ≤ W₀ ⊔ W₁) s = rM M (le_sup_right : W₁ ≤ W₀ ⊔ W₁) t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq₂ (F M) (homOfLE (le_sup_left : W₀ ≤ W₀ ⊔ W₁))
    (homOfLE (le_sup_right : W₁ ≤ W₀ ⊔ W₁)) le_rfl s t h0 h1

theorem surjective_app_sup (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj S.X₁ ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (W₀ W₁ : X.Opens) (h₀ : IsAffineOpen W₀) (h₁ : IsAffineOpen W₁)
    (hH1 : ∀ δ : Γ(S.X₁, W₀ ⊓ W₁), ∃ (a : Γ(S.X₁, W₀)) (b : Γ(S.X₁, W₁)),
      δ = S.X₁.presheaf.map (homOfLE inf_le_left).op a - S.X₁.presheaf.map (homOfLE inf_le_right).op b) :
    Function.Surjective (S.g.app (W₀ ⊔ W₁)) := by
  haveI := hS.mono_f
  intro s

  obtain ⟨m₀, hm₀⟩ := Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial S hS htriv W₀ h₀
    (rM S.X₃ le_sup_left s)
  obtain ⟨m₁, hm₁⟩ := Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial S hS htriv W₁ h₁
    (rM S.X₃ le_sup_right s)

  have hd : S.g.app (W₀ ⊓ W₁)
      (rM S.X₂ (inf_le_left : W₀ ⊓ W₁ ≤ W₀) m₀ - rM S.X₂ (inf_le_right : W₀ ⊓ W₁ ≤ W₁) m₁) = 0 := by
    rw [map_sub, ← rM_app, ← rM_app, hm₀, hm₁, rM_rM, rM_rM, sub_self]
  obtain ⟨δ, hδ⟩ := Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS.exact (W₀ ⊓ W₁) _ hd
  obtain ⟨a, b, hab⟩ := hH1 δ
  change δ = rM S.X₁ inf_le_left a - rM S.X₁ inf_le_right b at hab

  have hagree : rM S.X₂ (inf_le_left : W₀ ⊓ W₁ ≤ W₀) (m₀ - S.f.app W₀ a)
      = rM S.X₂ (inf_le_right : W₀ ⊓ W₁ ≤ W₁) (m₁ - S.f.app W₁ b) := by
    rw [rM_sub, rM_sub, rM_app, rM_app]
    have key : S.f.app (W₀ ⊓ W₁) (rM S.X₁ inf_le_left a) - S.f.app (W₀ ⊓ W₁) (rM S.X₁ inf_le_right b)
        = rM S.X₂ inf_le_left m₀ - rM S.X₂ inf_le_right m₁ := by
      rw [← map_sub, ← hab, hδ]
    rw [sub_eq_sub_iff_sub_eq_sub, ← key]
  obtain ⟨m, hm0, hm1⟩ := exists_glue S.X₂ W₀ W₁ _ _ hagree
  refine ⟨m, eq_of_rM_eq S.X₃ W₀ W₁ _ _ ?_ ?_⟩
  · rw [rM_app, hm0, map_sub, hm₀, fg_app_apply, sub_zero]
  · rw [rM_app, hm1, map_sub, hm₁, fg_app_apply, sub_zero]

end AlgebraicGeometry.Scheme.Modules.SupSurj

theorem solution
    {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj S.X₁ ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (W₀ W₁ : X.Opens) (h₀ : IsAffineOpen W₀) (h₁ : IsAffineOpen W₁)
    (hH1 : ∀ δ : Γ(S.X₁, W₀ ⊓ W₁), ∃ (a : Γ(S.X₁, W₀)) (b : Γ(S.X₁, W₁)),
      δ = S.X₁.presheaf.map (homOfLE inf_le_left).op a - S.X₁.presheaf.map (homOfLE inf_le_right).op b) :
    Function.Surjective (S.g.app (W₀ ⊔ W₁)) :=
  AlgebraicGeometry.Scheme.Modules.SupSurj.surjective_app_sup S hS htriv W₀ W₁ h₀ h₁ hH1

end S_AlgebraicGeometry_Scheme_Modules_surjective_app_sup_of_shortExact_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_sup_of_shortExact_of_locallyTrivial (solution)
