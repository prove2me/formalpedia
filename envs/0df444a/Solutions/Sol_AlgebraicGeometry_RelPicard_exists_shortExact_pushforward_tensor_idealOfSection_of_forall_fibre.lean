-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_shortExact_pushforward_tensor_idealOfSection_of_forall_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/47de18d3-1faf-5c41-9efd-6b0ef92db71e

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_surjective_app_sup_of_shortExact_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_forall_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_sectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_shortExact_pushforward_tensor_idealOfSection_of_forall_fibre
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_shortExact_pushforward_tensor_idealOfSection_of_forall_fibre.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_shortExact_pushforward_tensor_idealOfSection_of_forall_fibre.AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve Opposite TopologicalSpace"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pushforwardCongr Surjective SmoothOfRelativeDimension Scheme.Modules.pushforward Scheme.Modules.pushforwardComp IsProper Scheme.Modules.pullback IsClosedImmersion.of_comp Scheme.Hom Scheme.Hom.preimage_inf Scheme.Modules.pushforwardId Scheme.Hom.image_top_eq_opensRange LocallyOfFiniteType Spec Scheme IsOpenImmersion IsClosedImmersion IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackPushforwardAdjunction IsAffineOpen Scheme.Modules Scheme.Hom.mem_opensRange Scheme.Pullback.exists_preimage_pullback Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom SmoothProperCurve.FiniteMapData Scheme.Modules.shortExact_map_pushforward_of_forall_exists_surjective_app Scheme.Modules.surjective_app_sup_of_shortExact_of_locallyTrivial Scheme.TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_forall_field Scheme.Modules.exists_shortExact_ker_module_tensor_of_isClosedImmersion Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom Scheme.TwoAffineOpenCover.finiteType_algebraOfHom Scheme.Modules.exists_iso_pullback_of_isPullback Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.Modules.bijective_unit_app_of_le_opensRange"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pushforwardCongr ringCatSheaf Modules.pushforward Modules.pushforwardComp Modules.pullback Hom mk Γ Hom.preimage_inf Modules.pushforwardId Hom.image_top_eq_opensRange Hom.naturality Modules.pullbackPushforwardAdjunction isBasis_affineOpens Modules Opens Hom.mem_opensRange Pullback.exists_preimage_pullback PresheafOfModules Modules.IsInvertible TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.algebraOfHom Modules.shortExact_map_pushforward_of_forall_exists_surjective_app Modules.surjective_app_sup_of_shortExact_of_locallyTrivial TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_forall_field Modules.exists_shortExact_ker_module_tensor_of_isClosedImmersion Modules.isLocallyFreeOfRank_one_iff_isInvertible Hom.isInvertible_ker_of_comp_eq_id TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom TwoAffineOpenCover.finiteType_algebraOfHom Modules.exists_iso_pullback_of_isPullback TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Modules.bijective_unit_app_of_le_opensRange"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforwardCongr pushforward pushforwardComp pullback presheaf pushforwardId Hom pullbackPushforwardAdjunction IsInvertible tensor shortExact_map_pushforward_of_forall_exists_surjective_app surjective_app_sup_of_shortExact_of_locallyTrivial exists_shortExact_ker_module_tensor_of_isClosedImmersion isLocallyFreeOfRank_one_iff_isInvertible exists_iso_pullback_of_isPullback bijective_unit_app_of_le_opensRange"
namespace PointSES
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

theorem id_app_apply {M : X.Modules} (U : X.Opens) (m : Γ(M, U)) : (𝟙 M : M ⟶ M).app U m = m := rfl

noncomputable abbrev rM (M : X.Modules) {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) :=
  fun y => M.presheaf.map (homOfLE h).op y

theorem rM_rM (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    rM M h₃₂ (rM M h₂₁ y) = rM M (h₃₂.trans h₂₁) y := by
  show (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

theorem rM_app {M N : X.Modules} (φ : M ⟶ N) {V W : X.Opens} (h : V ≤ W) (m : Γ(M, W)) :
    rM N h (φ.app W m) = φ.app V (rM M h m) :=
  app_naturality φ (homOfLE h) m

theorem rM_sub (M : X.Modules) {V W : X.Opens} (h : V ≤ W) (y z : Γ(M, W)) :
    rM M h (y - z) = rM M h y - rM M h z := map_sub _ _ _

theorem rM_neg (M : X.Modules) {V W : X.Opens} (h : V ≤ W) (y : Γ(M, W)) :
    rM M h (-y) = -rM M h y := map_neg _ _

theorem rM_refl (M : X.Modules) (V : X.Opens) (y : Γ(M, V)) : rM M (le_refl V) y = y := by
  change (M.presheaf.map (homOfLE (le_refl V)).op) y = y
  have hid : M.presheaf.map (homOfLE (le_refl V)).op = 𝟙 _ := by
    rw [show (homOfLE (le_refl V)).op = 𝟙 (op V) from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  rw [hid]
  rfl

theorem rM_injective_of_eq (M : X.Modules) {V W : X.Opens} (h : V = W) : Function.Injective (rM M h.le) := by
  intro y z hyz
  have := congrArg (rM M h.ge) hyz
  rwa [rM_rM, rM_rM, rM_refl, rM_refl] at this

theorem hH1_of_iso {M N : X.Modules} (e : M ≅ N) (W₀ W₁ : X.Opens)
    (h : ∀ δ : Γ(N, W₀ ⊓ W₁), ∃ (a : Γ(N, W₀)) (b : Γ(N, W₁)),
      δ = rM N inf_le_left a - rM N inf_le_right b) :
    ∀ δ : Γ(M, W₀ ⊓ W₁), ∃ (a : Γ(M, W₀)) (b : Γ(M, W₁)),
      δ = M.presheaf.map (homOfLE inf_le_left).op a - M.presheaf.map (homOfLE inf_le_right).op b := by
  intro δ
  obtain ⟨a, b, hab⟩ := h (e.hom.app _ δ)
  refine ⟨e.inv.app _ a, e.inv.app _ b, ?_⟩
  have hδ : δ = e.inv.app _ (e.hom.app _ δ) := by
    rw [← comp_app_apply, e.hom_inv_id, id_app_apply]
  change δ = rM M inf_le_left (e.inv.app _ a) - rM M inf_le_right (e.inv.app _ b)
  rw [hδ, hab, map_sub, rM_app, rM_app]

section OpenImm

variable {X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j] (N : X.Modules)

noncomputable abbrev η : N ⟶ (Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj N) :=
  (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N

noncomputable abbrev pull (V : X.Opens) (m : Γ(N, V)) :
    Γ((Scheme.Modules.pullback j).obj N, j ⁻¹ᵁ V) :=
  (η j N).app V m

theorem pull_sub (V : X.Opens) (m m' : Γ(N, V)) : pull j N V (m - m') = pull j N V m - pull j N V m' :=
  map_sub _ _ _

theorem pull_neg (V : X.Opens) (m : Γ(N, V)) : pull j N V (-m) = -pull j N V m := map_neg _ _

theorem map_pull {U V : X.Opens} (h : U ≤ V) (m : Γ(N, V)) :
    rM ((Scheme.Modules.pullback j).obj N) (show j ⁻¹ᵁ U ≤ j ⁻¹ᵁ V from fun _ hx => h hx) (pull j N V m)
      = pull j N U (rM N h m) := by
  rw [pull, pull, ← app_naturality (η j N) (homOfLE h) m]
  rfl

theorem pull_bijective (V : X.Opens) (hV : V ≤ j.opensRange) : Function.Bijective (pull j N V) :=
  Scheme.Modules.bijective_unit_app_of_le_opensRange j N V hV

theorem hH1_of_pullback (𝒲 : X'.TwoAffineOpenCover) {A : Type u} [CommRing A] (x' : X' ⟶ Spec (.of A))
    (hH1 : Subsingleton (𝒲.sectionsOf x' ((Scheme.Modules.pullback j).obj N)).H1) :
    ∀ δ : Γ(N, j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1), ∃ (a : Γ(N, j ''ᵁ 𝒲.U0)) (b : Γ(N, j ''ᵁ 𝒲.U1)),
      δ = rM N inf_le_left a - rM N inf_le_right b := by
  have h0 : j ⁻¹ᵁ (j ''ᵁ 𝒲.U0) = 𝒲.U0 := j.preimage_image_eq _
  have h1 : j ⁻¹ᵁ (j ''ᵁ 𝒲.U1) = 𝒲.U1 := j.preimage_image_eq _
  have h01 : j ⁻¹ᵁ (j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1) = 𝒲.U0 ⊓ 𝒲.U1 := by
    rw [Scheme.Hom.preimage_inf, h0, h1]
  have hW₀ : j ''ᵁ 𝒲.U0 ≤ j.opensRange := j.image_le_opensRange _
  have hW₁ : j ''ᵁ 𝒲.U1 ≤ j.opensRange := j.image_le_opensRange _
  intro δ

  have hz : (Submodule.Quotient.mk (rM ((Scheme.Modules.pullback j).obj N) h01.ge (pull j N _ δ)) :
      (𝒲.sectionsOf x' ((Scheme.Modules.pullback j).obj N)).H1) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hz
  obtain ⟨⟨s0, s1⟩, hs⟩ := hz
  rw [TwoChartCech.Sections.cechDiff_apply] at hs
  change rM ((Scheme.Modules.pullback j).obj N) inf_le_right s1 - rM ((Scheme.Modules.pullback j).obj N) inf_le_left s0
    = rM ((Scheme.Modules.pullback j).obj N) h01.ge (pull j N _ δ) at hs

  obtain ⟨a, ha⟩ := (pull_bijective j N _ hW₀).2 (rM ((Scheme.Modules.pullback j).obj N) h0.le s0)
  obtain ⟨b, hb⟩ := (pull_bijective j N _ hW₁).2 (rM ((Scheme.Modules.pullback j).obj N) h1.le s1)
  have hpa : pull j N _ (rM N (inf_le_left : j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1 ≤ j ''ᵁ 𝒲.U0) a)
      = rM ((Scheme.Modules.pullback j).obj N)
          ((show j ⁻¹ᵁ (j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1) ≤ j ⁻¹ᵁ (j ''ᵁ 𝒲.U0) from fun _ hx => hx.1).trans h0.le) s0 := by
    rw [← map_pull, ha, rM_rM]
  have hpb : pull j N _ (rM N (inf_le_right : j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1 ≤ j ''ᵁ 𝒲.U1) b)
      = rM ((Scheme.Modules.pullback j).obj N)
          ((show j ⁻¹ᵁ (j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1) ≤ j ⁻¹ᵁ (j ''ᵁ 𝒲.U1) from fun _ hx => hx.2).trans h1.le) s1 := by
    rw [← map_pull, hb, rM_rM]
  refine ⟨-a, -b, ?_⟩
  apply (pull_bijective j N _ (inf_le_left.trans hW₀)).1
  apply rM_injective_of_eq ((Scheme.Modules.pullback j).obj N) h01.symm
  rw [rM_neg N, rM_neg N, pull_sub, pull_neg, pull_neg, hpa, hpb, rM_sub, rM_neg, rM_neg, rM_rM, rM_rM]
  rw [← hs]
  abel

end OpenImm

theorem opensRange_eq_preimage {X T X' W' : Scheme.{u}} (π : X ⟶ T) (π' : X' ⟶ W') (g' : X' ⟶ X) (j : W' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion g'] (hcart : IsPullback g' π' π j) :
    g'.opensRange = π ⁻¹ᵁ j.opensRange := by
  apply le_antisymm
  · intro x hx
    obtain ⟨x', rfl⟩ := Scheme.Hom.mem_opensRange.mp hx
    show π.base (g'.base x') ∈ j.opensRange
    rw [Scheme.Hom.mem_opensRange]
    refine ⟨π'.base x', ?_⟩
    change (π' ≫ j).base x' = (g' ≫ π).base x'
    rw [hcart.w]
  · intro x hx
    change π.base x ∈ j.opensRange at hx
    obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hx
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine Scheme.Hom.mem_opensRange.mpr ⟨hcart.isoPullback.inv.base z, ?_⟩
    change (hcart.isoPullback.inv ≫ g').base z = x
    rw [hcart.isoPullback_inv_fst]
    exact hz

end AlgebraicGeometry.Scheme.Modules.PointSES

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pushforwardCongr Surjective SmoothOfRelativeDimension Scheme.Modules.pushforward Scheme.Modules.pushforwardComp IsProper Scheme.Modules.pullback IsClosedImmersion.of_comp Scheme.Hom Scheme.Hom.preimage_inf Scheme.Modules.pushforwardId Scheme.Hom.image_top_eq_opensRange LocallyOfFiniteType Spec Scheme IsOpenImmersion IsClosedImmersion IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackPushforwardAdjunction IsAffineOpen Scheme.Modules Scheme.Hom.mem_opensRange Scheme.Pullback.exists_preimage_pullback Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom SmoothProperCurve.FiniteMapData Scheme.Modules.shortExact_map_pushforward_of_forall_exists_surjective_app Scheme.Modules.surjective_app_sup_of_shortExact_of_locallyTrivial Scheme.TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_forall_field Scheme.Modules.exists_shortExact_ker_module_tensor_of_isClosedImmersion Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom Scheme.TwoAffineOpenCover.finiteType_algebraOfHom Scheme.Modules.exists_iso_pullback_of_isPullback Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.Modules.bijective_unit_app_of_le_opensRange"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "fibreAt fibreModule"
namespace PointSES
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

open AlgebraicGeometry.Scheme.Modules.PointSES

theorem surjective_app_preimage
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : (pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L)).H1)
    (S₀ : ShortComplex (pullback c t).Modules) (hS₀ : S₀.ShortExact) (e₁ : S₀.X₁ ≅ L)
    (W : T.Opens) (hW : IsAffineOpen W) :
    Function.Surjective (S₀.g.app ((pullback.snd c t) ⁻¹ᵁ W)) := by

  have htriv₁ : ∀ x : ↥(pullback c t), ∃ V : (pullback c t).Opens, x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj S₀.X₁ ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) := by
    intro x
    obtain ⟨V, hx, ⟨e⟩⟩ := hL.exists_trivialization x
    exact ⟨V, hx, ⟨(Scheme.Modules.pullback V.ι).mapIso e₁ ≪≫ e⟩⟩

  letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
  haveI : Algebra.FiniteType R Γ(T, W) := Scheme.TwoAffineOpenCover.finiteType_algebraOfHom t W hW
  haveI : IsNoetherianRing Γ(T, W) := Algebra.FiniteType.isNoetherianRing R _
  obtain ⟨g', hcart, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom c t W hW
  haveI : IsOpenImmersion g' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hcart.flip inferInstance

  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨𝔉A, -, -, -, -⟩ := 𝔉.exists_baseChange Γ(T, W)

  have hG : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback g').obj L) := hL.pullback g'
  have hfin := 𝔉A.finite_H0_H1_sectionsOf ((Scheme.Modules.pullback g').obj L) hG.exists_trivialization
  have hH1 : Subsingleton ((𝔉A.twoAffineOpenCover.sectionsOf
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)))
      ((Scheme.Modules.pullback g').obj L)).H1) := by
    refine Scheme.TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_forall_field
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) 𝔉A.twoAffineOpenCover _
      hG.exists_trivialization hfin.2 ?_
    intro K _ _

    obtain ⟨φ, hφ, -, hmod⟩ := Scheme.Modules.exists_iso_pullback_of_isPullback (pullback.snd c t)
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) g' hW.fromSpec hcart
      (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K)
    obtain ⟨𝒱, -, -, -, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (fibreAt c t (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec))
      (fibreAt c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K))
      φ hφ
      (𝔉A.twoAffineOpenCover.pullback (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) K)
      (fibreModule c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K)
        ((Scheme.Modules.pullback g').obj L))
      (fibreModule c t (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec) L) (hmod L).some
    haveI := hfib K (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec) 𝒱
    exact e1.symm.toEquiv.subsingleton

  have hH1X := hH1_of_pullback g' L 𝔉A.twoAffineOpenCover _ hH1
  have hH1S := hH1_of_iso e₁ _ _ hH1X

  have hsup : g' ''ᵁ 𝔉A.twoAffineOpenCover.U0 ⊔ g' ''ᵁ 𝔉A.twoAffineOpenCover.U1 = (pullback.snd c t) ⁻¹ᵁ W := by
    have h1 : g' ''ᵁ 𝔉A.twoAffineOpenCover.U0 ⊔ g' ''ᵁ 𝔉A.twoAffineOpenCover.U1
        = g' ''ᵁ (𝔉A.twoAffineOpenCover.U0 ⊔ 𝔉A.twoAffineOpenCover.U1) := by
      ext1
      simp [Set.image_union]
    rw [h1, 𝔉A.twoAffineOpenCover.sup_eq_top, Scheme.Hom.image_top_eq_opensRange,
      opensRange_eq_preimage _ _ _ _ hcart, hW.opensRange_fromSpec]
  rw [← hsup]
  exact Scheme.Modules.surjective_app_sup_of_shortExact_of_locallyTrivial S₀ hS₀ htriv₁ _ _
    (𝔉A.twoAffineOpenCover.isAffineOpen_U0.image_of_isOpenImmersion g')
    (𝔉A.twoAffineOpenCover.isAffineOpen_U1.image_of_isOpenImmersion g') hH1S

theorem main
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (p : T ⟶ pullback c t) (hp : p ≫ pullback.snd c t = 𝟙 T)
    (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (F ⊗ p.ker.module))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (F ⊗ p.ker.module))).H0 = n) :
    ∃ S : ShortComplex T.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ (Scheme.Modules.pushforward (pullback.snd c t)).obj (F ⊗ p.ker.module)) ∧
      Nonempty (S.X₂ ≅ (Scheme.Modules.pushforward (pullback.snd c t)).obj F) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pullback p).obj F) := by

  haveI : IsSeparated (pullback.snd c t) := inferInstance
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c t inferInstance
  haveI : IsClosedImmersion p := by
    have : IsClosedImmersion (p ≫ pullback.snd c t) := by rw [hp]; infer_instance
    exact IsClosedImmersion.of_comp p (pullback.snd c t)
  have hI : Scheme.Modules.IsInvertible p.ker.module :=
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp).isInvertible_module
  have hFI : Scheme.Modules.IsInvertible (F ⊗ p.ker.module) := hF.tensor hI

  obtain ⟨S₀, hS₀, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := Scheme.Modules.exists_shortExact_ker_module_tensor_of_isClosedImmersion p F
    ((Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible F).mpr hF)
  let e₁' : S₀.X₁ ≅ F ⊗ p.ker.module := e₁ ≪≫ β_ _ _

  refine ⟨S₀.map (Scheme.Modules.pushforward (pullback.snd c t)), ?_,
    ⟨(Scheme.Modules.pushforward (pullback.snd c t)).mapIso e₁'⟩,
    ⟨(Scheme.Modules.pushforward (pullback.snd c t)).mapIso e₂⟩,
    ⟨(Scheme.Modules.pushforward (pullback.snd c t)).mapIso e₃ ≪≫
      (Scheme.Modules.pushforwardComp p (pullback.snd c t)).app _ ≪≫
      (Scheme.Modules.pushforwardCongr hp).app _ ≪≫ (Scheme.Modules.pushforwardId T).app _⟩⟩
  refine Scheme.Modules.shortExact_map_pushforward_of_forall_exists_surjective_app _ S₀ hS₀ ?_
  intro U y hyU
  obtain ⟨W, hW, hyW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens hyU
  exact ⟨W, hyW, hWU, surjective_app_preimage R c ε h𝔉 t (F ⊗ p.ker.module) hFI
    (fun k _ s 𝒲 => (hfib k s 𝒲).1) S₀ hS₀ e₁' W hW⟩

end AlgebraicGeometry.RelPicard.PointSES

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (p : T ⟶ pullback c t) (hp : p ≫ pullback.snd c t = 𝟙 T)
    (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (F ⊗ p.ker.module))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (F ⊗ p.ker.module))).H0 = n) :
    ∃ S : ShortComplex T.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ (Scheme.Modules.pushforward (pullback.snd c t)).obj (F ⊗ p.ker.module)) ∧
      Nonempty (S.X₂ ≅ (Scheme.Modules.pushforward (pullback.snd c t)).obj F) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pullback p).obj F) :=
  AlgebraicGeometry.RelPicard.PointSES.main R c ε h𝔉 t p hp F hF n hfib

end

end S_AlgebraicGeometry_RelPicard_exists_shortExact_pushforward_tensor_idealOfSection_of_forall_fibre
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_shortExact_pushforward_tensor_idealOfSection_of_forall_fibre (solution)
