-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_projPresentation_isPullback_toProj_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8f3e9fd0-80c1-5de5-a832-f52e390b1399

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isPullback_toProj_of_faithfullyFlat
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (L' : X'.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ L')
    {M : ℕ} (𝔔 : Scheme.Modules.ProjPresentation L' f' M) :
    ∃ (N : ℕ) (𝔓 : Scheme.Modules.ProjPresentation L f N) (𝔓' : Scheme.Modules.ProjPresentation L' f' N),
      IsPullback c 𝔓'.toProj 𝔓.toProj (ProjSpace.map S S' N) ∧
      ∀ j : Fin (M + 1), ∃ a : Fin (N + 1) → S',
        𝔔.σ j = ∑ l, ((f'.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S')).inv.hom (a l))) • 𝔓'.σ l := by
  classical

  letI iS : Algebra S Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom.toAlgebra
  letI iSL : Module S Γ(L, ⊤) := Module.compHom _ (algebraMap S Γ(X, ⊤))
  letI iS' : Algebra S' Γ(X', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom.toAlgebra
  letI iS'L : Module S' Γ((Scheme.Modules.pullback c).obj L, ⊤) := Module.compHom _ (algebraMap S' Γ(X', ⊤))

  obtain ⟨𝔔₀, hQ₀t, hQ₀σ⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso 𝔔 e.symm

  obtain ⟨β, hβ⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat S' f f' c hc L hL

  have hdec : ∀ j : Fin (M + 1), ∃ T : Finset (S' × Γ(L, ⊤)), β.symm (𝔔₀.σ j) = ∑ i ∈ T, i.1 ⊗ₜ[S] i.2 :=
    fun j => TensorProduct.exists_finset _
  choose T hT using hdec

  let N : ℕ := Fintype.card (Σ j : Fin (M + 1), ↥(T j))
  have hcard : Fintype.card (Option (Σ j : Fin (M + 1), ↥(T j))) = N + 1 := by rw [Fintype.card_option]
  let eI : Option (Σ j : Fin (M + 1), ↥(T j)) ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  let σfun : Option (Σ j : Fin (M + 1), ↥(T j)) → Γ(L, ⊤) := fun o => match o with
    | none => 0
    | some x => x.2.1.2
  let coef : Fin (M + 1) → Option (Σ j : Fin (M + 1), ↥(T j)) → S' := fun j o => match o with
    | none => 0
    | some x => if x.1 = j then x.2.1.1 else 0
  let σ : Fin (N + 1) → Γ(L, ⊤) := fun l => σfun (eI.symm l)
  let a : Fin (M + 1) → Fin (N + 1) → S' := fun j l => coef j (eI.symm l)

  have key : ∀ (Rs V : Type u) [Semiring Rs] [AddCommMonoid V] [Module Rs V] (φ : S' → Rs) (hφ : φ 0 = 0)
      (ψ : Γ(L, ⊤) → V) (j : Fin (M + 1)),
      ∑ l : Fin (N + 1), φ (a j l) • ψ (σ l) = ∑ i ∈ T j, φ i.1 • ψ i.2 := by
    intro Rs V _ _ _ φ hφ ψ j
    have h1 : ∑ l : Fin (N + 1), φ (a j l) • ψ (σ l) = ∑ o : Option (Σ j : Fin (M + 1), ↥(T j)), φ (coef j o) • ψ (σfun o) := by
      rw [← Equiv.sum_comp eI.symm]
    rw [h1, Fintype.sum_option]
    have h0 : φ (coef j none) • ψ (σfun none) = 0 := by
      show φ 0 • ψ 0 = 0
      rw [hφ, zero_smul]
    rw [h0, zero_add]
    have h2 : ∀ x : (Σ j : Fin (M + 1), ↥(T j)), φ (coef j (some x)) • ψ (σfun (some x)) = if x.1 = j then φ x.2.1.1 • ψ x.2.1.2 else 0 := by
      intro x
      show φ (if x.1 = j then x.2.1.1 else 0) • ψ x.2.1.2 = _
      split_ifs
      · rfl
      · rw [hφ, zero_smul]
    simp_rw [h2]
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Finset.sum_coe_sort (T j) (fun i => φ i.1 • ψ i.2)

  let σ' : Fin (N + 1) → Γ((Scheme.Modules.pullback c).obj L, ⊤) := fun l => β ((1 : S') ⊗ₜ[S] σ l)
  have hσ' : ∀ l, σ' l = (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app L).app ⊤) (σ l) := fun l => hβ (σ l)
  have hρ : ∀ j : Fin (M + 1), 𝔔₀.σ j = ∑ l, (algebraMap S' (X'.presheaf.obj (Opposite.op ⊤)) (a j l)) • σ' l := by
    intro j
    rw [key _ _ (algebraMap S' (X'.presheaf.obj (Opposite.op ⊤))) (map_zero _) (fun m => β ((1 : S') ⊗ₜ[S] m)) j]
    have h1 : 𝔔₀.σ j = β (β.symm (𝔔₀.σ j)) := (β.apply_symm_apply _).symm
    rw [h1, hT j, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 : i.1 ⊗ₜ[S] i.2 = i.1 • ((1 : S') ⊗ₜ[S] i.2) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h2, LinearEquiv.map_smul]
    rfl

  let U' : Fin (M + 1) → X'.Opens := fun j =>
    𝔔₀.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) S') (MvPolynomial.X j)
  have hU' : iSup U' = ⊤ := by
    have h : ⨆ i : Fin (M + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) S')
        (MvPolynomial.X i) = ⊤ :=
      Proj.iSup_basicOpen_eq_top _ (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X S' M)
    refine le_antisymm le_top fun y _ => ?_
    have hy : 𝔔₀.toProj.base y ∈ (⊤ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) S')).Opens) := trivial
    rw [← h] at hy
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

  haveI : Surjective c := by
    have hs : Surjective (Spec.map (CommRingCat.ofHom (algebraMap S S'))) :=
      ⟨by rw [Spec.map_base]; exact PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
    exact MorphismProperty.of_isPullback (P := @Surjective) hc.flip hs
  obtain ⟨U, hU, hframe⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
      c L hL σ σ' hσ' 𝔔₀.σ U' hU' (fun j V' hV' => 𝔔₀.frame j V' hV') (fun j => ⟨fun l => algebraMap S' (X'.presheaf.obj (Opposite.op ⊤)) (a j l), hρ j⟩)

  obtain ⟨𝔓, h𝔓σ, -⟩ := AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top f L N σ U hU hframe
  obtain ⟨𝔓'₀, hσ'₀, -, hsq₀⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback hc 𝔓
  obtain ⟨𝔓', htp, hσ'e⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso 𝔓'₀ e
  refine ⟨N, 𝔓, 𝔓', by rw [htp]; exact hsq₀, fun j => ⟨a j, ?_⟩⟩

  have hQσ : 𝔔.σ j = (e.hom.app ⊤) (𝔔₀.σ j) := by
    rw [hQ₀σ j]
    change 𝔔.σ j = ((e.symm.hom ≫ e.hom).app ⊤) (𝔔.σ j)
    rw [Iso.symm_hom, Iso.inv_hom_id]
    rfl
  have hPσ : ∀ l, 𝔓'.σ l = (e.hom.app ⊤) (σ' l) := by
    intro l; rw [hσ'e l, hσ'₀ l, h𝔓σ, hσ' l]
  rw [hQσ, hρ j, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Scheme.Modules.Hom.app_smul, hPσ l]
  congr 1
  show ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom (a j l) = (f'.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S')).inv.hom (a j l))
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isPullback_toProj_of_faithfullyFlat
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isPullback_toProj_of_faithfullyFlat (solution)
