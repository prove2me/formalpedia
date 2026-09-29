-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.thetaGroup.ker_pt_le_center_and_commutatorElement_mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/edc18428-ce5a-56b0-9bd0-8a810175f6fa

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_RiemannForm_existsUnique_isConstScalar
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isConstScalar_pullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_ker_pt_le_center_and_commutatorElement_mem_ker
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

open scoped commutatorElement

namespace ThetaT1

set_option backward.isDefEq.respectTransparency false

section units
universe u
variable {X Y : Scheme.{u}}

theorem map_pullbackId_inv_comp (f : X ⟶ Y) (M : Y.Modules)
    (p : (Scheme.Modules.pullback f).obj M = (Scheme.Modules.pullback (f ≫ 𝟙 Y)).obj M) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).inv.app M) ≫
      (Scheme.Modules.pullbackComp f (𝟙 Y)).hom.app M = eqToHom p := by
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality f) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app, eqToHom_app] at h
  erw [Category.comp_id ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).hom.app M))] at h
  rw [← cancel_mono ((Scheme.Modules.pullbackComp f (𝟙 Y)).inv.app M ≫
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).hom.app M))]
  rw [Category.assoc, Iso.hom_inv_id_app_assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, h, eqToHom_trans, eqToHom_refl]

theorem pullbackId_inv_app_comp (f : X ⟶ Y) (M : Y.Modules)
    (q : (Scheme.Modules.pullback f).obj M = (Scheme.Modules.pullback (𝟙 X ≫ f)).obj M) :
    (Scheme.Modules.pullbackId X).inv.app ((Scheme.Modules.pullback f).obj M) ≫
      (Scheme.Modules.pullbackComp (𝟙 X) f).hom.app M = eqToHom q := by
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality f) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, eqToHom_app] at h
  erw [Category.comp_id ((Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback f).obj M))] at h
  rw [← cancel_mono ((Scheme.Modules.pullbackComp (𝟙 X) f).inv.app M ≫
    (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback f).obj M))]
  rw [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app, h, eqToHom_trans, eqToHom_refl]

end units

section core
variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

theorem fib_mapComp_inv_app (a b : A ⟶ A) (M : A.Modules) :
    (Scheme.Modules.fibration.mapComp b.op.toLoc a.op.toLoc).inv.toNatTrans.app M =
      (Scheme.Modules.pullbackComp a b).hom.app M := by
  simp [Scheme.Modules.fibration, Scheme.Modules.pseudofunctor, Pseudofunctor.comp, Bicategory.Adj.forget₁,
    LocallyDiscrete.mkPseudofunctor]
  rfl

theorem comp_eq_comp_of_isConstScalar {M N : A.Modules} (σ : M ⟶ M) (τ : N ⟶ N) (φ : M ⟶ N) (c : k)
    (hσ : IsConstScalar f σ c) (hτ : IsConstScalar f τ c) : σ ≫ φ = φ ≫ τ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, hσ U s, hτ U, Scheme.Modules.Hom.app_smul]

theorem comm_of_base_eq_id (M : A.Modules) (h₁ h₂ : modulePair (A := A) M ⟶ modulePair (A := A) M)
    (hB : h₁.base = 𝟙 A) (c : k)
    (hu : IsConstScalar f
      (h₁.fiber ≫ (Scheme.Modules.pullbackCongr hB).hom.app M ≫ (Scheme.Modules.pullbackId A).hom.app M) c)
    (h2f : h₂.base ≫ f = f) :
    h₂ ≫ h₁ = h₁ ≫ h₂ := by
  obtain ⟨B, φ⟩ := h₁
  obtain ⟨T, ψ⟩ := h₂
  change B = 𝟙 A at hB
  subst hB
  change T ≫ f = f at h2f

  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app] at hu
  erw [Category.id_comp] at hu
  set u : M ⟶ M := φ ≫ (Scheme.Modules.pullbackId A).hom.app M with hu_def
  have hφ : φ = u ≫ (Scheme.Modules.pullbackId A).inv.app M := by
    rw [hu_def, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id φ).symm
  have hcomm : ψ ≫ (Scheme.Modules.pullback T).map u = u ≫ ψ :=
    (comp_eq_comp_of_isConstScalar f u ((Scheme.Modules.pullback T).map u) ψ c hu
      (AlgebraicGeometry.RiemannForm.isConstScalar_pullback_map k f T h2f hu)).symm
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp
  · simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber, Pseudofunctor.CoGrothendieck.categoryStruct_comp_base,
      modulePair_fiber, Scheme.Modules.fibration_map_toFunctor, fib_mapComp_inv_app]
    change ψ ≫ (Scheme.Modules.pullback T).map φ ≫ (Scheme.Modules.pullbackComp T (𝟙 A)).hom.app M =
      (φ ≫ (Scheme.Modules.pullback (𝟙 A)).map ψ ≫ (Scheme.Modules.pullbackComp (𝟙 A) T).hom.app M) ≫ eqToHom _
    rw [hφ, CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    rw [map_pullbackId_inv_comp T M (by simp), reassoc_of% hcomm]
    have hnat : (Scheme.Modules.pullbackId A).inv.app M ≫ (Scheme.Modules.pullback (𝟙 A)).map ψ =
        ψ ≫ (Scheme.Modules.pullbackId A).inv.app ((Scheme.Modules.pullback T).obj M) := by
      have hn := (Scheme.Modules.pullbackId A).inv.naturality ψ
      rw [CategoryTheory.Functor.id_map] at hn
      exact hn.symm
    rw [reassoc_of% hnat, reassoc_of% (pullbackId_inv_app_comp T M (by simp)), eqToHom_trans]

end core

theorem main
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    (thetaGroup.pt f L hc M).ker ≤ Subgroup.center (thetaGroup f L hc M) ∧
    ∀ g h : thetaGroup f L hc M, ⁅g, h⁆ ∈ (thetaGroup.pt f L hc M).ker := by
  refine ⟨fun z hz => ?_, fun g h => ?_⟩
  · rw [MonoidHom.mem_ker] at hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hB := thetaGroup.base_eq_id_of_pt_eq_one f L hc M z hz
    obtain ⟨c, hcσ, -⟩ := AlgebraicGeometry.RiemannForm.existsUnique_isConstScalar k f hA M hM (thetaGroup.unitReading M hB)
    have hgf : g.1.1.hom.base ≫ f = f := by
      rw [thetaGroup.base_eq f L hc M g]; exact translation_over f L _
    have key := comm_of_base_eq_id f M z.1.1.hom g.1.1.hom hB c hcσ hgf
    apply Subtype.ext
    change g.1 * z.1 = z.1 * g.1
    apply Prod.ext
    · change g.1.1 * z.1.1 = z.1.1 * g.1.1
      rw [Aut.Aut_mul_def, Aut.Aut_mul_def]
      exact Iso.ext key.symm
    · exact mul_comm _ _
  · rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _

end ThetaT1

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    (thetaGroup.pt f L hc M).ker ≤ Subgroup.center (thetaGroup f L hc M) ∧
    ∀ g h : thetaGroup f L hc M, ⁅g, h⁆ ∈ (thetaGroup.pt f L hc M).ker :=
  ThetaT1.main k f L hc hA M hM

end S_AlgebraicGeometry_RiemannForm_thetaGroup_ker_pt_le_center_and_commutatorElement_mem_ker
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_ker_pt_le_center_and_commutatorElement_mem_ker (solution)
