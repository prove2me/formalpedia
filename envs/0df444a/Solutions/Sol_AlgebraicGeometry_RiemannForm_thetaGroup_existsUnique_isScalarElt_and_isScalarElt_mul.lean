-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.thetaGroup.existsUnique_isScalarElt_and_isScalarElt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/00821396-85da-53ef-8710-85e3c02b2925

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_RiemannForm_existsUnique_isConstScalar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_existsUnique_isScalarElt_and_isScalarElt_mul
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

open scoped commutatorElement

namespace ThetaT2

set_option backward.isDefEq.respectTransparency false

section units
universe u
variable {X Y : Scheme.{u}}

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

theorem pullbackComp_id_hom_app (f : X ⟶ Y) (M : Y.Modules)
    (q : (Scheme.Modules.pullback f).obj M = (Scheme.Modules.pullback (𝟙 X ≫ f)).obj M) :
    (Scheme.Modules.pullbackComp (𝟙 X) f).hom.app M =
      (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback f).obj M) ≫ eqToHom q := by
  rw [← pullbackId_inv_app_comp f M q, Iso.hom_inv_id_app_assoc]

end units

section core
variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

theorem fib_mapComp_inv_app (a b : A ⟶ A) (M : A.Modules) :
    (Scheme.Modules.fibration.mapComp b.op.toLoc a.op.toLoc).inv.toNatTrans.app M =
      (Scheme.Modules.pullbackComp a b).hom.app M := by
  simp [Scheme.Modules.fibration, Scheme.Modules.pseudofunctor, Pseudofunctor.comp, Bicategory.Adj.forget₁,
    LocallyDiscrete.mkPseudofunctor]
  rfl

theorem fib_mapId_inv_app (M : A.Modules) :
    (Scheme.Modules.fibration.mapId ⟨Opposite.op A⟩).inv.toNatTrans.app M = (Scheme.Modules.pullbackId A).inv.app M := by
  simp [Scheme.Modules.fibration, Scheme.Modules.pseudofunctor, Pseudofunctor.comp, Bicategory.Adj.forget₁,
    LocallyDiscrete.mkPseudofunctor]

theorem isConstScalar_id (M : A.Modules) : IsConstScalar f (𝟙 M) (1 : k) := by
  intro U s
  rw [Scheme.Modules.Hom.id_app, map_one, map_one, map_one, one_smul]
  rfl

theorem isConstScalar_comp {M : A.Modules} {σ τ : M ⟶ M} {c d : k} (hσ : IsConstScalar f σ c) (hτ : IsConstScalar f τ d) :
    IsConstScalar f (σ ≫ τ) (d * c) := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, hσ U s, Scheme.Modules.Hom.app_smul, hτ U,
    ← mul_smul, map_mul, map_mul, map_mul]
  exact congrArg (· • s) (mul_comm _ _)

theorem reading_comp (M : A.Modules) (h₁ h₂ : modulePair (A := A) M ⟶ modulePair (A := A) M)
    (hB₁ : h₁.base = 𝟙 A) (hB₂ : h₂.base = 𝟙 A) (hB : (h₂ ≫ h₁).base = 𝟙 A) :
    (h₂ ≫ h₁).fiber ≫ (Scheme.Modules.pullbackCongr hB).hom.app M ≫ (Scheme.Modules.pullbackId A).hom.app M =
      (h₂.fiber ≫ (Scheme.Modules.pullbackCongr hB₂).hom.app M ≫ (Scheme.Modules.pullbackId A).hom.app M) ≫
        (h₁.fiber ≫ (Scheme.Modules.pullbackCongr hB₁).hom.app M ≫ (Scheme.Modules.pullbackId A).hom.app M) := by
  obtain ⟨B₁, φ₁⟩ := h₁
  obtain ⟨B₂, φ₂⟩ := h₂
  change B₁ = 𝟙 A at hB₁
  change B₂ = 𝟙 A at hB₂
  subst hB₁ hB₂
  simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber, Pseudofunctor.CoGrothendieck.categoryStruct_comp_base,
    modulePair_fiber, Scheme.Modules.fibration_map_toFunctor, fib_mapComp_inv_app, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.assoc]
  erw [pullbackComp_id_hom_app (𝟙 A) M rfl, eqToHom_refl]
  change φ₂ ≫ (Scheme.Modules.pullback (𝟙 A)).map φ₁ ≫
      ((Scheme.Modules.pullbackId A).hom.app ((Scheme.Modules.pullback (𝟙 A)).obj M) ≫ 𝟙 _) ≫ 𝟙 _ ≫
        (Scheme.Modules.pullbackId A).hom.app M =
    φ₂ ≫ 𝟙 _ ≫ (Scheme.Modules.pullbackId A).hom.app M ≫ φ₁ ≫ 𝟙 _ ≫ (Scheme.Modules.pullbackId A).hom.app M
  simp only [Category.id_comp, Category.comp_id]
  erw [← (Scheme.Modules.pullbackId A).hom.naturality_assoc φ₁]
  rfl

end core

theorem main
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    (∀ g : thetaGroup f L hc M, thetaGroup.pt f L hc M g = 1 → ∃! c : k, thetaGroup.IsScalarElt f L hc M g c) ∧
    (∀ (g h : thetaGroup f L hc M) (c d : k), thetaGroup.IsScalarElt f L hc M g c →
      thetaGroup.IsScalarElt f L hc M h d → thetaGroup.IsScalarElt f L hc M (g * h) (c * d)) ∧
    thetaGroup.IsScalarElt f L hc M 1 1 ∧
    (∀ g h : thetaGroup f L hc M, thetaGroup.pt f L hc M g = thetaGroup.pt f L hc M h →
      thetaGroup.pt f L hc M (g⁻¹ * h) = 1) := by
  refine ⟨fun g hg => ?_, fun g h c d hgc hhd => ?_, ?_, fun g h hgh => ?_⟩
  ·
    obtain ⟨c, hcc, huniq⟩ := AlgebraicGeometry.RiemannForm.existsUnique_isConstScalar k f hA M hM
      (thetaGroup.unitReading M (thetaGroup.base_eq_id_of_pt_eq_one f L hc M g hg))
    exact ⟨c, ⟨hg, hcc⟩, fun c' hc' => huniq c' hc'.2⟩
  ·
    obtain ⟨hg0, hgc⟩ := hgc
    obtain ⟨hh0, hhd⟩ := hhd
    have hgh0 : thetaGroup.pt f L hc M (g * h) = 1 := by rw [map_mul, hg0, hh0, mul_one]
    refine ⟨hgh0, ?_⟩
    have key : thetaGroup.unitReading M (thetaGroup.base_eq_id_of_pt_eq_one f L hc M (g * h) hgh0) =
        thetaGroup.unitReading M (thetaGroup.base_eq_id_of_pt_eq_one f L hc M h hh0) ≫
          thetaGroup.unitReading M (thetaGroup.base_eq_id_of_pt_eq_one f L hc M g hg0) :=
      reading_comp M g.1.1.hom h.1.1.hom (thetaGroup.base_eq_id_of_pt_eq_one f L hc M g hg0)
        (thetaGroup.base_eq_id_of_pt_eq_one f L hc M h hh0) (thetaGroup.base_eq_id_of_pt_eq_one f L hc M (g * h) hgh0)
    rw [key]
    exact isConstScalar_comp f hhd hgc
  ·
    refine ⟨map_one _, ?_⟩
    have e : thetaGroup.unitReading M (thetaGroup.base_eq_id_of_pt_eq_one f L hc M 1 (map_one _)) = 𝟙 M := by
      change (𝟙 (modulePair (A := A) M) : modulePair M ⟶ modulePair M).fiber ≫ _ ≫ _ = 𝟙 M
      simp only [Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber, modulePair_fiber, fib_mapId_inv_app,
        Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
      erw [Category.id_comp]
      exact (Scheme.Modules.pullbackId A).inv_hom_id_app M
    rw [e]
    exact isConstScalar_id f M
  · rw [map_mul, map_inv, hgh, inv_mul_cancel]

end ThetaT2

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    (∀ g : thetaGroup f L hc M, thetaGroup.pt f L hc M g = 1 → ∃! c : k, thetaGroup.IsScalarElt f L hc M g c) ∧
    (∀ (g h : thetaGroup f L hc M) (c d : k), thetaGroup.IsScalarElt f L hc M g c →
      thetaGroup.IsScalarElt f L hc M h d → thetaGroup.IsScalarElt f L hc M (g * h) (c * d)) ∧
    thetaGroup.IsScalarElt f L hc M 1 1 ∧
    (∀ g h : thetaGroup f L hc M, thetaGroup.pt f L hc M g = thetaGroup.pt f L hc M h →
      thetaGroup.pt f L hc M (g⁻¹ * h) = 1) :=
  ThetaT2.main k f L hc hA M hM

end S_AlgebraicGeometry_RiemannForm_thetaGroup_existsUnique_isScalarElt_and_isScalarElt_mul
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_existsUnique_isScalarElt_and_isScalarElt_mul (solution)
