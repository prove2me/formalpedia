-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.thetaGroup.mul_comm_of_two_torsion_of_forall_two_torsion_pullback_translation_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3d98219e-5261-536b-9482-a449650dd3bf

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_eq_one_of_isScalarElt_one
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_existsUnique_isScalarElt_and_isScalarElt_mul
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_ker_pt_le_center_and_commutatorElement_mem_ker
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_self_pt_eq_and_isScalarElt_mul_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_mul_comm_of_two_torsion_of_forall_two_torsion_pullback_translation_iso
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation"

namespace LiftsCommute

theorem comm_of_comm_of_central {G : Type*} [Group G] {a b z z' : G} (hab : a * b = b * a)
    (hz : z ∈ Subgroup.center G) (hz' : z' ∈ Subgroup.center G) : (a * z) * (b * z') = (b * z') * (a * z) := by
  rw [Subgroup.mem_center_iff] at hz hz'
  calc (a * z) * (b * z') = a * (z * b) * z' := by group
    _ = a * (b * z) * z' := by rw [hz b]
    _ = (a * b) * (z * z') := by group
    _ = (b * a) * (z' * z) := by rw [hab, hz z']
    _ = b * (a * z') * z := by group
    _ = b * (z' * a) * z := by rw [hz' a]
    _ = (b * z') * (a * z) := by group

theorem commutator_sq_eq_one {G : Type*} [Group G] {a b : G} (hκ : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center G)
    (ha2 : a * a ∈ Subgroup.center G) : (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) = 1 := by
  set κ := a * b * a⁻¹ * b⁻¹ with hκdef
  rw [Subgroup.mem_center_iff] at hκ ha2
  have hab : a * b = κ * b * a := by rw [hκdef]; group

  have h1 : a * a * b = κ * κ * (b * (a * a)) := by
    calc a * a * b = a * (a * b) := by group
      _ = a * (κ * b * a) := by rw [hab]
      _ = (a * κ) * b * a := by group
      _ = (κ * a) * b * a := by rw [hκ a]
      _ = κ * (a * b) * a := by group
      _ = κ * (κ * b * a) * a := by rw [hab]
      _ = κ * κ * (b * (a * a)) := by group
  rw [← ha2 b] at h1
  have h2 : κ * κ * (b * (a * a)) = 1 * (b * (a * a)) := by rw [one_mul]; exact h1.symm
  exact mul_right_cancel h2

end LiftsCommute

open LiftsCommute in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hK2 : ∀ Q : L.AlgPoints hc k, 2 • Q = 0 →
      Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛₀ ≅ 𝓛₀))
    (g g' : thetaGroup f L hc (𝓛₀ ⊗ 𝓛₀))
    (hg : 2 • Multiplicative.toAdd (thetaGroup.pt f L hc (𝓛₀ ⊗ 𝓛₀) g) = 0)
    (hg' : 2 • Multiplicative.toAdd (thetaGroup.pt f L hc (𝓛₀ ⊗ 𝓛₀) g') = 0) :
    g * g' = g' * g := by
  classical
  let M : A.Modules := 𝓛₀ ⊗ 𝓛₀
  have hM : Scheme.Modules.IsInvertible M := h𝓛₀.tensor_monoidalV2 h𝓛₀
  obtain ⟨ε, hεpt, hεsc⟩ := AlgebraicGeometry.RiemannForm.thetaGroup.exists_monoidHom_tensor_self_pt_eq_and_isScalarElt_mul_self k f L hc hA 𝓛₀ h𝓛₀
  obtain ⟨hZ0, hcomm0⟩ := AlgebraicGeometry.RiemannForm.thetaGroup.ker_pt_le_center_and_commutatorElement_mem_ker k f L hc hA 𝓛₀ h𝓛₀
  obtain ⟨hZ, -⟩ := AlgebraicGeometry.RiemannForm.thetaGroup.ker_pt_le_center_and_commutatorElement_mem_ker k f L hc hA M hM
  obtain ⟨huniq0, hmul0, hone0, -⟩ :=
    AlgebraicGeometry.RiemannForm.thetaGroup.existsUnique_isScalarElt_and_isScalarElt_mul k f L hc hA 𝓛₀ h𝓛₀

  have hlift : ∀ h : thetaGroup f L hc M, 2 • Multiplicative.toAdd (thetaGroup.pt f L hc M h) = 0 →
      ∃ (h₀ : thetaGroup f L hc 𝓛₀) (z : thetaGroup f L hc M), z ∈ Subgroup.center (thetaGroup f L hc M) ∧
        h = ε h₀ * z ∧ h₀ * h₀ ∈ Subgroup.center (thetaGroup f L hc 𝓛₀) := by
    intro h hh
    obtain ⟨φ⟩ := hK2 (Multiplicative.toAdd (thetaGroup.pt f L hc M h)) hh
    let h₀ := thetaGroup.liftOfIso f L hc 𝓛₀ (Multiplicative.toAdd (thetaGroup.pt f L hc M h)) φ
    have hpt0 : thetaGroup.pt f L hc 𝓛₀ h₀ = thetaGroup.pt f L hc M h := by
      change Multiplicative.ofAdd (Multiplicative.toAdd (thetaGroup.pt f L hc M h)) = _
      exact ofAdd_toAdd _
    let z := (ε h₀)⁻¹ * h
    have hz : z ∈ (thetaGroup.pt f L hc M).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hεpt, hpt0, inv_mul_cancel]
    refine ⟨h₀, z, hZ hz, by simp [z], hZ0 ?_⟩
    rw [MonoidHom.mem_ker, map_mul, hpt0, ← ofAdd_toAdd (thetaGroup.pt f L hc M h), ← ofAdd_add, ← two_nsmul, hh, ofAdd_zero]
  obtain ⟨g₀, z, hz, hgz, hg2⟩ := hlift g hg
  obtain ⟨g₀', z', hz', hgz', -⟩ := hlift g' hg'

  let κ := g₀ * g₀' * g₀⁻¹ * g₀'⁻¹
  have hκker : κ ∈ (thetaGroup.pt f L hc 𝓛₀).ker := hcomm0 g₀ g₀'
  have hκZ : κ ∈ Subgroup.center (thetaGroup f L hc 𝓛₀) := hZ0 hκker
  have hκ2 : κ * κ = 1 := commutator_sq_eq_one hκZ hg2
  obtain ⟨c, hc1, -⟩ := huniq0 κ hκker
  have hcc : c * c = 1 := by
    have h2 : thetaGroup.IsScalarElt f L hc 𝓛₀ (κ * κ) (c * c) := hmul0 κ κ c c hc1 hc1
    rw [hκ2] at h2
    exact (huniq0 1 (map_one _)).unique h2 hone0
  have hεκ : ε κ = 1 := by
    apply AlgebraicGeometry.RiemannForm.thetaGroup.eq_one_of_isScalarElt_one k f L hc M
    have := hεsc κ c hc1
    rwa [hcc] at this
  have hεcomm : ε g₀ * ε g₀' = ε g₀' * ε g₀ := by
    have : ε κ = ε g₀ * ε g₀' * (ε g₀)⁻¹ * (ε g₀')⁻¹ := by simp [κ, map_mul, map_inv]
    rw [hεκ] at this
    calc ε g₀ * ε g₀' = (ε g₀ * ε g₀' * (ε g₀)⁻¹ * (ε g₀')⁻¹) * (ε g₀' * ε g₀) := by group
      _ = ε g₀' * ε g₀ := by rw [← this, one_mul]
  rw [hgz, hgz']
  exact comm_of_comm_of_central hεcomm hz hz'

end
end S_AlgebraicGeometry_RiemannForm_thetaGroup_mul_comm_of_two_torsion_of_forall_two_torsion_pullback_translation_iso
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_mul_comm_of_two_torsion_of_forall_two_torsion_pullback_translation_iso (solution)
