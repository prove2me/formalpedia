-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_subgroup_thetaGroup_tensor_self_injOn_pt_image_eq_two_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/e9432e1a-1544-5880-8537-c287b2b3774a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_mul_comm_of_two_torsion_of_forall_two_torsion_pullback_translation_iso
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_pt_eq_one_and_isScalarElt
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_eq_one_of_isScalarElt_one
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_existsUnique_isScalarElt_and_isScalarElt_mul
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_ker_pt_le_center_and_commutatorElement_mem_ker
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_Subgroup_exists_subgroup_injOn_map_eq_of_ker_le_center_of_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_subgroup_thetaGroup_tensor_self_injOn_pt_image_eq_two_torsion
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hK2 : ∀ Q : L.AlgPoints hc k, 2 • Q = 0 →
      Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛₀ ≅ 𝓛₀)) :
    ∃ K : Subgroup (RiemannForm.thetaGroup f L hc (𝓛₀ ⊗ 𝓛₀)),
      (∀ g ∈ K, ∀ h ∈ K, RiemannForm.thetaGroup.pt f L hc (𝓛₀ ⊗ 𝓛₀) g = RiemannForm.thetaGroup.pt f L hc (𝓛₀ ⊗ 𝓛₀) h → g = h) ∧
      (∀ Q : L.AlgPoints hc k, (∃ g ∈ K, RiemannForm.thetaGroup.pt f L hc (𝓛₀ ⊗ 𝓛₀) g = Multiplicative.ofAdd Q) ↔ 2 • Q = 0) := by
  classical
  let M : A.Modules := 𝓛₀ ⊗ 𝓛₀
  have hM : Scheme.Modules.IsInvertible M := h𝓛₀.tensor_monoidalV2 h𝓛₀
  let π := RiemannForm.thetaGroup.pt f L hc M
  obtain ⟨hZ, -⟩ := AlgebraicGeometry.RiemannForm.thetaGroup.ker_pt_le_center_and_commutatorElement_mem_ker k f L hc hA M hM
  obtain ⟨huniq, hmul, hone, -⟩ :=
    AlgebraicGeometry.RiemannForm.thetaGroup.existsUnique_isScalarElt_and_isScalarElt_mul k f L hc hA M hM

  let H : Subgroup (Multiplicative (L.AlgPoints hc k)) :=
    { carrier := {v | 2 • Multiplicative.toAdd v = 0}
      mul_mem' := by
        intro a b ha hb
        change 2 • Multiplicative.toAdd (a * b) = 0
        rw [toAdd_mul, nsmul_add, ha, hb, add_zero]
      one_mem' := by change 2 • Multiplicative.toAdd (1 : Multiplicative (L.AlgPoints hc k)) = 0; rw [toAdd_one, nsmul_zero]
      inv_mem' := by
        intro a ha
        change 2 • Multiplicative.toAdd a⁻¹ = 0
        rw [toAdd_inv, smul_neg, ha, neg_zero] }
  have hHmem : ∀ v, v ∈ H ↔ 2 • Multiplicative.toAdd v = 0 := fun v => Iff.rfl

  have hsq : ∀ z ∈ π.ker, ∃ w ∈ π.ker, w * w = z := by
    intro z hz
    have hz1 : π z = 1 := hz
    obtain ⟨c, hc1, -⟩ := huniq z hz1

    have hzinv : π z⁻¹ = 1 := by rw [map_inv, hz1, inv_one]
    obtain ⟨c', hc', -⟩ := huniq z⁻¹ hzinv
    have h11 : RiemannForm.thetaGroup.IsScalarElt f L hc M 1 (c * c') := by
      have := hmul z z⁻¹ c c' hc1 hc'
      rwa [mul_inv_cancel] at this
    have hcc' : c * c' = 1 := (huniq 1 (map_one π)).unique h11 hone
    have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc'
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c two_pos
    have hd0 : d ≠ 0 := by rintro rfl; apply hc0; rw [← hd]; simp
    obtain ⟨w, hw1, hwd⟩ := AlgebraicGeometry.RiemannForm.thetaGroup.exists_pt_eq_one_and_isScalarElt k f L hc M d hd0
    refine ⟨w, hw1, ?_⟩
    have hww : RiemannForm.thetaGroup.IsScalarElt f L hc M (w * w) c := by
      have := hmul w w d d hwd hwd
      rwa [← pow_two d, hd] at this
    have h1 : RiemannForm.thetaGroup.IsScalarElt f L hc M (z⁻¹ * (w * w)) 1 := by
      have := hmul z⁻¹ (w * w) c' c hc' hww
      rwa [mul_comm c' c, hcc'] at this
    have := AlgebraicGeometry.RiemannForm.thetaGroup.eq_one_of_isScalarElt_one k f L hc M _ h1
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hH2 : ∀ h ∈ H, h * h = 1 := by
    intro h hh
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one, ← two_nsmul]
    exact hh
  have hlift : ∀ h ∈ H, ∃ g : RiemannForm.thetaGroup f L hc M, π g = h := by
    intro h hh
    obtain ⟨φ⟩ := hK2 (Multiplicative.toAdd h) hh
    exact ⟨RiemannForm.thetaGroup.liftOfIso f L hc M (Multiplicative.toAdd h)
      (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (φ ⊗ᵢ φ)), rfl⟩
  have hcomm : ∀ g g' : RiemannForm.thetaGroup f L hc M, π g ∈ H → π g' ∈ H → g * g' = g' * g :=
    fun g g' hg hg' => AlgebraicGeometry.RiemannForm.thetaGroup.mul_comm_of_two_torsion_of_forall_two_torsion_pullback_translation_iso
      k f L hc hA 𝓛₀ h𝓛₀ hK2 g g' hg hg'
  obtain ⟨K, hKinj, hKim⟩ := Subgroup.exists_subgroup_injOn_map_eq_of_ker_le_center_of_comm π hZ hsq H hH2 hlift hcomm
  refine ⟨K, hKinj, fun Q => ?_⟩
  exact (hKim (Multiplicative.ofAdd Q)).trans (by rw [hHmem, toAdd_ofAdd])

end
end S_AlgebraicGeometry_Polarisation_exists_subgroup_thetaGroup_tensor_self_injOn_pt_image_eq_two_torsion
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_subgroup_thetaGroup_tensor_self_injOn_pt_image_eq_two_torsion (solution)
