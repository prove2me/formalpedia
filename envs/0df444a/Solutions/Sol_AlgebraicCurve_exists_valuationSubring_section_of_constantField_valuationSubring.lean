-- Prove2me | solution 1 for AlgebraicCurve.exists_valuationSubring_section_of_constantField_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1291c7a7-18b0-56f3-8d75-16981624b845

import Mathlib
import Theorems.Thm_AlgebraicCurve_exists_regularProlongation_retraction_of_constantField_valuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_valuationSubring_section_of_constantField_valuationSubring
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring"

open AlgebraicCurve

theorem solution
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K)
    (hker : RingHom.ker σ = IsLocalRing.maximalIdeal A)
    (hsec : ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c) :
    ∃ (O : ValuationSubring F') (ρ : O →+* F),
      (∀ f : F, ∃ h : algebraMap F F' f ∈ O, ρ ⟨algebraMap F F' f, h⟩ = f) ∧
      RingHom.ker ρ = IsLocalRing.maximalIdeal O ∧
      (∀ f' : F', f' ≠ 0 → ∃ c : K', ∃ h : c • f' ∈ O, ρ ⟨c • f', h⟩ ≠ 0) ∧
      (∀ (c : K') (h : algebraMap K' F' c ∈ O),
        ρ ⟨algebraMap K' F' c, h⟩ ∈ Set.range (algebraMap K F)) := by
  obtain ⟨O, ρ, hmem_iff, hker_ρ, hresA, hreg, hret⟩ :=
    AlgebraicCurve.exists_regularProlongation_retraction_of_constantField_valuationSubring
      K F K' F' hfg hfg' hgen A hK σ hker hsec
  refine ⟨O, ρ, hret, hker_ρ, hreg, ?_⟩

  intro c hc
  obtain ⟨h', hρ⟩ := hresA ⟨c, (hmem_iff c).mp hc⟩
  exact ⟨σ ⟨c, (hmem_iff c).mp hc⟩, hρ.symm⟩

end S_AlgebraicCurve_exists_valuationSubring_section_of_constantField_valuationSubring
end P2MW
export P2MW.S_AlgebraicCurve_exists_valuationSubring_section_of_constantField_valuationSubring (solution)
