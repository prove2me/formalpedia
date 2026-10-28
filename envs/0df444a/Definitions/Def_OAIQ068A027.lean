-- Prove2me | Definitions.Def_OAIQ068A027
-- name    : OAIQ068A027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:57:56.824827+00:00
-- url     : https://prove2.me/theorems/3d3d45a6-f7e9-4dd0-a2d1-132ad1170eed
-- title:
--   Definitions bundle OAIQ068A027 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 27 definitions, 2 inductive types or structures, 7 instances and 15 theorems. The definitions and types are `OAI.PiExponentApprox.TransverseMultiplicity.rectangularQuotientEquiv`, `OAI.PiExponentApprox.polynomialDerivativeCore`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.CoefficientClosedLocal`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPolynomialIdeal`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.coefficientClosedPoint`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateBasisClosedPointEquiv`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.originalLocalCoefficientLocalEquiv`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.polynomialPrimeClosedPointEquiv`, `OAI.PiExponentJets.W22.ActualRegularCutHistory`, `OAI.PiExponentJets.W22.ProjectiveComponent.hilbertDegree`, `OAI.PiExponentJets.W22.RegularPrefixCut`, `OAI.PiExponentJets.W22.RegularPrefixCut.next`, `OAI.PiExponentJets.W22.RetainedPrimeCycle.degree`, `OAI.PiExponentJets.W22.actualHP`, `OAI.PiExponentJets.W22.actualMultiplicity`, `OAI.PiExponentJets.W24.ringEquiv_localQuotient`, `OAI.PiExponentSeshadri.IdealModule.descendedPowerLayer`, `OAI.PiExponentSeshadri.IdealModule.powerLayer`, `OAI.PiExponentSeshadri.IdealModule.powerMap`, `OAI.PiExponentSeshadri.IdealModule.powerSequence`, `OAI.PiExponentSeshadri.ProjectiveChartSections.framedLaurentVertex`, `OAI.PiExponentSiegel.W23.affineClosedQuotientLocalEquiv`, `OAI.PiExponentSiegel.W23.affineCoefficientAlgHom`, `OAI.PiExponentSiegel.W23.affineCoefficientAlgebra`, `OAI.PiExponentSiegel.W23.affineCoefficientMap`, `OAI.PiExponentSiegel.W23.affineLocalQuotientEquiv`, `OAI.PiExponentSiegel.W23.affineMappedIdeal`, `OAI.PiExponentSiegel.W23.affineQuotientAlgebra`, `OAI.PiExponentSiegel.W23.affineQuotientMap`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Geometry_CurveContact`, `PiExponent_Geometry_LineBundleTensor`, `PiExponent_Geometry_ProjectiveChartSections`, `PiExponent_Jets_TransverseMultiplicity`, `PiExponent_LocalAlgebra_AffineClosedPointLocalization`, `PiExponent_LocalAlgebra_CoordinateBasisSplitting`, `PiExponent_LocalAlgebra_HilbertDenominatorReduction`, `PiExponent_LocalAlgebra_HilbertMultiplicityFiltration`, `PiExponent_LocalAlgebra_IdealPowerAnnihilator`, `PiExponent_LocalAlgebra_IdealPowerDescent`, `PiExponent_LocalAlgebra_IdealPowerFiltration`, `PiExponent_LocalAlgebra_RegularCutHistory`, `PiExponent_LocalAlgebra_RetainedIntersectionCycles`, `PiExponent_LocalAlgebra_SplitClosedPointCompatibility`, `PiExponent_Polynomials_HilbertPolynomial`, `PiExponent_Polynomials_HomogeneousHilbertExistence`, `PiExponent_Polynomials_HomogeneousHilbertPolynomial`, `PiExponent_Polynomials_PolynomialPrimeClosedPointEquiv`, `PiExponent_Polynomials_PolynomialPrimeDimension`.
--
--   **Imports.** It imports the bundles `OAIQ068A012`, `OAIQ068A016`, `OAIQ068A017` and `OAIQ068A018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A033` and `OAIQ068A034`; the statements `OAI_PiExponentJets_W22_ActualRegularCutHistory_degree_bound`, `OAI.PiExponentJets.W22.ActualRegularCutHistory.degree_bound_q68`, `OAI_PiExponentJets_W22_RetainedPrimeCycle_retainedChild_dimension`, `OAI.PiExponentJets.W22.RetainedPrimeCycle.retainedChild_dimension_q68`, `OAI_PiExponentJets_W22_actualHP_natDegree_of_prime_dimension`, `OAI.PiExponentJets.W22.actualHP_natDegree_of_prime_dimension_q68`, `OAI_PiExponentJets_W22_actualMultiplicityCycle_zero_degree`, `OAI.PiExponentJets.W22.actualMultiplicityCycle_zero_degree_q68`, `OAI_PiExponentJets_W22_component_multiplicity_sum_bound`, `OAI.PiExponentJets.W22.component_multiplicity_sum_bound_q68`, `OAI_PiExponentJets_W22_homogeneous_prefix_hilbert_degree` and `OAI.PiExponentJets.W22.homogeneous_prefix_hilbert_degree_q68`; the proofs of `OAI_PiExponentJets_PolynomialLocalResidueResolution_exists_regularParameters_actual_height`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height_q68`, `OAI_PiExponentJets_W22_ActualRegularCutHistory_degree_bound`, `OAI.PiExponentJets.W22.ActualRegularCutHistory.degree_bound_q68`, `OAI_PiExponentJets_W22_RetainedPrimeCycle_retainedChild_dimension`, `OAI.PiExponentJets.W22.RetainedPrimeCycle.retainedChild_dimension_q68`, `OAI_PiExponentJets_W22_actualHP_natDegree_of_prime_dimension`, `OAI.PiExponentJets.W22.actualHP_natDegree_of_prime_dimension_q68`, `OAI_PiExponentJets_W22_actualMultiplicityCycle_zero_degree`, `OAI.PiExponentJets.W22.actualMultiplicityCycle_zero_degree_q68`, `OAI_PiExponentJets_W22_component_multiplicity_sum_bound`, `OAI.PiExponentJets.W22.component_multiplicity_sum_bound_q68`, `OAI_PiExponentJets_W22_homogeneous_local_regular_bezout`, `OAI.PiExponentJets.W22.homogeneous_local_regular_bezout_q68`, `OAI_PiExponentJets_W22_homogeneous_prefix_hilbert_degree`, `OAI.PiExponentJets.W22.homogeneous_prefix_hilbert_degree_q68`, `OAI_PiExponentJets_W24_polynomial_prime_pair_dimension`, `OAI.PiExponentJets.W24.polynomial_prime_pair_dimension_q68`, `OAI_PiExponent_CoordinateSliceComparison_length_eq_sliceFamily_of_normalBasis`, `OAI.PiExponent.CoordinateSliceComparison.length_eq_sliceFamily_of_normalBasis_q68`, `OAI_PiExponent_CoordinateSliceComparison_sliceFamily_mem_minimalPrimes_of_normalBasis`, `OAI.PiExponent.CoordinateSliceComparison.sliceFamily_mem_minimalPrimes_of_normalBasis_q68`, `OAI_PiExponent_CurveComponentRigidity_coordinate_constant_of_persistent_comparison`, `OAI.PiExponent.CurveComponentRigidity.coordinate_constant_of_persistent_comparison_q68`, `OAI_PiExponent_CurvePrimeHeight_kernel_height_le`, `OAI.PiExponent.CurvePrimeHeight.kernel_height_le_q68`, `OAI_PiExponent_CurvePrimeHeight_kernel_height_succ_le` and `OAI.PiExponent.CurvePrimeHeight.kernel_height_succ_le_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A012
import Definitions.Def_OAIQ068A016
import Definitions.Def_OAIQ068A017
import Definitions.Def_OAIQ068A018

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContact
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox

noncomputable section

def polynomialDerivativeCore {m : ℕ}
    (D : Derivation ℂ (FramePolynomial m) (FramePolynomial m))
    (I : Ideal (FramePolynomial m)) : Ideal (FramePolynomial m) where
  carrier := {p | p ∈ I ∧ D p ∈ I}
  zero_mem' := by simp only [Set.mem_ofPred_eq, D.map_zero]; exact ⟨I.zero_mem, I.zero_mem⟩
  add_mem' := by
    intro p q hp hq
    refine ⟨I.add_mem hp.1 hq.1, ?_⟩
    rw [map_add]
    exact I.add_mem hp.2 hq.2
  smul_mem' := by
    intro r p hp
    change r * p ∈ I ∧ D (r * p) ∈ I
    refine ⟨I.mul_mem_left r hp.1, ?_⟩
    rw [Derivation.leibniz]
    exact I.add_mem (I.mul_mem_left r hp.2) (by
      simpa only [smul_eq_mul, mul_comm] using I.mul_mem_left (D r) hp.1)

end
end PiExponentApprox

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_LineBundleTensor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace Geometry

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

instance powerSection_isIso {M : X.Modules} (s : structureSheaf X ⟶ M) [IsIso s] (n : ℕ) :
    IsIso (powerSection s n) := by unfold powerSection; infer_instance

end Geometry

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveChartSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ProjectiveChartSections

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology

variable {X : Scheme} (U : X.Opens) (M : X.Modules)

open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
variable {R ι : Type} [CommRing R] [Fintype ι] (i : ι) (d : ℤ)

def framedLaurentVertex (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* MvPolynomial {j : ι // j ≠ i} R) :
    (schemeFreeOpen_p0 X U ⟶ M) →+ Laurent ι R d :=
  (vertexLaurent i d).toAddMonoidHom.comp (framedHomRingEquiv U M e r).toAddMonoidHom

end PiExponentSeshadri.ProjectiveChartSections

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_TransverseMultiplicity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox.TransverseMultiplicity

noncomputable section

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

theorem rectangularQuotientCoefficients_bijective (n : σ → ℕ) :
    Function.Bijective (rectangularQuotientCoefficients (K := K) n) := by
  constructor
  · intro a b hab
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    intro d hd
    have hc := congrFun hab (⟨d, hd⟩ : RectIndex n)
    change coeff d f = coeff d g at hc
    rw [map_sub, hc, sub_self]
  · intro packet
    obtain ⟨f, hf⟩ := rectangularPacket_surjective (K := K) n packet
    exact ⟨Ideal.Quotient.mk (rectangularIdeal (K := K) n) f, hf⟩

def rectangularQuotientEquiv (n : σ → ℕ) :
    (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) ≃ₗ[K] (RectIndex n → K) :=
  LinearEquiv.ofBijective (rectangularQuotientCoefficients n)
    (rectangularQuotientCoefficients_bijective n)

end
end PiExponentApprox.TransverseMultiplicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_SplitClosedPointCompatibility
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

theorem closedPointEvaluation_original :
    ((closedPointEvaluationRingHom K α β Q hB).comp
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom).comp
      (algebraMap (MvPolynomial (α ⊕ β) K)
        (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)) =
      algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change closedPointEvaluation K α β Q hB
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
        (algebraMap (MvPolynomial (α ⊕ β) K)
          (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)
          (MvPolynomial.C a))) = _
    have h := closedPointEvaluation_coefficient K α β Q hB (MvPolynomial.C a)
    rw [← PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_coefficient] at h
    simpa only [RingHom.comp_apply, MvPolynomial.rename_C, MvPolynomial.aeval_C,
      IsScalarTower.algebraMap_apply K (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q),
      MvPolynomial.algebraMap_eq] using h
  · intro i
    cases i with
    | inl i =>
      let := splitCoefficientResidueAlgebra K α β Q hB
      change closedPointEvaluation K α β Q hB
        (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
          (algebraMap (MvPolynomial (α ⊕ β) K)
            (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)
            (MvPolynomial.X (Sum.inl i)))) = _
      rw [PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inl,
        closedPointEvaluation, MvPolynomial.aeval_X]
    | inr j =>
      let := splitCoefficientResidueAlgebra K α β Q hB
      change closedPointEvaluation K α β Q hB
        (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
          (algebraMap (MvPolynomial (α ⊕ β) K)
            (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)
            (MvPolynomial.X (Sum.inr j)))) = _
      rw [PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inr,
        closedPointEvaluation_coefficient, MvPolynomial.aeval_X]
      rfl

theorem coefficientClosedPoint_comap :
    (RingHom.ker ((closedPointEvaluationRingHom K α β Q hB).comp
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom)).comap
      (algebraMap (MvPolynomial (α ⊕ β) K)
        (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)) = Q := by
  ext f
  change closedPointEvaluation K α β Q hB
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
      (algebraMap _ (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β) f)) = 0 ↔ f ∈ Q
  have h := RingHom.congr_fun (closedPointEvaluation_original K α β Q hB) f
  change closedPointEvaluation K α β Q hB
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
      (algebraMap _ (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β) f)) =
        algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q) f at h
  rw [h]
  exact Ideal.algebraMap_residueField_eq_zero

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialPrimeClosedPointEquiv
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

def coefficientClosedPoint :
    Ideal (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β) :=
  RingHom.ker ((closedPointEvaluationRingHom K α β Q hB).comp
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom)

instance coefficientClosedPoint_isMaximal :
    (coefficientClosedPoint K α β Q hB).IsMaximal := by
  change ((RingHom.ker (closedPointEvaluationRingHom K α β Q hB)).comap
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom).IsMaximal
  let := closedPointEvaluation_kernel_maximal K α β Q hB
  exact Ideal.comap_isMaximal_of_surjective _
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).surjective

abbrev CoefficientClosedLocal := Localization.AtPrime (coefficientClosedPoint K α β Q hB)

theorem closedLocal_isLocalizationAtOriginal :
    IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB) Q := by
  have h : IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB)
      ((coefficientClosedPoint K α β Q hB).comap
        (algebraMap (MvPolynomial (α ⊕ β) K)
          (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β))) := by
    infer_instance
  have hQ : (coefficientClosedPoint K α β Q hB).comap
      (algebraMap (MvPolynomial (α ⊕ β) K)
        (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)) = Q :=
    coefficientClosedPoint_comap K α β Q hB
  have transport (J : Ideal (MvPolynomial (α ⊕ β) K)) [J.IsPrime]
      (he : J = Q) :
      IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB) J →
        IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB) Q := by
    subst J
    exact id
  exact transport _ hQ h

def originalLocalCoefficientLocalEquiv :
    Localization.AtPrime Q ≃+* CoefficientClosedLocal K α β Q hB := by
  letI := closedLocal_isLocalizationAtOriginal K α β Q hB
  exact (IsLocalization.algEquiv Q.primeCompl
    (Localization.AtPrime Q) (CoefficientClosedLocal K α β Q hB)).toRingEquiv

def closedPolynomialIdeal : Ideal (MvPolynomial α (SplitCoefficientField K β)) :=
  (coefficientClosedPoint K α β Q hB).map
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom

instance closedPolynomialIdeal_isMaximal :
    (closedPolynomialIdeal K α β Q hB).IsMaximal := by
  exact (inferInstance : (coefficientClosedPoint K α β Q hB).IsMaximal).map_bijective
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).bijective

def polynomialPrimeClosedPointEquiv :
    Localization.AtPrime Q ≃+*
      Localization.AtPrime (closedPolynomialIdeal K α β Q hB) :=
  (originalLocalCoefficientLocalEquiv K α β Q hB).trans
    (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
      (coefficientClosedPoint K α β Q hB))

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_AffineClosedPointLocalization
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegel.W23
open PiExponentSiegelAux.W09
open PiExponentJets.PolynomialLocalResidueResolution

variable (K α β : Type*) [Field K]

def affineCoefficientAlgHom :
    SplitPolynomial K α β →ₐ[K] FractionCoefficientPolynomial K α β :=
  (polynomialCoefficientLocalizationEquiv K α β).toAlgHom.comp
    (IsScalarTower.toAlgHom K (SplitPolynomial K α β)
      (PolynomialCoefficientLocalization K α β))

abbrev affineCoefficientMap :
    SplitPolynomial K α β →+* FractionCoefficientPolynomial K α β :=
  (affineCoefficientAlgHom K α β).toRingHom

@[reducible] def affineCoefficientAlgebra :
    Algebra (SplitPolynomial K α β) (FractionCoefficientPolynomial K α β) :=
  (affineCoefficientMap K α β).toAlgebra

attribute [local instance] affineCoefficientAlgebra

instance affineCoefficient_isLocalization :
    IsLocalization (coefficientDenominators K α β) (FractionCoefficientPolynomial K α β) := by
  exact (IsLocalization.isLocalization_iff_of_ringEquiv
    (coefficientDenominators K α β)
    (polynomialCoefficientLocalizationEquiv K α β).toRingEquiv).mp inferInstance

def affineMappedIdeal (P : Ideal (SplitPolynomial K α β)) :
    Ideal (FractionCoefficientPolynomial K α β) :=
  P.map (affineCoefficientMap K α β)

variable (Q : Ideal (SplitPolynomial K α β)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

theorem affineCoefficientMap_comap_closedPoint :
    (closedPolynomialIdeal K α β Q hB).comap (affineCoefficientMap K α β) = Q := by
  change ((coefficientClosedPoint K α β Q hB).map
      (polynomialCoefficientLocalizationEquiv K α β).toRingHom).comap
      ((polynomialCoefficientLocalizationEquiv K α β).toRingHom.comp
        (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β))) = Q
  rw [← Ideal.comap_comap, ← atPrimeImage_comap]
  exact coefficientClosedPoint_comap K α β Q hB

theorem affineMappedIdeal_le_closedPoint (P : Ideal (SplitPolynomial K α β)) (hPQ : P ≤ Q) :
    affineMappedIdeal K α β P ≤ closedPolynomialIdeal K α β Q hB := by
  apply Ideal.map_le_iff_le_comap.mpr
  rw [affineCoefficientMap_comap_closedPoint]
  exact hPQ

theorem originalLocalCoefficientLocalEquiv_algebraMap (a : SplitPolynomial K α β) :
    originalLocalCoefficientLocalEquiv K α β Q hB
      (algebraMap (SplitPolynomial K α β) (Localization.AtPrime Q) a) =
      algebraMap (SplitPolynomial K α β) (CoefficientClosedLocal K α β Q hB) a := by
  let := closedLocal_isLocalizationAtOriginal K α β Q hB
  exact (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
    (CoefficientClosedLocal K α β Q hB)).commutes a

theorem closedPointLocalEquiv_algebraMap (a : SplitPolynomial K α β) :
    polynomialPrimeClosedPointEquiv K α β Q hB
      (algebraMap (SplitPolynomial K α β) (Localization.AtPrime Q) a) =
      algebraMap (FractionCoefficientPolynomial K α β)
        (Localization.AtPrime (closedPolynomialIdeal K α β Q hB))
        (affineCoefficientMap K α β a) := by
  change atPrimeEquivOfRingEquiv
    (polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
    (coefficientClosedPoint K α β Q hB)
    (originalLocalCoefficientLocalEquiv K α β Q hB
      (algebraMap (SplitPolynomial K α β) (Localization.AtPrime Q) a)) = _
  exact (congrArg (atPrimeEquivOfRingEquiv
    (polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
    (coefficientClosedPoint K α β Q hB))
    (originalLocalCoefficientLocalEquiv_algebraMap K α β Q hB a)).trans
    (atPrimeEquivOfRingEquiv_algebraMap
      (polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
      (coefficientClosedPoint K α β Q hB)
      (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β) a))

theorem closedPointLocalEquiv_map_ideal (P : Ideal (SplitPolynomial K α β)) :
    (parameterLocalizedIdeal P Q).map
      (polynomialPrimeClosedPointEquiv K α β Q hB).toRingHom =
    parameterLocalizedIdeal (affineMappedIdeal K α β P)
      (closedPolynomialIdeal K α β Q hB) := by
  unfold parameterLocalizedIdeal affineMappedIdeal
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro a
  exact closedPointLocalEquiv_algebraMap K α β Q hB a

def affineLocalQuotientEquiv (P : Ideal (SplitPolynomial K α β)) :
    (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) ≃+*
      (Localization.AtPrime (closedPolynomialIdeal K α β Q hB) ⧸
        parameterLocalizedIdeal (affineMappedIdeal K α β P)
          (closedPolynomialIdeal K α β Q hB)) :=
  Ideal.quotientEquiv _ _ (polynomialPrimeClosedPointEquiv K α β Q hB)
    (closedPointLocalEquiv_map_ideal K α β Q hB P).symm

def affineClosedQuotientLocalEquiv (P : Ideal (SplitPolynomial K α β)) (hPQ : P ≤ Q) :
    Localization.AtPrime (quotientParameterPrime P Q hPQ) ≃+*
      Localization.AtPrime
        (R := FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)
        (quotientParameterPrime (affineMappedIdeal K α β P)
        (closedPolynomialIdeal K α β Q hB)
        (affineMappedIdeal_le_closedPoint K α β Q hB P hPQ)) :=
  ((localizationQuotientParametersEquiv P Q hPQ).symm.trans
    (affineLocalQuotientEquiv K α β Q hB P)).trans
    (localizationQuotientParametersEquiv (affineMappedIdeal K α β P)
      (closedPolynomialIdeal K α β Q hB)
      (affineMappedIdeal_le_closedPoint K α β Q hB P hPQ))

def affineQuotientMap (P : Ideal (SplitPolynomial K α β)) :
    (SplitPolynomial K α β ⧸ P) →+*
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) :=
  Ideal.quotientMap _ (affineCoefficientMap K α β) Ideal.le_comap_map

@[reducible] def affineQuotientAlgebra (P : Ideal (SplitPolynomial K α β)) :
    Algebra (SplitPolynomial K α β ⧸ P)
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) :=
  RingHom.toAlgebra'
    (R := SplitPolynomial K α β ⧸ P)
    (S := FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)
    (affineQuotientMap K α β P) (fun x y =>
      (Ideal.Quotient.commSemiring (affineMappedIdeal K α β P)).mul_comm
        (affineQuotientMap K α β P x) y)

attribute [local instance] affineQuotientAlgebra

@[simp] theorem affineQuotientMap_mk (P : Ideal (SplitPolynomial K α β))
    (a : SplitPolynomial K α β) :
    affineQuotientMap K α β P (Ideal.Quotient.mk P a) =
      Ideal.Quotient.mk _ (affineCoefficientMap K α β a) := rfl

instance affineQuotient_scalarTower (P : Ideal (SplitPolynomial K α β)) :
    IsScalarTower K (SplitPolynomial K α β ⧸ P)
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) := by
  apply IsScalarTower.of_algebraMap_eq
    (R := K) (S := SplitPolynomial K α β ⧸ P)
    (A := FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)
  intro k
  change Ideal.Quotient.mk _ (algebraMap K (FractionCoefficientPolynomial K α β) k) =
    affineQuotientMap K α β P (Ideal.Quotient.mk P (algebraMap K (SplitPolynomial K α β) k))
  rw [affineQuotientMap_mk]
  exact congrArg (Ideal.Quotient.mk (affineMappedIdeal K α β P))
    ((affineCoefficientAlgHom K α β).commutes k).symm

end PiExponentSiegel.W23

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoordinateBasisSplitting
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable {n : ℕ} {T : Type*} (j : T → Fin n) (hj : Function.Injective j)

variable (K : Type*) [Field K] (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]
variable (t : Set Q.ResidueField) (j : t → Fin n) (hj : Function.Injective j)
variable (hcoord : ∀ a, residueCoordinate K n Q (j a) = (a : Q.ResidueField))
variable (ht : IsTranscendenceBasis K ((↑) : t → Q.ResidueField))

def coordinateBasisClosedPointEquiv : Localization.AtPrime Q ≃+*
    Localization.AtPrime
      (closedPolynomialIdeal K (RemainingCoordinate j) t (coordinateSplitPrime K Q t j hj)
        (coordinateSplitPrime_basis K Q t j hj hcoord ht)) :=
  (coordinateBasisLocalEquiv K Q t j hj).trans
    (polynomialPrimeClosedPointEquiv K (RemainingCoordinate j) t
      (coordinateSplitPrime K Q t j hj)
      (coordinateSplitPrime_basis K Q t j hj hcoord ht))

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_HilbertDenominatorReduction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

theorem stabilized_colon_polynomial_numerator
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1) (m r : ℕ)
    (hstable : iteratedColon I f (m+1) = iteratedColon I f m)
    (P : ℕ → Polynomial ℤ)
    (hP : ∀ j : ℕ, sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f j) =
      (P j : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ r).val) :
    sectionHilbertSeries I = (colonHilbertNumerator P m : PowerSeries ℤ) *
      (PowerSeries.invOneSubPow ℤ (r+1)).val := by
  have hu : (PowerSeries.invOneSubPow ℤ r).val =
      (1-PowerSeries.X) * (PowerSeries.invOneSubPow ℤ (r+1)).val := by
    symm
    simpa only [pow_one, Nat.add_comm] using
      PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℤ r 1
  have hv : (PowerSeries.invOneSubPow ℤ r).val * (PowerSeries.invOneSubPow ℤ 1).val =
      (PowerSeries.invOneSubPow ℤ (r+1)).val := by
    rw [← Units.val_mul, ← PowerSeries.invOneSubPow_add]
  rw [stabilized_iteratedColon_series I hI f hf m hstable]
  simp_rw [hP]
  have hsum : (∑ j ∈ Finset.range m,
      PowerSeries.X ^ j * ((P j : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ r).val)) =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j * (P j : PowerSeries ℤ)) *
        (PowerSeries.invOneSubPow ℤ r).val := by
    simp only [Finset.sum_mul, mul_assoc]
  rw [hsum, mul_assoc (P m : PowerSeries ℤ), hv, hu]
  have hcoe : (colonHilbertNumerator P m : PowerSeries ℤ) =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j * (P j : PowerSeries ℤ)) *
        (1-PowerSeries.X) + PowerSeries.X ^ m * (P m : PowerSeries ℤ) := by
    change Polynomial.coeToPowerSeries.ringHom
      ((∑ j ∈ Finset.range m, Polynomial.X ^ j * P j) * (1-Polynomial.X) +
        Polynomial.X ^ m * P m) = _
    rw [map_add, map_mul, map_sum]
    simp only [map_mul, map_sub, map_pow, map_one]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  rw [hcoe]
  ring

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousHilbertExistence
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type v} [Field k]

theorem exists_homogeneous_hilbert_numerator
    (σ : Type u) [Fintype σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ P : Polynomial ℤ, sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  classical
  refine Fintype.induction_empty_option
    (P := fun τ _ => ∀ J : Ideal (MvPolynomial τ k),
      J.IsHomogeneous (MvPolynomial.homogeneousSubmodule τ k) →
      ∃ P : Polynomial ℤ, sectionHilbertSeries J =
        (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card τ)).val)
    ?_ ?_ ?_ σ I hI
  · intro α β _ e ih J hJ
    let : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨P, hP⟩ := ih (J.map (MvPolynomial.rename e.symm).toRingHom)
      (PiExponentSiegel.W08.renameImageIdeal_homogeneous e.symm J hJ)
    refine ⟨P, ?_⟩
    rw [sectionHilbertSeries_rename e.symm J]
    simpa only [Fintype.card_congr e] using hP
  · intro J _
    exact exists_hilbert_numerator_no_variables (by simp) J
  · intro α _ ih J hJ
    let f : MvPolynomial (Option α) k := MvPolynomial.X none
    have hf : f.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X k none
    obtain ⟨m, hm⟩ := PiExponentJets.W06.exists_colon_pow_stable J f
    have hstable : iteratedColon J f (m+1) = iteratedColon J f m := by
      simpa only [iteratedColon_eq_colon_power] using hm
    let Jlower : ℕ → Ideal (MvPolynomial (Option α) k) :=
      fun j => Ideal.span {f} ⊔ iteratedColon J f j
    have hlower : ∀ j, (Jlower j).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Option α) k) := by
      intro j
      apply Ideal.IsHomogeneous.sup
      · apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule (Option α) k)
        intro g hg
        obtain rfl := Set.mem_singleton_iff.mp hg
        exact ⟨1, hf⟩
      · exact iteratedColon_homogeneous J hJ f hf j
    have hX : ∀ j, MvPolynomial.X none ∈ Jlower j := by
      intro j
      have hinc : Ideal.span {f} ≤ Jlower j := le_sup_left
      exact hinc (Ideal.subset_span (Set.mem_singleton f))
    choose P hP using fun j => ih (PiExponentSiegel.W08.coordinateImageIdeal (Jlower j))
      (PiExponentSiegel.W08.coordinateImageIdeal_homogeneous (Jlower j) (hlower j))
    have hseries : ∀ j, sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon J f j) =
        (P j : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card α)).val := by
      intro j
      rw [show Ideal.span {f} ⊔ iteratedColon J f j = Jlower j from rfl,
        sectionHilbertSeries_coordinate (Jlower j) (hX j)]
      exact hP j
    refine ⟨colonHilbertNumerator P m, ?_⟩
    simpa only [Fintype.card_option] using
      stabilized_colon_polynomial_numerator J hJ f hf m (Fintype.card α) hstable P hseries

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousHilbertPolynomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type v} [Field k]

theorem exists_homogeneous_hilbert_polynomial
    (σ : Type u) [Fintype σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ) := by
  obtain ⟨P, hP⟩ := exists_homogeneous_hilbert_numerator σ I hI
  refine ⟨Polynomial.hilbertPoly (P.map (Int.castRingHom ℚ)) (Fintype.card σ),
    (P.map (Int.castRingHom ℚ)).natDegree, ?_⟩
  intro n hn
  rw [← coeff_rationalSectionHilbertSeries, rational_hilbert_numerator I P hP]
  exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HilbertPolynomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

noncomputable def actualHP (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) : Polynomial ℚ :=
  (exists_homogeneous_hilbert_polynomial σ I hI).choose

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_HilbertMultiplicityFiltration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

noncomputable def actualMultiplicity (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (d : ℕ) : ℚ :=
  (actualHP I hI).coeff d * (d.factorial : ℚ)

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPowerFiltration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X : Scheme.{0}}

instance closedMap_mono {I J : X.IdealSheafData} (h : I ≤ J) : Mono (closedMap h) := by
  have : Mono (closedMap h ≫ closedInclusion J) := by rw [closedMap_inclusion]; infer_instance
  exact mono_of_mono (closedMap h) (closedInclusion J)

def powerMap (I : X.IdealSheafData) (n : ℕ) : closedModule (I^(n+1)) ⟶ closedModule (I^n) :=
  closedMap (fun _U => Ideal.pow_le_pow_right (Nat.le_succ n))

instance powerMap_mono (I : X.IdealSheafData) (n : ℕ) : Mono (powerMap I n) :=
  closedMap_mono _

def powerLayer (I : X.IdealSheafData) (n : ℕ) : X.Modules := cokernel (powerMap I n)

def powerSequence (I : X.IdealSheafData) (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (powerMap I n) (cokernel.π (powerMap I n)) (cokernel.condition _)

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPowerAnnihilator
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

lemma multiplyToNextPower_powerMap (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    multiplyToNextPower I n r hr ≫ powerMap I n = r • 𝟙 (closedModule (I^n)) := by
  apply (cancel_mono (closedInclusion (I^n))).mp
  rw [Category.assoc, show powerMap I n ≫ closedInclusion (I^n) =
    closedInclusion (I^(n+1)) from closedMap_inclusion _]
  rw [multiplyToNextPower_inclusion]
  ext U x
  change restrictScalar X U r * (show Γ(X,U) from (closedInclusion (I^n)).app U x) =
    (closedInclusion (I^n)).app U (restrictScalar X U r • x)
  exact ((closedInclusion (I^n)).app_smul _ x).symm

theorem powerLayer_smul_id_eq_zero (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    r • 𝟙 (powerLayer I n) = 0 := by
  apply (cancel_epi (cokernel.π (powerMap I n))).mp
  have h : (r • 𝟙 (closedModule (I^n))) ≫ cokernel.π (powerMap I n) = 0 := by
    rw [← multiplyToNextPower_powerMap I n r hr, Category.assoc, cokernel.condition,
      Limits.comp_zero]
  calc
    _ = (r • 𝟙 (closedModule (I^n))) ≫ cokernel.π (powerMap I n) := by
      ext U x
      exact ((cokernel.π (powerMap I n)).app_smul _ x).symm
    _ = 0 := h
    _ = _ := Limits.comp_zero.symm
end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPowerDescent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def descendedPowerLayer (I : X.IdealSheafData) (n : ℕ) : I.subscheme.Modules :=
  (Scheme.Modules.pullback I.subschemeι).obj (powerLayer I n)

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialPrimeDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W24
open PiExponentSiegel.W23 PiExponentSiegelAux.W09
open PiExponentJets.PolynomialLocalResidueResolution

section Equivalence
variable {A B : Type*} [CommRing A] [CommRing B]

attribute [local instance] OAI.PiExponentJets.W24.imagePrime_isPrime
def ringEquiv_localQuotient (e : A ≃+* B) (P Q : Ideal A) [Q.IsPrime] :
    (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) ≃+*
      (Localization.AtPrime (Q.map e.toRingHom) ⧸
        parameterLocalizedIdeal (P.map e.toRingHom) (Q.map e.toRingHom)) :=
  Ideal.quotientEquiv _ _ (atPrimeEquivOfRingEquiv e Q)
    (ringEquiv_localizedIdeal_map e P Q).symm

end Equivalence


end PiExponentJets.W24

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RetainedIntersectionCycles
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

namespace ProjectiveComponent

variable {k : Type u} {σ : Type v} [Field k]

variable [Fintype σ]

noncomputable def hilbertDegree (P : ProjectiveComponent k σ) : ℚ :=
  actualMultiplicity P.val P.homogeneous (actualHP P.val P.homogeneous).natDegree

end ProjectiveComponent

namespace RetainedPrimeCycle

variable {k : Type u} {σ : Type v} [Field k] [Fintype σ]

noncomputable def degree (C : RetainedPrimeCycle.{u,v,w} k σ) : ℚ :=
  ∑ a, (C.coefficient a : ℚ) * (C.component a).hilbertDegree

end RetainedPrimeCycle
end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularCutHistory
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

structure RegularPrefixCut
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (S : HomogeneousPolynomialIdeal k σ) where
  polynomial : MvPolynomial σ k
  polynomialDegree : ℕ
  positiveDegree : 0 < polynomialDegree
  homogeneous : polynomial.IsHomogeneous polynomialDegree
  avoidsParent : ∀ P : RetainedMinimalPrime S.val T, polynomial ∉ P.val
  dimensionIndex : ℕ
  parentDegree : ∀ P : RetainedMinimalPrime S.val T,
    (actualHP P.val (RetainedMinimalPrime.toComponent S.property v hv P).homogeneous).natDegree =
      dimensionIndex+1
  localDimension : ∀ Q : RetainedMinimalPrime (S.val ⊔ Ideal.span {polynomial}) T,
    ringKrullDim (Localization.AtPrime Q.val ⧸
      S.val.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val))) = 1
  regularAtChild : ∀ Q : RetainedMinimalPrime (S.val ⊔ Ideal.span {polynomial}) T,
    Function.Injective (W28.LocalIntersection.quotientMul
      (S.val.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val)))
      (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val) polynomial))

namespace RegularPrefixCut

variable {T : Ideal (MvPolynomial σ k)} {v : σ} {hv : MvPolynomial.X v ∉ T}
  {S : HomogeneousPolynomialIdeal k σ}

noncomputable def next (F : RegularPrefixCut T v hv S) : HomogeneousPolynomialIdeal k σ :=
  ⟨S.val ⊔ Ideal.span {F.polynomial}, cut_ideal_homogeneous S.val S.property F.polynomial F.homogeneous⟩

end RegularPrefixCut

inductive ActualRegularCutHistory
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (S₀ : HomogeneousPolynomialIdeal k σ) : HomogeneousPolynomialIdeal k σ → ℕ → Prop
  | nil : ActualRegularCutHistory T v hv S₀ S₀ 1
  | step {S : HomogeneousPolynomialIdeal k σ} {e : ℕ}
      (previous : ActualRegularCutHistory T v hv S₀ S e)
      (F : RegularPrefixCut T v hv S) :
      ActualRegularCutHistory T v hv S₀ F.next (e * F.polynomialDegree)

end PiExponentJets.W22

end OAI
end


