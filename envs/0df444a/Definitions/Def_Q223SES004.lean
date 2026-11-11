-- Prove2me | Definitions.Def_Q223SES004
-- name    : Q223SES004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:51:14.967662+00:00
-- url     : https://prove2.me/theorems/adb28812-1fe2-499d-9333-e1d53179c28e
-- title:
--   Definitions bundle Q223SES004 of the split of OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 221 declarations of OpenAI's Lean: 81 definitions, 16 instances and 124 theorems. The definitions and types are `OAI.MaximalSeshadri.AlgebraicJets.binaryJetEquiv`, `OAI.MaximalSeshadri.AlgebraicJets.formalTrunc`, `OAI.MaximalSeshadri.AlgebraicJets.jetAugment`, `OAI.MaximalSeshadri.AlgebraicJets.mapJetAlgebra`, `OAI.MaximalSeshadri.AlgebraicJets.polynomialJetEquiv`, `OAI.MaximalSeshadri.AlgebraicJets.polynomialJetEquivAt`, `OAI.MaximalSeshadri.AlgebraicJets.regularTaylorCoeffs`, `OAI.MaximalSeshadri.AlgebraicJets.specializeTaylor`, `OAI.MaximalSeshadri.AnalyticCoordinates.analyticFirst`, `OAI.MaximalSeshadri.AnalyticCoordinates.analyticFormal`, `OAI.MaximalSeshadri.AnalyticCoordinates.analyticSecond`, `OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor`, `OAI.MaximalSeshadri.AnalyticCoordinates.bivariateTaylor`, `OAI.MaximalSeshadri.BertiniIntegral.mvCoeffDerivation`, `OAI.MaximalSeshadri.BertiniIntegral.mvParameterDerivation`, `OAI.MaximalSeshadri.BlowupGluing.cover`, `OAI.MaximalSeshadri.BlowupGluing.diagram`, `OAI.MaximalSeshadri.BlowupGluing.diagramMap`, `OAI.MaximalSeshadri.BlowupGluing.gluing`, `OAI.MaximalSeshadri.BlowupGluing.localProjection`, `OAI.MaximalSeshadri.BlowupGluing.localScheme`, `OAI.MaximalSeshadri.BlowupGluing.projection`, `OAI.MaximalSeshadri.BlowupGluing.scheme`, `OAI.MaximalSeshadri.BlowupGluing.transition`, `OAI.MaximalSeshadri.ClosedPushforward.cohomologyEquiv`, `OAI.MaximalSeshadri.ClosedPushforward.cohomologyLinearMap`, `OAI.MaximalSeshadri.ClosedPushforward.cohomologyMap`, `OAI.MaximalSeshadri.FinitePointBlowup.pointCover`, `OAI.MaximalSeshadri.Frames.endUnit`, `OAI.MaximalSeshadri.Frames.frameChange`, `OAI.MaximalSeshadri.Frames.openSectionEquiv`, `OAI.MaximalSeshadri.Frames.restrictEndIso`, `OAI.MaximalSeshadri.Frames.restrictFrame`, `OAI.MaximalSeshadri.Frames.restrictSection`, `OAI.MaximalSeshadri.FreeOpenUnit.freeTopIso`, `OAI.MaximalSeshadri.Geometry.BaseSections.cohomologyZero`, `OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseEquiv`, `OAI.MaximalSeshadri.Geometry.BaseSections.globalSectionsLinear`, `OAI.MaximalSeshadri.Geometry.BaseSections.homChart`, `OAI.MaximalSeshadri.Geometry.BaseSections.planeBoundariesFreeHomGroup` and 41 more.
--
--   **Sources.** They come from these modules of lean/OAI/AlgebraicGeometry, in whole or in part: `Seshadri_Analytic_CoordinateJets`, `Seshadri_Analytic_FormalSeries`, `Seshadri_Bertini_Derivations`, `Seshadri_Blowup_BlowupIntegral`, `Seshadri_Blowup_BlowupProper`, `Seshadri_Blowup_ExceptionalIdeal`, `Seshadri_Blowup_FiniteCenters`, `Seshadri_Blowup_Gluing`, `Seshadri_Blowup_LocalEquations`, `Seshadri_Blowup_LocalUniversal`, `Seshadri_Blowup_PlaneCharts`, `Seshadri_Blowup_PrincipalCharts`, `Seshadri_Blowup_ReesAlgebra`, `Seshadri_Blowup_ReesCharts`, `Seshadri_Blowup_Uniqueness`, `Seshadri_Cohomology_AffineVanishing`, `Seshadri_Cohomology_ClosedPushforwardCohomology`, `Seshadri_Cohomology_CurveH0Finite`, `Seshadri_Cohomology_FiniteCover`, `Seshadri_Cohomology_PlanePairToric`, `Seshadri_Cohomology_PlaneRelationCycles`, `Seshadri_Cohomology_RestrictionComparison`, `Seshadri_Cohomology_SheafExactness`, `Seshadri_Cohomology_SurfaceCech`, `Seshadri_Cohomology_TripleComplex`, `Seshadri_Cohomology_TripleEvaluation`, `Seshadri_Divisors_LinearSections`, `Seshadri_Divisors_OpenSectionsLinear`, `Seshadri_Divisors_SectionChart`, `Seshadri_Divisors_SectionTransport`, `Seshadri_Geometry_PlaneBoundaries`, `Seshadri_Geometry_PlaneCoordinates`, `Seshadri_Jets_BinaryJetDimension`, `Seshadri_Jets_FormalEtale`, `Seshadri_Jets_NodalTaylor`, `Seshadri_Jets_PolynomialJets`, `Seshadri_Projective_SectionMaps`, `Seshadri_Sheaves_CartierModule`, `Seshadri_Sheaves_ClosedPushforwardEuler`, `Seshadri_Sheaves_Frames`, `Seshadri_Sheaves_PlaneProjectionModule`, `Seshadri_Sheaves_SectionOpens`, `Seshadri_Sheaves_Sections`, `Seshadri_Sheaves_TensorFrames`.
--
--   **Imports.** It imports the published bundle `Def_MaximalSeshadriConstants`; the bundles `Q223SES000`, `Q223SES001` and `Q223SES002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q223SES007` and `Q223SES008`; the statements `OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor_exactJets_s01`, `OAI.MaximalSeshadri.Geometry.LineBundle.power_extension_ratio_s01`, `OAI.MaximalSeshadri.Geometry.local_powerSection_coefficient_s01`, `OAI_MaximalSeshadri_Geometry_nodal_ideal_branch_sum_le_degree` and `OAI.MaximalSeshadri.Geometry.nodal_ideal_branch_sum_le_degree_s01`; the proofs of `OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor_exactJets_s01`, `OAI_MaximalSeshadri_BertiniIntegral_etale_generic_hyperplane_section`, `OAI.MaximalSeshadri.BertiniIntegral.etale_generic_hyperplane_section_s01`, `OAI_MaximalSeshadri_Geometry_IntegralCurve_euler_pushforward`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.euler_pushforward_s01`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.invertible_ideal_s01`, `OAI.MaximalSeshadri.Geometry.exists_open_jet_configuration_s01`, `OAI.MaximalSeshadri.Geometry.local_powerSection_coefficient_s01` and `OAI.MaximalSeshadri.Geometry.surface_configuration_outside_countable_closed_s01`.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/AlgebraicGeometry at commit adc7f12

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES000
import Definitions.Def_Q223SES001
import Definitions.Def_Q223SES002

section
-- module Solutions.Q223_SES.Seshadri_Analytic_FormalSeries
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open PowerSeries Filter

local instance instHasAntidiagonalExponent_2_r7a40b1_1 : Finset.HasAntidiagonal Exponent :=
  Finset.HasAntidiagonal.antidiagonalOfLocallyFinite
lemma biCoeff_injective : Function.Injective biCoeff := by
  intro f g h
  apply PowerSeries.ext
  intro b
  apply PowerSeries.ext
  intro a
  exact congrFun h (a,b)

lemma biCoeff_mul (f g : BiSeries) (e : Exponent) :
    biCoeff (f * g) e = coeffConvolution (biCoeff f) (biCoeff g) e := by
  classical
  simp only [biCoeff, coeff_mul, map_sum]
  rw [← Finset.sum_product _ _
    (fun ij : (ℕ × ℕ) × (ℕ × ℕ) =>
      (coeff ij.2.1 (coeff ij.1.1 f)) * (coeff ij.2.2 (coeff ij.1.2 g)))]
  apply Finset.sum_bij (fun ij _ => ((ij.2.1,ij.1.1),(ij.2.2,ij.1.2)))
  · intro ij hij
    rcases Finset.mem_product.mp hij with ⟨h₁,h₂⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at h₁ h₂ ⊢
    exact Prod.ext h₂ h₁
  · intro i hi j hj he
    have h₁ := congrArg (fun p : Exponent × Exponent => (p.1.2,p.2.2)) he
    have h₂ := congrArg (fun p : Exponent × Exponent => (p.1.1,p.2.1)) he
    exact Prod.ext (by simpa using h₁) (by simpa using h₂)
  · intro p hp
    refine ⟨((p.1.2,p.2.2),(p.1.1,p.2.1)), ?_, rfl⟩
    rw [Finset.mem_product]
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    refine ⟨congrArg Prod.snd hp, ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    exact congrArg Prod.fst hp
  · intro ij hij
    rfl

def analyticFormal : analyticFunctionAlgebra →ₐ[ℂ] BiSeries where
  toFun f := biSeries (analyticCoefficients f)
  map_one' := by
    apply biCoeff_injective
    ext e
    have h := analyticCoefficients_const 1
    simp only [map_one] at h
    simp only [biCoeff_biSeries, h]
    rcases e with ⟨a,b⟩
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [biCoeff, ha, hb]
  map_mul' f g := by
    apply biCoeff_injective
    ext e
    simp only [biCoeff_biSeries, analyticCoefficients_mul, biCoeff_mul]
    congr 1 <;> ext a <;> exact biCoeff_biSeries _ _ |>.symm
  map_zero' := by
    apply biCoeff_injective
    ext e
    have h := analyticCoefficients_const 0
    simp only [map_zero, ite_self] at h
    simp [h, biCoeff, biSeries]
  map_add' f g := by
    apply biCoeff_injective
    ext e
    simp [analyticCoefficients_add, biCoeff, biSeries]
  commutes' a := by
    apply biCoeff_injective
    ext e
    simp only [biCoeff_biSeries, analyticCoefficients_const]
    rw [PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply]
    simp only [Algebra.algebraMap_self]
    rcases e with ⟨k,b⟩
    by_cases hk : k = 0 <;> by_cases hb : b = 0 <;> simp [biCoeff, coeff_C, hk, hb]

end
end MaximalSeshadri.AnalyticCoordinates


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_PolynomialJets
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

lemma polynomialJetCoeffs_surjective [Finite σ] (n : ℕ) :
    Function.Surjective (polynomialJetCoeffs (σ := σ) (R := R) n) := by
  classical
  let : Fintype (JetIndex σ n) := Fintype.ofFinite _
  intro a
  refine ⟨∑ d : JetIndex σ n, monomial d.val (a d), ?_⟩
  ext e
  change (∑ index : JetIndex σ n, monomial index.val (a index)).coeff e.val = a e
  simp only [coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro d _ hde
    rw [ite_eq_right (fun equality => hde (Subtype.ext equality))]
  · simp

def polynomialJetEquiv [Finite σ] (n : ℕ) :
    (MvPolynomial σ R ⧸ (idealOfVars σ R) ^ n) ≃ₗ[R] (JetIndex σ n → R) := by
  let e := LinearMap.quotKerEquivOfSurjective
    (polynomialJetCoeffs (σ := σ) (R := R) n) (polynomialJetCoeffs_surjective n)
  exact (Submodule.quotEquivOfEq _ _ (polynomialJetCoeffs_ker n).symm).trans e

end

noncomputable section
open MvPolynomial
variable {σ R : Type*} [CommRing R]

lemma polynomialJetCoeffsAt_surjective [Finite σ] (x : σ → R) (n : ℕ) :
    Function.Surjective (polynomialJetCoeffsAt x n) :=
  (polynomialJetCoeffs_surjective n).comp (polynomialTranslate x).surjective

def polynomialJetEquivAt [Finite σ] (x : σ → R) (n : ℕ) :
    (MvPolynomial σ R ⧸ (RingHom.ker (eval x)) ^ n) ≃ₗ[R] (JetIndex σ n → R) := by
  let e := LinearMap.quotKerEquivOfSurjective
    (polynomialJetCoeffsAt x n) (polynomialJetCoeffsAt_surjective x n)
  exact (Submodule.quotEquivOfEq _ _ (polynomialJetCoeffsAt_ker x n).symm).trans e

@[simp] lemma polynomialJetEquivAt_mk [Finite σ] (x : σ → R) (n : ℕ)
    (p : MvPolynomial σ R) (d : JetIndex σ n) :
    polynomialJetEquivAt x n (Ideal.Quotient.mk _ p) d =
      (polynomialTranslate x p).coeff d.val := rfl

@[simp] lemma polynomialJetEquiv_mk [Finite σ] (n : ℕ)
    (p : MvPolynomial σ R) (d : JetIndex σ n) :
    polynomialJetEquiv (σ := σ) (R := R) n (Ideal.Quotient.mk _ p) d =
      p.coeff d.val := rfl

end

noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

def jetAugment (n : ℕ) (hn : 0 < n) : JetAlgebra σ R n →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (aeval (fun _ : σ => (0 : R))) (by
    intro p hp
    have hc := (mem_pow_idealOfVars_iff' n p).mp hp 0 (by simpa using hn)
    simpa [aeval_def, eval_zero, constantCoeff_eq] using hc)

@[simp] lemma jetAugment_mk (n : ℕ) (hn : 0 < n) (p : MvPolynomial σ R) :
    jetAugment n hn (Ideal.Quotient.mk _ p) = constantCoeff p := by
  change (aeval (fun _ : σ => (0 : R))) p = _
  simp [aeval_def]

end

noncomputable section
open MvPolynomial

variable {σ F R S : Type*} [CommRing F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S]

def mapJetAlgebra (φ : R →ₐ[F] S) (n : ℕ) :
    JetAlgebra σ R n →ₐ[F] JetAlgebra σ S n :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom φ) (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    change ((idealOfVars σ R).map (MvPolynomial.map φ.toRingHom)) ^ n ≤ _
    rw [map_idealOfVars])

@[simp] lemma mapJetAlgebra_mk (φ : R →ₐ[F] S) (n : ℕ) (p : MvPolynomial σ R) :
    mapJetAlgebra (σ := σ) φ n (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map φ.toRingHom p) := rfl

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SheafExactness
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.TildeFlasque
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AffineDenominators AdicInjective InjectiveRange
universe u
variable {R : CommRingCat.{u}} [IsNoetherianRing R]
variable (M : (Spec R).Modules)

theorem top_surjective (hloc : IsLocalizing (modulesSpecToSheaf.obj M))
    [Module.Injective R Γ(M,⊤)] (U : (Spec R).Opens) :
    Function.Surjective (res U ⊤ le_top (M := M)) := by
  have hU : IsCompact (U : Set (Spec R)) := NoetherianSpace.isCompact _
  obtain ⟨ι, hι, g, hg⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact U hU
  let := hι
  let I : Ideal R := Ideal.span (Set.range g)
  let r := res U ⊤ le_top (M := M)
  have hk : r.ker = adicTorsion I Γ(M,⊤) := by
    ext s
    change r s = 0 ↔ s ∈ adicTorsion I Γ(M,⊤)
    rw [mem_adicTorsion]
    exact ⟨kernel_is_torsion g U hg hloc s, torsion_in_kernel g U hg s⟩
  have hi : Module.Injective R (adicTorsion I Γ(M,⊤)) := adicTorsion_injective I Γ(M,⊤)
  let : Module.Injective R r.ker := Module.Baer.injective
    (Module.Baer.of_equiv (LinearEquiv.ofEq _ _ hk.symm) (Module.Baer.of_injective hi))
  apply surjective_of_torsion_cokernel I r
  · exact fun s => cokernel_is_torsion g U hg hU hloc s
  · exact fun s => torsion_free g U hg s

theorem flasque_of_injective_global (hloc : IsLocalizing (modulesSpecToSheaf.obj M))
    [Module.Injective R Γ(M,⊤)] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨t,ht⟩ := top_surjective M hloc V.unop s
    refine ⟨res U.unop ⊤ le_top t, ?_⟩
    change res V.unop U.unop (leOfHom i.unop) (res U.unop ⊤ le_top t) = s
    rw [res_comp]
    exact ht

instance tilde_injective_isFlasque (N : ModuleCat.{u} R) [Module.Injective R N] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde N)) := by
  let : Module.Injective R Γ(tilde N,⊤) := Module.Baer.injective
    (Module.Baer.of_equiv (asIso (tilde.toOpen N ⊤)).toLinearEquiv
      (Module.Baer.of_injective inferInstance))
  exact flasque_of_injective_global (tilde N) (isLocalizing_tilde N)

end
end MaximalSeshadri.TildeFlasque


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_AffineVanishing
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.AffineCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open FlasqueCohomology
universe u
variable {R : CommRingCat.{u}}

attribute [local instance] OAI.MaximalSeshadri.AffineCohomology.affineHasExt
theorem tilde_ext_zero [IsNoetherianRing R] (n : ℕ) (M : ModuleCat.{u} R)
    (x : Ext.{u+1} (C := (Spec R).Modules)
      (structureSheafUnit (Spec R)) (tilde M) (n+1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let T : ShortComplex (Spec R).Modules :=
      { X₁ := tilde S.X₁
        X₂ := tilde S.X₂
        X₃ := tilde S.X₃
        f := tilde.map S.f
        g := tilde.map S.g
        zero := (S.map (tilde.functor R)).zero }
    have hT : T.ShortExact := hS.map (tilde.functor R)
    let : Injective S.X₂ := (inferInstance : Injective (Injective.under M))
    let : Module.Injective R S.X₂ := Module.injective_module_of_injective_object R S.X₂
    obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ _ hT x
      (flasque_ext_zero (Spec R).ringCatSheaf 0 (tilde S.X₂) _) rfl
    obtain ⟨f,rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    obtain ⟨g,rfl⟩ := globalHom_tilde_surjective S.g f
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      show (Ext.mk₀ (tilde.map S.g)).comp hT.extClass rfl = 0 from hT.comp_extClass,
      Ext.comp_zero] at hy
    exact hy.symm
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let T : ShortComplex (Spec R).Modules :=
      { X₁ := tilde S.X₁
        X₂ := tilde S.X₂
        X₃ := tilde S.X₃
        f := tilde.map S.f
        g := tilde.map S.g
        zero := (S.map (tilde.functor R)).zero }
    have hT : T.ShortExact := hS.map (tilde.functor R)
    let : Injective S.X₂ := (inferInstance : Injective (Injective.under M))
    let : Module.Injective R S.X₂ := Module.injective_module_of_injective_object R S.X₂
    obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ _ hT x
      (flasque_ext_zero (Spec R).ringCatSheaf (n+1) (tilde S.X₂) _) rfl
    rw [ih S.X₃ y, Ext.zero_comp] at hy
    exact hy.symm

theorem quasicoherent_ext_zero [IsNoetherianRing R] (n : ℕ) (M : (Spec R).Modules)
    [M.IsQuasicoherent]
    (x : Ext.{u+1} (C := (Spec R).Modules)
      (structureSheafUnit (Spec R)) M (n+1)) : x = 0 := by
  let e := asIso M.fromTildeΓ
  have hx := tilde_ext_zero n _ (x.comp (Ext.mk₀ e.inv) (add_zero _))
  have h := congrArg (fun y => y.comp (Ext.mk₀ e.hom) (add_zero (n+1))) hx
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    e.inv_hom_id, Ext.comp_mk₀_id, Ext.zero_comp] using h

end
end MaximalSeshadri.AffineCohomology

namespace MaximalSeshadri.RestrictionExact
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance restriction_preservesMonomorphisms :
    (Scheme.Modules.restrictFunctor f).PreservesMonomorphisms where
  preserves g _ := restriction_mono f g

instance restriction_preservesHomology :
    (Scheme.Modules.restrictFunctor f).PreservesHomology :=
  (Scheme.Modules.restrictFunctor f).preservesHomology_of_preservesMonos_and_cokernels

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
  (Scheme.Modules.restrictFunctor f).preservesFiniteLimits_of_preservesHomology

end
end MaximalSeshadri.RestrictionExact

namespace MaximalSeshadri.AffineSchemeCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open Scheme.Modules
universe u

attribute [local instance] OAI.MaximalSeshadri.AffineSchemeCohomology.hasExtScheme
theorem affine_ext_zero (X : Scheme.{u}) [IsAffine X] [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Ext.{u+1} (C := X.Modules)
      (AffineCohomology.structureSheafUnit X) M (n+1)) : x = 0 := by
  let : IsNoetherianRing Γ(X, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let E := restrictionEquivalence X.isoSpec.symm
  let F := E.functor
  let : F.Additive := RestrictionExact.restriction_additive _
  let : EnoughInjectives X.Modules := ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  let e : F.obj (AffineCohomology.structureSheafUnit X) ≅
      AffineCohomology.structureSheafUnit (Spec Γ(X, ⊤)) :=
    restrictUnitIso X.isoSpec.inv
  let z : Ext.{u+1} (F.obj (AffineCohomology.structureSheafUnit X)) (F.obj M) (n+1) :=
    x.mapExactFunctor F
  have hz : z = 0 := by
    have hw : (Ext.mk₀ e.inv).comp z (zero_add _) = 0 :=
      AffineCohomology.quasicoherent_ext_zero n (M.restrict X.isoSpec.inv)
        ((Ext.mk₀ e.inv).comp z (zero_add _))
    have h := congrArg (fun y => (Ext.mk₀ e.hom).comp y (zero_add (n+1))) hw
    simpa only [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp,
      Ext.comp_zero] using h
  have hb : Function.Injective (F.mapExtAddHom (AffineCohomology.structureSheafUnit X) M (n+1) :
      Ext.{u+1} (C := X.Modules) (AffineCohomology.structureSheafUnit X) M (n+1) →
      Ext.{u+1} (F.obj (AffineCohomology.structureSheafUnit X)) (F.obj M) (n+1)) :=
    (F.mapExt_bijective_of_preservesInjectiveObjects _ _ (n+1)).injective
  apply hb
  simpa only [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_zero] using hz

end
end MaximalSeshadri.AffineSchemeCohomology


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_CartierModule
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.IdealModule

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

def frameOnRange (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f]
    (e : M.restrict f ≅ unit X) : M.restrict f.opensRange.ι ≅ unit f.opensRange.toScheme :=
  ((Scheme.Modules.restrictFunctorCongr f.isoOpensRange_inv_comp).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp f.isoOpensRange.inv f).app M ≪≫
    (Scheme.Modules.restrictFunctor f.isoOpensRange.inv).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso f.isoOpensRange.inv

end
end MaximalSeshadri.IdealModule

namespace MaximalSeshadri.IdealPullback

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma specIdeal_comap (I : Ideal R) (f : R →+* S) :
    (specIdeal I).comap (Spec.map (CommRingCat.ofHom f)) = specIdeal (I.map f) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [comap_top, specIdeal_top, specIdeal_top, Ideal.map_map, Ideal.map_map]
  congr 1
  exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm

end

end MaximalSeshadri.IdealPullback

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_FormalEtale
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets

noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Field F] [CommRing S] [Algebra F S]

def specializeTaylor (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n) (ρ : S →ₐ[F] F) :
    S →ₐ[F] JetAlgebra σ F n :=
  (mapJetAlgebra ρ n).comp τ

end

noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]

def regularTaylorCoeffs (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n) :
    S →ₗ[F] (JetIndex σ n → S) :=
  ((polynomialJetEquiv (σ := σ) (R := S) n).toLinearMap.restrictScalars F).comp τ.toLinearMap

end

end MaximalSeshadri.AlgebraicJets
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_CoordinateJets
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology
open Filter PowerSeries
open MaximalSeshadri.FormalCoordinates

def analyticFirst : analyticFunctionAlgebra := ⟨Prod.fst, analyticAt_fst⟩
def analyticSecond : analyticFunctionAlgebra := ⟨Prod.snd, analyticAt_snd⟩

variable {S : Type*} [CommRing S] [Algebra ℂ S]

def analyticTaylor (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) :
    S →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ :=
  (binaryEquiv ℂ).symm.toAlgHom.comp (analyticFormal.comp (analyticPullback q hq))

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

def formalTrunc (n : ℕ) : MvPowerSeries σ F →ₐ[F] JetAlgebra σ F n :=
  (MvPowerSeries.truncTotalAlgHom σ F n).restrictScalars F

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_Derivations
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def mvCoeffDerivation {K A σ : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (D : Derivation K A A) : Derivation K (MvPolynomial σ A) (MvPolynomial σ A) where
  toFun := AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom
  map_add' p q := by ext m; simp
  map_smul' k p := by ext m; simp
  map_one_eq_zero' := by
    ext m
    simp [MvPolynomial.coeff_one, apply_ite D]
  leibniz' p q := by
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq =>
      simp only [add_mul, map_add, add_smul, smul_add, hp, hq]
      abel
    | monomial m a =>
      induction q using MvPolynomial.induction_on' with
      | add p q hp hq =>
        simp only [mul_add, map_add, add_smul, smul_add, hp, hq]
        abel
      | monomial n b =>
        have hm (u : σ →₀ ℕ) (c : A) :
            AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom (MvPolynomial.monomial u c) =
              MvPolynomial.monomial u (D c) := by
          ext t
          simp [MvPolynomial.coeff_monomial, apply_ite D]
        change AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom
            (MvPolynomial.monomial m a * MvPolynomial.monomial n b) =
          MvPolynomial.monomial m a *
            AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom (MvPolynomial.monomial n b) +
          MvPolynomial.monomial n b *
            AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom (MvPolynomial.monomial m a)
        rw [MvPolynomial.monomial_mul_monomial, hm, hm, hm, D.leibniz]
        simp only [smul_eq_mul, map_add, MvPolynomial.monomial_mul_monomial, add_comm n m]

@[simp] theorem mvCoeffDerivation_coeff {K A σ : Type*} [CommRing K] [CommRing A]
    [Algebra K A] (D : Derivation K A A) (p : MvPolynomial σ A) (m) :
    (mvCoeffDerivation D p).coeff m = D (p.coeff m) := rfl

@[simp] theorem mvCoeffDerivation_C {K A σ : Type*} [CommRing K] [CommRing A]
    [Algebra K A] (D : Derivation K A A) (a : A) :
    mvCoeffDerivation (σ := σ) D (MvPolynomial.C a) = MvPolynomial.C (D a) := by
  ext m
  simp [MvPolynomial.coeff_C, apply_ite D]

@[simp] theorem mvCoeffDerivation_X {K A σ : Type*} [CommRing K] [CommRing A]
    [Algebra K A] (D : Derivation K A A) (i : σ) :
    mvCoeffDerivation D (MvPolynomial.X i) = 0 := by
  ext m
  simp [MvPolynomial.coeff_X, apply_ite D]

@[simp] theorem mvCoeffDerivation_algebraMap {K A σ : Type*}
    [CommRing K] [CommRing A] [Algebra K A] (D : Derivation K A A)
    (p : MvPolynomial σ K) :
    mvCoeffDerivation D (algebraMap (MvPolynomial σ K) (MvPolynomial σ A) p) = 0 := by
  ext m
  simp [MvPolynomial.coeff_map]

def mvParameterDerivation {K A σ : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (D : Derivation K A A) :
    Derivation (MvPolynomial σ K) (MvPolynomial σ A) (MvPolynomial σ A) where
  toFun := mvCoeffDerivation D
  map_add' := map_add (mvCoeffDerivation D)
  map_smul' r p := by
    rw [Algebra.smul_def, (mvCoeffDerivation D).leibniz,
      mvCoeffDerivation_algebraMap, smul_zero, add_zero, Algebra.smul_def]
    rfl
  map_one_eq_zero' := (mvCoeffDerivation D).map_one_eq_zero
  leibniz' := (mvCoeffDerivation D).leibniz

end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_ReesAlgebra
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial DirectSum AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

instance instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat : IsScalarTower R (piece I 0) (reesAlgebra I) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := piece I 0) (A := reesAlgebra I)
    (fun _ => rfl)

instance instFiniteTypeSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNatOfIsNoetherianRing [IsNoetherianRing R] : Algebra.FiniteType (piece I 0) (reesAlgebra I) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R (piece I 0) (reesAlgebra I)

instance projection_proper [IsNoetherianRing R] : IsProper (projection I) := by
  have hP : IsProper (Proj.toSpecZero (piece I)) := inferInstance
  have hS : IsIso (Spec.map (zeroIso I).hom) := inferInstance
  have hQ : IsProper (Spec.map (zeroIso I).hom) := by infer_instance
  exact MorphismProperty.comp_mem (@IsProper) _ _ hP hQ

end

noncomputable section
open Polynomial DirectSum AlgebraicGeometry CategoryTheory HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def ratio (a b : I) : chart I a :=
  HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) 1
    (generator I b) (by simpa using generator_mem I b)

lemma chartMap_ratio (a b : I) :
    chartMap I a (ratio I a b) =
      IsLocalization.mk' (M := Submonoid.powers a.val) (Localization.Away a.val)
        b.val ⟨a.val, ⟨1, pow_one _⟩⟩ := by
  simp only [ratio, chartMap_mk, evaluation_generator, pow_one]

lemma base_mul_ratio (a b : I) :
    chartBase I a a.val * ratio I a b = chartBase I a b.val := by
  apply chartMap_injective I a
  rw [map_mul, chartMap_base, chartMap_ratio, chartMap_base]
  exact IsLocalization.mk'_spec' (M := Submonoid.powers a.val)
    (Localization.Away a.val) b.val ⟨a.val, ⟨1, pow_one _⟩⟩

lemma map_ideal_principal (a : I) :
    I.map (chartBase I a) = Ideal.span {chartBase I a a.val} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change chartBase I a b ∈ Ideal.span {chartBase I a a.val}
    rw [Ideal.mem_span_singleton]
    exact ⟨ratio I a ⟨b, hb⟩, (base_mul_ratio I a ⟨b, hb⟩).symm⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ a.property

lemma chart_generator_regular (a : I) :
    IsRegular (chartBase I a a.val) := by
  have hu : IsUnit (chartMap I a (chartBase I a a.val)) := by
    rw [chartMap_base]
    exact IsLocalization.map_units (Localization.Away a.val)
      (⟨a.val, 1, pow_one _⟩ : Submonoid.powers a.val)
  constructor
  · intro x y h
    apply chartMap_injective I a
    apply hu.isRegular.left
    simpa only [map_mul] using congrArg (chartMap I a) h
  · intro x y h
    apply chartMap_injective I a
    apply hu.isRegular.right
    simpa only [map_mul] using congrArg (chartMap I a) h

end
end MaximalSeshadri.ReesGrading


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_ReesCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial HomogeneousLocalization
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable {B : Type v} [CommRing B] (f : R →+* B)

def chartToLocalization : chart I a →+* Localization.Away (f a.val) :=
  (IsLocalization.map (M := Submonoid.powers a.val)
    (T := Submonoid.powers (f a.val)) (S := Localization.Away a.val)
    (Localization.Away (f a.val)) f (by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, (map_pow f _ _).symm⟩)).comp (chartMap I a)

lemma chartToLocalization_mk (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ piece I (n • (1 : ℕ))) :
    chartToLocalization I a f
      (HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) n p hp) =
      IsLocalization.mk' (M := Submonoid.powers (f a.val))
        (Localization.Away (f a.val)) (f (evaluation I p))
          ⟨(f a.val) ^ n, ⟨n, rfl⟩⟩ := by
  simp only [chartToLocalization, RingHom.comp_apply, chartMap_mk, IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  exact map_pow f _ _

lemma chartToLocalization_base (r : R) :
    chartToLocalization I a f (chartBase I a r) =
      algebraMap B (Localization.Away (f a.val)) (f r) := by
  simp [chartToLocalization, chartMap_base]

lemma chartToLocalization_range (hI : I.map f ≤ Ideal.span {f a.val})
    (x : chart I a) :
    ∃ b : B, algebraMap B (Localization.Away (f a.val)) b =
      chartToLocalization I a f x := by
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (generator_mem I a) x
  rw [chartToLocalization_mk]
  have hpn : p ∈ piece I n := by simpa using hp
  have he : evaluation I p = (p : R[X]).coeff n := evaluation_piece I ⟨p, hpn⟩
  obtain ⟨b, hb⟩ := coeff_power_dvd I a f hI n (p.property n)
  refine ⟨b, ?_⟩
  rw [he, hb]
  exact (IsLocalization.mk'_mul_cancel_left (M := Submonoid.powers (f a.val))
    (S := Localization.Away (f a.val)) b ⟨(f a.val) ^ n, ⟨n, rfl⟩⟩).symm

def chartLift (hI : I.map f ≤ Ideal.span {f a.val}) (hfa : IsRegular (f a.val)) :
    chart I a →+* B where
  toFun x := Classical.choose (chartToLocalization_range I a f hI x)
  map_zero' := localizationMap_injective I a f hfa (by
    rw [Classical.choose_spec (chartToLocalization_range I a f hI 0), map_zero, map_zero])
  map_one' := localizationMap_injective I a f hfa (by
    rw [Classical.choose_spec (chartToLocalization_range I a f hI 1), map_one, map_one])
  map_add' x y := localizationMap_injective I a f hfa (by
    rw [Classical.choose_spec (chartToLocalization_range I a f hI (x+y)), map_add,
      map_add, Classical.choose_spec (chartToLocalization_range I a f hI x),
      Classical.choose_spec (chartToLocalization_range I a f hI y)])
  map_mul' x y := localizationMap_injective I a f hfa (by
    rw [Classical.choose_spec (chartToLocalization_range I a f hI (x*y)), map_mul,
      map_mul, Classical.choose_spec (chartToLocalization_range I a f hI x),
      Classical.choose_spec (chartToLocalization_range I a f hI y)])

lemma chartLift_spec (hI : I.map f ≤ Ideal.span {f a.val}) (hfa : IsRegular (f a.val))
    (x : chart I a) :
    algebraMap B (Localization.Away (f a.val)) (chartLift I a f hI hfa x) =
      chartToLocalization I a f x :=
  Classical.choose_spec (chartToLocalization_range I a f hI x)

lemma chartLift_base (hI : I.map f ≤ Ideal.span {f a.val}) (hfa : IsRegular (f a.val))
    (r : R) : chartLift I a f hI hfa (chartBase I a r) = f r := by
  apply localizationMap_injective I a f hfa
  rw [chartLift_spec, chartToLocalization_base]

end

end MaximalSeshadri.ReesGrading


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_ExceptionalIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry

def lineBundleOfCover {X : Scheme} (M : X.Modules) (C : X.OpenCover)
    (h : ∀ i, Nonempty (M.restrict (C.f i) ≅ IdealModule.unit (C.X i))) : LineBundle X where
  sheaf := M
  locallyRankOne x := by
    refine ⟨(C.f (C.idx x)).opensRange, C.covers x, ?_⟩
    exact ⟨IdealModule.frameOnRange M (C.f (C.idx x)) (h (C.idx x)).some⟩

def idealLineBundle {X : Scheme} (I : X.IdealSheafData) (C : X.AffineOpenCover)
    (r : ∀ i, Γ(Spec (C.X i), ⊤))
    (h : ∀ i, (I.comap (C.f i)).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r i})
    (hr : ∀ i, IsLeftRegular (r i)) : LineBundle X :=
  lineBundleOfCover (IdealModule.closedModule I) C.openCover
    (fun i => by
      let : IsOpenImmersion (C.f i) := C.map_prop i
      exact IdealModule.frame_restriction I (C.f i) (r i) (h i) (hr i))

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.ReesGrading
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def exceptionalIdeal : (affineBlowup I).IdealSheafData :=
  (IdealPullback.specIdeal I).comap (projection I)

def chartEquation (a : I) : Γ(Spec ((chartCover I).X a), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (chart I a))).inv (chartBase I a a.val)

lemma exceptional_chart (a : I) :
    ((exceptionalIdeal I).comap ((chartCover I).f a)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {chartEquation I a} := by
  rw [exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp, chartCover_projection]
  change ((IdealPullback.specIdeal I).comap
      (Spec.map (CommRingCat.ofHom (chartBase I a)))).ideal
      ⟨(⊤ : (Spec (CommRingCat.of (chart I a))).Opens), isAffineOpen_top _⟩ =
    Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of (chart I a))).inv (chartBase I a a.val)}
  rw [IdealPullback.specIdeal_comap, IdealPullback.specIdeal_top, map_ideal_principal,
    Ideal.map_span, Set.image_singleton]

lemma chartEquation_regular (a : I) : IsLeftRegular (chartEquation I a) := by
  apply IdealModule.regular_map_flat _ _ (chart_generator_regular I a).left
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (chart I a))).inv)

end

noncomputable section
open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

def exceptionalLineBundle : Geometry.LineBundle (affineBlowup I) :=
  Geometry.idealLineBundle (exceptionalIdeal I) (chartCover I) (chartEquation I)
    (exceptional_chart I) (chartEquation_regular I)

def exceptionalInclusion : (exceptionalLineBundle I).sheaf ⟶ IdealModule.unit (affineBlowup I) :=
  IdealModule.closedInclusion (exceptionalIdeal I)

instance exceptionalInclusion_mono : Mono (exceptionalInclusion I) := by
  exact inferInstanceAs (Mono (IdealModule.inclusion (exceptionalIdeal I).subschemeι))

end

noncomputable section
open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

lemma exceptional_presents : Geometry.PresentsPullbackIdeal (IdealPullback.specIdeal I)
    (projection I) (exceptionalLineBundle I) (exceptionalInclusion I) := by
  refine ⟨exceptionalInclusion_mono I, fun U V e => ?_⟩
  change ((IdealModule.closedInclusion (exceptionalIdeal I)).val.app (Opposite.op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal (IdealPullback.specIdeal I) (projection I) U V e

theorem exceptional_invertible : Geometry.InvertiblePullbackIdeal (IdealPullback.specIdeal I)
    (projection I) :=
  ⟨exceptionalLineBundle I, exceptionalInclusion I, exceptional_presents I⟩

end
end MaximalSeshadri.ReesGrading


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_PrincipalCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

instance projection_separated : IsSeparated (projection I) := by
  have hP : IsSeparated (Proj.toSpecZero (piece I)) := inferInstance
  have hQ : IsSeparated (Spec.map (zeroIso I).hom) := inferInstance
  exact MorphismProperty.comp_mem (@IsSeparated) _ _ hP hQ

lemma projection_mem (x : affineBlowup I) (s : R) :
    s ∈ ((projection I) x).asIdeal ↔
      algebraMap R (reesAlgebra I) s ∈ x.asHomogeneousIdeal := by
  change zeroEquiv I s ∈ ((Proj.toSpecZero (piece I)) x).asIdeal ↔ _
  exact ProjBase.toSpecZero_mem (piece I) x (zeroEquiv I s)

lemma projection_preimage (s : R) :
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen s =
      Proj.basicOpen (piece I) (algebraMap R (reesAlgebra I) s) := by
  ext x
  exact not_congr (projection_mem I x s)

lemma projection_preimage_le_chart (a : I) :
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen a.val ≤
      Proj.basicOpen (piece I) (generator I a) := by
  rw [projection_preimage]
  intro x hx
  obtain ⟨b, hb⟩ := Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))
  have h : x ∈ Proj.basicOpen (piece I)
      (algebraMap R (reesAlgebra I) a.val * generator I b) := by
    rw [Proj.basicOpen_mul]
    exact ⟨hx, hb⟩
  rw [base_generator_comm, Proj.basicOpen_mul] at h
  exact h.2

end
end MaximalSeshadri.ReesGrading


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_Uniqueness
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.SpecMaps
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}

lemma factor (f : X ⟶ Spec R) :
    X.toSpecΓ ≫ Spec.map (coordinate f) = f := by
  unfold coordinate
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

lemma preimage_basicOpen (f : X ⟶ Spec R) (a : R) :
    f ⁻¹ᵁ PrimeSpectrum.basicOpen a = X.basicOpen (coordinate f a) := by
  conv_lhs => rw [← factor f]
  change X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (coordinate f a) = _
  exact Scheme.toSpecΓ_preimage_basicOpen _ _

lemma isUnit_coordinate_of_preimage_top (f : X ⟶ Spec R) (a : R)
    (h : f ⁻¹ᵁ PrimeSpectrum.basicOpen a = ⊤) : IsUnit (coordinate f a) := by
  apply isUnit_of_basicOpen_eq_top
  rwa [preimage_basicOpen] at h

lemma ideal_unit_generator (I : Ideal R) (f : X ⟶ Spec R)
    (hI : I.map (coordinate f).hom = ⊤) (x : X) :
    ∃ a : I, x ∈ f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val := by
  by_contra! hn
  have hle : I ≤ (f x).asIdeal := by
    intro a ha
    exact not_not.mp (hn ⟨a, ha⟩)
  have hmap : I.map (coordinate f).hom ≤ (X.toSpecΓ x).asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hm := hle ha
    rw [← factor f, Scheme.Hom.comp_apply, Spec.map_apply] at hm
    exact hm
  rw [hI] at hmap
  exact (X.toSpecΓ x).isPrime.ne_top (top_unique hmap)

end
end MaximalSeshadri.SpecMaps

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
open SpecMaps
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma ext_of_unit_generator {Y : Scheme.{u}} (a : I)
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hu : IsUnit (coordinate f a.val)) : g = h := by
  let : IsOpenImmersion ((chartCover I).f a) := (chartCover I).map_prop a
  have ht : f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val = ⊤ := by
    rw [preimage_basicOpen, Scheme.basicOpen_of_isUnit _ hu]
  have hrange (k : Y ⟶ affineBlowup I) (hk : k ≫ projection I = f) :
      Set.range k ⊆ Set.range ((chartCover I).f a) := by
    rintro _ ⟨y, rfl⟩
    change k y ∈ ((chartCover I).f a).opensRange
    change k y ∈ (Proj.awayι (piece I) (generator I a) (generator_mem I a)
      (show 0 < (1 : ℕ) from Nat.zero_lt_one)).opensRange
    rw [Proj.opensRange_awayι]
    apply projection_preimage_le_chart I a
    change (projection I) (k y) ∈ PrimeSpectrum.basicOpen a.val
    rw [← Scheme.Hom.comp_apply, hk]
    exact ht.ge (Set.mem_univ y)
  let g' : Y ⟶ Spec (CommRingCat.of (chart I a)) :=
    IsOpenImmersion.lift (X := Spec ((chartCover I).X a)) ((chartCover I).f a) g (hrange g hg)
  let h' : Y ⟶ Spec (CommRingCat.of (chart I a)) :=
    IsOpenImmersion.lift (X := Spec ((chartCover I).X a)) ((chartCover I).f a) h (hrange h hh)
  have hg' : g' ≫ (chartCover I).f a = g :=
    IsOpenImmersion.lift_fac ((chartCover I).f a) g (hrange g hg)
  have hh' : h' ≫ (chartCover I).f a = h :=
    IsOpenImmersion.lift_fac ((chartCover I).f a) h (hrange h hh)
  have eg : g' ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) = f := by
    calc
      _ = g' ≫ ((chartCover I).f a ≫ projection I) :=
        congrArg (fun morphism => g' ≫ morphism) (chartCover_projection I a).symm
      _ = (g' ≫ (chartCover I).f a) ≫ projection I :=
        (Category.assoc g' ((chartCover I).f a) (projection I)).symm
      _ = f := (congrArg (fun morphism => morphism ≫ projection I) hg').trans hg
  have eh : h' ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) = f := by
    calc
      _ = h' ≫ ((chartCover I).f a ≫ projection I) :=
        congrArg (fun morphism => h' ≫ morphism) (chartCover_projection I a).symm
      _ = (h' ≫ (chartCover I).f a) ≫ projection I :=
        (Category.assoc h' ((chartCover I).f a) (projection I)).symm
      _ = f := (congrArg (fun morphism => morphism ≫ projection I) hh').trans hh
  have he : coordinate g' (chartBase I a a.val) = coordinate f a.val := by
    have hc := congrArg coordinate eg
    rw [coordinate_comp_spec] at hc
    exact ConcreteCategory.congr_hom hc a.val
  have hgh := chart_scheme_ext I a g' h' (eg.trans eh.symm) (by rw [he]; exact hu.isRegular)
  rw [← hg', ← hh', hgh]

end
end MaximalSeshadri.ReesGrading

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
open SpecMaps
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma ext_on_generator_open {Y : Scheme.{u}} (a : I)
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f) :
    (f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val).ι ≫ g =
      (f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val).ι ≫ h := by
  let U : Y.Opens := f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val
  apply ext_of_unit_generator I a _ _ (U.ι ≫ f)
  · rw [Category.assoc, hg]
  · rw [Category.assoc, hh]
  · apply isUnit_coordinate_of_preimage_top
    change U.ι ⁻¹ᵁ U = ⊤
    exact U.ι_preimage_self

lemma ext_of_unit_ideal {Y : Scheme.{u}}
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hI : I.map (coordinate f).hom = ⊤) : g = h := by
  refine Scheme.hom_ext_of_forall g h ?_
  intro y
  have ha : ∃ a : I, y ∈ f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val :=
    ideal_unit_generator (R := CommRingCat.of R) I f hI y
  obtain ⟨a, hay⟩ := ha
  refine ⟨f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val, hay, ?_⟩
  exact ext_on_generator_open I a g h f hg hh

lemma principal_basicOpen_unit_ideal {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (r : Γ(Y, ⊤)) (hI : I.map (coordinate f).hom = Ideal.span {r}) :
    I.map (coordinate ((Y.basicOpen r).ι ≫ f)).hom = ⊤ := by
  rw [coordinate_comp]
  change I.map ((Y.basicOpen r).ι.appTop.hom.comp (coordinate f).hom) = ⊤
  rw [← Ideal.map_map, hI, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
  apply isUnit_of_basicOpen_eq_top
  rw [← Scheme.preimage_basicOpen_top]
  exact (Y.basicOpen r).ι_preimage_self

lemma principal_unique {Y : Scheme.{u}} [IsAffine Y]
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (r : Γ(Y, ⊤)) (hI : I.map (coordinate f).hom = Ideal.span {r}) (hr : IsRegular r) :
    g = h := by
  apply SchematicExt.ext_of_ker_eq_bot_of_isSeparated (projection I) (hg.trans hh.symm)
    (Y.basicOpen r).ι (SchematicExt.basicOpen_ker_eq_bot r hr)
  exact ext_of_unit_ideal I _ _ ((Y.basicOpen r).ι ≫ f)
    (by rw [Category.assoc, hg]) (by rw [Category.assoc, hh])
    (principal_basicOpen_unit_ideal I f r hI)

end
end MaximalSeshadri.ReesGrading


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_Frames
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.coefficient_scalarEnd _root_.OAI.MaximalSeshadri.Frames.moduleSectionEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y Z : Scheme.{u}}

lemma end_apply (f : O X ⟶ O X) (U : X.Opens) (a : Γ(X, U)) :
    f.app U a = a * (show Γ(X, U) from f.app U (1 : Γ(X, U))) := by
  have h := f.app_smul (r := a) (x := (1 : Γ(X, U)))
  change f.app U (a * 1 : Γ(X, U)) = a * (show Γ(X, U) from f.app U (1 : Γ(X, U))) at h
  simpa only [mul_one] using h

lemma endValue_comp (f g : O X ⟶ O X) :
    endValue (f ≫ g) = endValue f * endValue g := by
  exact end_apply g ⊤ (endValue f)

def frameChange {M : X.Modules} (e f : M ≅ O X) : Γ(X, ⊤)ˣ where
  val := endValue (e.inv ≫ f.hom)
  inv := endValue (f.inv ≫ e.hom)
  val_inv := by rw [← endValue_comp]; simp
  inv_val := by rw [← endValue_comp]; simp

lemma coefficient_change {M : X.Modules} (e f : M ≅ O X) (s : O X ⟶ M) :
    coefficient f s = (frameChange e f : Γ(X, ⊤)) * coefficient e s := by
  change endValue (s ≫ f.hom) = endValue (e.inv ≫ f.hom) * endValue (s ≫ e.hom)
  rw [mul_comm, ← endValue_comp]
  simp

lemma coefficient_frame {M : X.Modules} (e : M ≅ O X) : coefficient e e.inv = 1 := by
  simp [coefficient]

def restrictSection (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (s : O X ⟶ M) : O Y ⟶ M.restrict φ :=
  (Scheme.Modules.restrictUnitIso φ).inv ≫ (Scheme.Modules.restrictFunctor φ).map s

def restrictFrame (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (e : M ≅ O X) : M.restrict φ ≅ O Y :=
  (Scheme.Modules.restrictFunctor φ).mapIso e ≪≫ Scheme.Modules.restrictUnitIso φ

lemma end_naturality (f : O X ⟶ O X) (U : X.Opens) :
    f.app U (1 : Γ(X, U)) =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (endValue f) := by
  have h := CategoryTheory.congr_fun (f.mapPresheaf.naturality
    (homOfLE (show U ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
  change f.app U (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤))) =
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (endValue f) at h
  simpa only [map_one] using h

lemma endValue_restrict (φ : Y ⟶ X) [IsOpenImmersion φ] (f : O X ⟶ O X) :
    endValue (restrictSection φ f ≫ (Scheme.Modules.restrictUnitIso φ).hom) =
      φ.appTop (endValue f) := by
  change (φ.appIso ⊤).hom (f.app (φ ''ᵁ ⊤) ((φ.appIso ⊤).inv 1)) = _
  rw [map_one, end_naturality]
  change (X.presheaf.map (homOfLE (show φ ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫
    (φ.appIso ⊤).hom) (endValue f) = _
  rw [Scheme.Hom.appIso_hom']
  simp only [Scheme.Hom.appTop, Scheme.Hom.appLE,
    Scheme.Hom.naturality_assoc, ← Functor.map_comp]
  congr 1
  rw [show ((Opens.map φ.base).map (homOfLE (show φ ''ᵁ ⊤ ≤ ⊤ from le_top)).op.unop).op ≫
      (homOfLE (show (⊤ : Y.Opens) ≤ φ ⁻¹ᵁ (φ ''ᵁ ⊤) from by intro x _; exact ⟨x, Set.mem_univ _, rfl⟩)).op = 𝟙 _ from Subsingleton.elim _ _]
  change ConcreteCategory.hom (φ.app ⊤ ≫ Y.presheaf.map (𝟙 (Opposite.op ⊤))) =
    ConcreteCategory.hom (φ.app ⊤)
  exact congrArg ConcreteCategory.hom
    ((congrArg (fun morphism => φ.app ⊤ ≫ morphism) (Y.presheaf.map_id _)).trans
      (Category.comp_id _))

lemma coefficient_restrict (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M) :
    coefficient (restrictFrame φ e) (restrictSection φ s) = φ.appTop (coefficient e s) := by
  let restriction := Scheme.Modules.restrictFunctor φ
  let unitIso := Scheme.Modules.restrictUnitIso φ
  have composition :
      (unitIso.inv ≫ restriction.map s) ≫ restriction.map e.hom ≫ unitIso.hom =
        (unitIso.inv ≫ restriction.map (s ≫ e.hom)) ≫ unitIso.hom := by
    calc
      _ = unitIso.inv ≫ (restriction.map s ≫ restriction.map e.hom) ≫ unitIso.hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun morphism => unitIso.inv ≫ morphism)
            (Category.assoc _ _ _).symm)
      _ = unitIso.inv ≫ restriction.map (s ≫ e.hom) ≫ unitIso.hom :=
        congrArg (fun morphism => unitIso.inv ≫ morphism ≫ unitIso.hom)
          (restriction.map_comp s e.hom).symm
      _ = _ := (Category.assoc _ _ _).symm
  exact (congrArg endValue composition).trans (endValue_restrict φ (s ≫ e.hom))

lemma restrictUnit_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] :
    (Scheme.Modules.restrictUnitIso (φ ≫ ψ)).inv ≫
      (Scheme.Modules.restrictFunctorComp φ ψ).hom.app (O Z) =
    (Scheme.Modules.restrictUnitIso φ).inv ≫
      (Scheme.Modules.restrictFunctor φ).map (Scheme.Modules.restrictUnitIso ψ).inv := by
  ext U a
  change Z.presheaf.map (eqToHom (show ψ ''ᵁ (φ ''ᵁ U) = (φ ≫ ψ) ''ᵁ U from by simp)).op
    ((φ ≫ ψ).appIso U |>.inv |>.hom |>.toFun <| a) =
      (ψ.appIso (φ ''ᵁ U)).inv ((φ.appIso U).inv a)
  rw [Scheme.Hom.comp_appIso]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv]
  change ( (φ.appIso U).inv ≫ (ψ.appIso (φ ''ᵁ U)).inv ≫
    Z.presheaf.map _ ≫ Z.presheaf.map _) a = _
  rw [← CategoryTheory.Functor.map_comp]
  simp
  rfl

lemma restrictSection_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : Z.Modules} (s : O Z ⟶ M) :
    restrictSection (φ ≫ ψ) s ≫ (Scheme.Modules.restrictFunctorComp φ ψ).hom.app M =
      restrictSection φ (restrictSection ψ s) := by
  let first := Scheme.Modules.restrictFunctor φ
  let second := Scheme.Modules.restrictFunctor ψ
  let combined := Scheme.Modules.restrictFunctor (φ ≫ ψ)
  let comparison := (Scheme.Modules.restrictFunctorComp φ ψ).hom
  let unitIso := Scheme.Modules.restrictUnitIso (φ ≫ ψ)
  calc
    _ = unitIso.inv ≫ combined.map s ≫ comparison.app M := Category.assoc _ _ _
    _ = unitIso.inv ≫ comparison.app (O Z) ≫ (second ⋙ first).map s :=
      congrArg (fun morphism => unitIso.inv ≫ morphism) (comparison.naturality s)
    _ = (unitIso.inv ≫ comparison.app (O Z)) ≫ (second ⋙ first).map s :=
      (Category.assoc _ _ _).symm
    _ = ((Scheme.Modules.restrictUnitIso φ).inv ≫
        first.map (Scheme.Modules.restrictUnitIso ψ).inv) ≫ (second ⋙ first).map s :=
      congrArg (fun morphism => morphism ≫ (second ⋙ first).map s)
        (restrictUnit_comp φ ψ)
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun morphism => (Scheme.Modules.restrictUnitIso φ).inv ≫ morphism)
        (first.map_comp (Scheme.Modules.restrictUnitIso ψ).inv (second.map s)).symm)

lemma coefficient_transport {M N : X.Modules} (e : M ≅ N) (f : N ≅ O X)
    (s : O X ⟶ M) : coefficient (e ≪≫ f) s = coefficient f (s ≫ e.hom) := by
  simp only [coefficient, Iso.trans_hom, Category.assoc]

lemma coefficient_restrict_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : Z.Modules}
    (e : M.restrict ψ ≅ O X) (s : O Z ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctorComp φ ψ).app M ≪≫ restrictFrame φ e)
      (restrictSection (φ ≫ ψ) s) = φ.appTop (coefficient e (restrictSection ψ s)) := by
  rw [coefficient_transport]
  change coefficient (restrictFrame φ e)
    (restrictSection (φ ≫ ψ) s ≫ (Scheme.Modules.restrictFunctorComp φ ψ).hom.app M) = _
  rw [restrictSection_comp, coefficient_restrict]

lemma restrictSection_congr {φ ψ : Y ⟶ X} (h : φ = ψ)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : X.Modules} (s : O X ⟶ M) :
    restrictSection φ s ≫ (Scheme.Modules.restrictFunctorCongr h).hom.app M =
      restrictSection ψ s := by
  subst ψ
  have H : (Scheme.Modules.restrictFunctorCongr (show φ = φ from rfl)).hom.app M = 𝟙 _ := by
    ext U a
    simp
    rfl
  rw [H, Category.comp_id]

lemma overlap_coefficients {W : Scheme.{u}} (φ : Y ⟶ X) (ψ : Z ⟶ X)
    (a : W ⟶ Y) (b : W ⟶ Z) [IsOpenImmersion φ] [IsOpenImmersion ψ]
    [IsOpenImmersion a] [IsOpenImmersion b] (h : a ≫ φ = b ≫ ψ)
    {M : X.Modules} (e : M.restrict φ ≅ O Y) (f : M.restrict ψ ≅ O Z) :
    ∃ c : Γ(W, ⊤)ˣ, ∀ s : O X ⟶ M,
      b.appTop (coefficient f (restrictSection ψ s)) =
      (c : Γ(W, ⊤)) * a.appTop (coefficient e (restrictSection φ s)) := by
  let E : M.restrict (a ≫ φ) ≅ O W :=
    (Scheme.Modules.restrictFunctorComp a φ).app M ≪≫ restrictFrame a e
  let F : M.restrict (a ≫ φ) ≅ O W :=
    (Scheme.Modules.restrictFunctorCongr h).app M ≪≫
      (Scheme.Modules.restrictFunctorComp b ψ).app M ≪≫ restrictFrame b f
  refine ⟨frameChange E F, fun s => ?_⟩
  have H := coefficient_change E F (restrictSection (a ≫ φ) s)
  have hE : coefficient E (restrictSection (a ≫ φ) s) =
      a.appTop (coefficient e (restrictSection φ s)) := coefficient_restrict_comp a φ e s
  have hF : coefficient F (restrictSection (a ≫ φ) s) =
      b.appTop (coefficient f (restrictSection ψ s)) := by
    change coefficient ((Scheme.Modules.restrictFunctorCongr h).app M ≪≫
      ((Scheme.Modules.restrictFunctorComp b ψ).app M ≪≫ restrictFrame b f)) _ = _
    rw [coefficient_transport]
    change coefficient _ (restrictSection (a ≫ φ) s ≫
      (Scheme.Modules.restrictFunctorCongr h).hom.app M) = _
    rw [restrictSection_congr]
    exact coefficient_restrict_comp b ψ f s
  rwa [hE, hF] at H

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

lemma endValue_injective : Function.Injective (endValue (X := X)) := by
  intro f g h
  ext U a
  change Γ(X, U) at a
  change f.app U a = g.app U a
  rw [end_apply f U a, end_apply g U a]
  rw [end_naturality f U, end_naturality g U, h]

lemma end_isIso_iff (f : O X ⟶ O X) : IsIso f ↔ IsUnit (endValue f) := by
  constructor
  · intro h
    let := h
    refine isUnit_iff_exists_inv.mpr ⟨endValue (inv f), ?_⟩
    rw [← endValue_comp]
    simp
  · rintro ⟨u, hu⟩
    refine ⟨⟨scalarEnd ↑u⁻¹, ?_, ?_⟩⟩
    · apply endValue_injective
      rw [endValue_comp, ← hu, endValue_scalarEnd, endValue_id]
      exact Units.val_inv u
    · apply endValue_injective
      rw [endValue_comp, ← hu, endValue_scalarEnd, endValue_id]
      exact Units.inv_val u

lemma coefficient_isUnit_iff {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) :
    IsUnit (coefficient e s) ↔ IsIso s := by
  change IsUnit (endValue (s ≫ e.hom)) ↔ _
  rw [← end_isIso_iff]
  exact isIso_comp_right_iff s e.hom

end
end MaximalSeshadri.Frames

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorFrames
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma coefficient_injective {M : X.Modules} (e : M ≅ O X) :
    Function.Injective (coefficient e) := by
  intro s t h
  apply (cancel_mono e.hom).1
  exact endValue_injective h

end
end MaximalSeshadri.Frames


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_SectionOpens
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

lemma coefficient_restrict_isUnit {M : X.Modules} (e : M ≅ O X)
    (s : O X ⟶ M) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    IsUnit (φ.appTop (coefficient e s)) ↔
      IsIso ((Scheme.Modules.restrictFunctor φ).map s) := by
  rw [← coefficient_restrict, coefficient_isUnit_iff]
  let unitIso : (Scheme.Modules.restrictFunctor φ).obj (O X) ≅ O Y :=
    Scheme.Modules.restrictUnitIso φ
  exact isIso_comp_left_iff unitIso.inv
    ((Scheme.Modules.restrictFunctor φ).map s)

theorem isoOpen_eq_basicOpen {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) :
    SectionOpens.isoOpen s = X.basicOpen (coefficient e s) := by
  ext x
  constructor
  · intro hx
    obtain ⟨U, hxU, hU⟩ := (SectionOpens.mem_isoOpen_iff s x).mp hx
    have hc := (coefficient_restrict_isUnit e s U.ι).mpr hU
    have hb := U.toScheme.basicOpen_of_isUnit hc
    rw [← Scheme.preimage_basicOpen_top] at hb
    have H : (⟨x, hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ X.basicOpen (coefficient e s) := by
      rw [hb]; trivial
    exact H
  · intro hx
    let U := X.basicOpen (coefficient e s)
    refine (SectionOpens.mem_isoOpen_iff s x).mpr ⟨U, hx, ?_⟩
    apply (coefficient_restrict_isUnit e s U.ι).mp
    apply (isUnit_iff_basicOpen_top _).mpr
    rw [← Scheme.preimage_basicOpen_top]
    ext z
    change z.val ∈ X.basicOpen (coefficient e s) ↔ True
    exact iff_true_intro z.property

lemma isoOpen_restrictSection {M : X.Modules} (s : O X ⟶ M)
    (φ : Y ⟶ X) [IsOpenImmersion φ] :
    SectionOpens.isoOpen (restrictSection φ s) = φ ⁻¹ᵁ SectionOpens.isoOpen s := by
  exact (SectionOpens.isoOpen_precomp (Scheme.Modules.restrictUnitIso φ).symm
    ((Scheme.Modules.restrictFunctor φ).map s)).trans (SectionOpens.isoOpen_restrict s φ)

theorem preimage_isoOpen {M : X.Modules} (s : O X ⟶ M)
    (φ : Y ⟶ X) [IsOpenImmersion φ] (e : M.restrict φ ≅ O Y) :
    φ ⁻¹ᵁ SectionOpens.isoOpen s =
      Y.basicOpen (coefficient e (restrictSection φ s)) := by
  rw [← isoOpen_restrictSection, isoOpen_eq_basicOpen e]

end
end MaximalSeshadri.Frames


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_Sections
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped AlgebraicGeometry
variable {X : Scheme}

def openSectionEquiv (M : X.Modules) (U : X.Opens) :
    (O U.toScheme ⟶ M.restrict U.ι) ≃ Γ(M, U) :=
  (moduleSectionEquiv (M.restrict U.ι)).trans
    (let e := M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
     { toFun := e.hom
       invFun := e.inv
       left_inv := fun t => Iso.hom_inv_id_apply e t
       right_inv := fun t => Iso.inv_hom_id_apply e t })

end
end MaximalSeshadri.Frames


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_LocalEquations
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.ReesGrading
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Geometry
open SpecMaps
variable {R : Type} [CommRing R] (I : Ideal R)

lemma invertible_unique {Y : Scheme} (g h : Y ⟶ affineBlowup I)
    (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) : g = h := by
  apply Scheme.hom_ext_of_forall g h
  intro y
  obtain ⟨U, hyU, r, hr, hIr⟩ :=
    InvertibleLocal.affine_local_equation (IdealPullback.specIdeal I) f hf y
  refine ⟨U.1, hyU, ?_⟩
  apply principal_unique I (U.1.ι ≫ g) (U.1.ι ≫ h) (U.1.ι ≫ f)
    (by rw [Category.assoc, hg]) (by rw [Category.assoc, hh]) r _ hr
  rwa [← Scheme.IdealSheafData.comap_comp, IdealPullback.specIdeal_coordinate] at hIr

lemma local_lift {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of R))
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∃ h : U.toScheme ⟶ affineBlowup I,
      h ≫ projection I = U.ι ≫ f := by
  obtain ⟨U, hyU, r, hr, hIr⟩ :=
    InvertibleLocal.affine_local_equation (IdealPullback.specIdeal I) f hf y
  rw [← Scheme.IdealSheafData.comap_comp, IdealPullback.specIdeal_coordinate] at hIr
  refine ⟨U.1, hyU, principalScheme I U.1.toScheme (coordinate (U.1.ι ≫ f)).hom r hIr hr, ?_⟩
  rw [principalScheme_projection]
  exact factor (U.1.ι ≫ f)

theorem affineBlowup_universal {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of R))
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) :
    ∃! h : Y ⟶ affineBlowup I, h ≫ projection I = f := by
  classical
  choose U hyU g hg using local_lift I f hf
  let C : Y.OpenCover := {
    I₀ := Y
    X y := (U y).toScheme
    f y := (U y).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun y => ⟨y, ?_⟩, inferInstance⟩
      simpa using hyU y }
  have hcompat (x y : C.I₀) : pullback.fst (C.f x) (C.f y) ≫ g x =
      pullback.snd (C.f x) (C.f y) ≫ g y := by
    let j := pullback.fst (C.f x) (C.f y) ≫ C.f x
    apply invertible_unique I _ _ (j ≫ f)
    · rw [Category.assoc, hg x]
      rfl
    · rw [Category.assoc, hg y]
      exact (pullback.condition_assoc f).symm
    · exact InvertibleLocal.invertible_restrict (IdealPullback.specIdeal I) f hf j
  refine ⟨C.glueMorphisms g hcompat, ?_, ?_⟩
  · apply C.hom_ext
    intro y
    rw [← Category.assoc, C.ι_glueMorphisms]
    exact hg y
  · intro h hh
    exact invertible_unique I h _ f hh (by
      apply C.hom_ext
      intro y
      rw [← Category.assoc, C.ι_glueMorphisms]
      exact hg y) hf

end
end MaximalSeshadri.ReesGrading

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_LocalUniversal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry

theorem rees_isBlowup {R : Type} [CommRing R] (I : Ideal R) :
    IsBlowup (IdealPullback.specIdeal I) (ReesGrading.projection I) :=
  ⟨ReesGrading.exceptional_invertible I, fun _ f hf =>
    ReesGrading.affineBlowup_universal I f hf⟩

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.InvertibleLocal

noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y Z : Scheme}

lemma presents_restrict_general (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hf : PresentsPullbackIdeal I f J ι) (j : Z ⟶ Y) [IsOpenImmersion j] :
    PresentsPullbackIdeal I (j ≫ f) (restrictLineBundle J j) (restrictedInclusion J ι j) := by
  let : Mono ι := hf.1
  refine ⟨restrictedInclusion_mono J ι j, ?_⟩
  intro U V e
  change ((restrictedInclusion J ι j).val.app (Opposite.op U.1)).hom.range = _
  rw [restricted_image_on_chart J ι hf j U V ?_, ← Scheme.IdealSheafData.comap_comp]
  · exact IdealPullback.comap_ideal I (j ≫ f) U V e
  · rintro _ ⟨z, hz, rfl⟩
    exact e hz

lemma invertible_restrict_general (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (j : Z ⟶ Y) [IsOpenImmersion j] :
    InvertiblePullbackIdeal I (j ≫ f) := by
  obtain ⟨J, ι, h⟩ := hf
  exact ⟨restrictLineBundle J j, restrictedInclusion J ι j,
    presents_restrict_general I f J ι h j⟩

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X B Y Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.open_baseChange (hπ : IsBlowup I π) (j : Z ⟶ X)
    [IsOpenImmersion j] :
    IsBlowup (I.comap j) (pullback.fst j π) := by
  have hcongr {W : Scheme} (g : W ⟶ Z) :
      InvertiblePullbackIdeal (I.comap j) g ↔ InvertiblePullbackIdeal I (g ≫ j) :=
    InvertibleLocal.invertible_congr (Scheme.IdealSheafData.comap_comp I g j).symm
  have hpic : InvertiblePullbackIdeal (I.comap j) (pullback.fst j π) := by
    apply (hcongr _).mpr
    rw [pullback.condition]
    exact InvertibleLocal.invertible_restrict_general I π hπ.1 (pullback.snd j π)
  refine ⟨hpic, ?_⟩
  intro W f hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ j) ((hcongr f).mp hf)
  refine ⟨pullback.lift f l hl.symm, pullback.lift_fst _ _ _, ?_⟩
  intro m hm
  apply pullback.hom_ext
  · simpa only [pullback.lift_fst] using hm
  · rw [pullback.lift_snd]
    apply huniq
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hm]

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X B B' Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.baseChangeSquare (hπ : IsBlowup I π) (j : Z ⟶ X)
    [IsOpenImmersion j] (ρ : B' ⟶ Z) (hρ : IsBlowup (I.comap j) ρ)
    (β : B' ⟶ B) (hβ : β ≫ π = ρ ≫ j) : IsPullback ρ β j π := by
  let e := hρ.iso (hπ.open_baseChange j)
  refine IsPullback.of_iso_pullback ⟨hβ.symm⟩ e
    (hρ.iso_hom_comp (hπ.open_baseChange j)) ?_
  apply hπ.hom_ext (ρ ≫ j)
  · exact (InvertibleLocal.invertible_congr
      (Scheme.IdealSheafData.comap_comp I ρ j)).mpr hρ.1
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      hρ.iso_hom_comp (hπ.open_baseChange j)]
  · exact hβ

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry
variable {X : Scheme.{0}} [IsAffine X]

lemma specIdeal_comap_toSpec (I : X.IdealSheafData) :
    (specIdeal (I.ideal ⟨⊤, isAffineOpen_top X⟩)).comap X.toSpecΓ = I := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [comap_top, specIdeal_top, Scheme.toSpecΓ_appTop, Ideal.map_map]
  change Ideal.map ((Scheme.ΓSpecIso Γ(X, ⊤)).hom.hom.comp
    (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom) _ = _
  simp only [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]

lemma comap_isoSpec_inv (I : X.IdealSheafData) :
    I.comap X.isoSpec.inv = specIdeal (I.ideal ⟨⊤, isAffineOpen_top X⟩) := by
  conv_lhs => rw [← specIdeal_comap_toSpec I]
  rw [← Scheme.IdealSheafData.comap_comp]
  change (specIdeal _).comap (X.isoSpec.inv ≫ X.isoSpec.hom) = _
  rw [Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.AffineBlowup
noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X : Scheme.{0}} [IsAffine X] (I : X.IdealSheafData)

theorem isBlowup : IsBlowup I (projection I) :=
  (rees_isBlowup (I.ideal ⟨⊤, isAffineOpen_top X⟩)).postIso X.isoSpec.symm I
    (IdealPullback.comap_isoSpec_inv I)

end
end MaximalSeshadri.AffineBlowup


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_Gluing
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.BlowupGluing
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MaximalSeshadri.Geometry

variable {X : Scheme.{0}} (I : X.IdealSheafData)

attribute [local instance] OAI.MaximalSeshadri.BlowupGluing.localAffine
abbrev localScheme (U : X.AffineZariskiSite) : Scheme :=
  AffineBlowup.scheme (localCentre I U)

abbrev localProjection (U : X.AffineZariskiSite) : localScheme I U ⟶ U.toOpens.toScheme :=
  AffineBlowup.projection (localCentre I U)

lemma local_isBlowup (U : X.AffineZariskiSite) :
    IsBlowup (localCentre I U) (localProjection I U) :=
  AffineBlowup.isBlowup (localCentre I U)

lemma local_invertible {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    InvertiblePullbackIdeal (localCentre I V)
      (localProjection I U ≫ (baseCover I).trans h) := by
  apply (InvertibleLocal.invertible_congr (I' := localCentre I U)
    (f' := localProjection I U) ?_).mpr (local_isBlowup I U).1
  rw [Scheme.IdealSheafData.comap_comp, centre_transition]

def transition {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    localScheme I U ⟶ localScheme I V :=
  ((local_isBlowup I V).2 _ _ (local_invertible I h)).choose

@[reassoc (attr := simp)]
lemma transition_projection {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    transition I h ≫ localProjection I V = localProjection I U ≫ (baseCover I).trans h :=
  ((local_isBlowup I V).2 _ _ (local_invertible I h)).choose_spec.1

lemma transition_id (U : X.AffineZariskiSite) : transition I (𝟙 U) = 𝟙 (localScheme I U) := by
  apply (local_isBlowup I U).hom_ext (localProjection I U) (local_isBlowup I U).1
  · rw [transition_projection, Scheme.Cover.trans_id (baseCover I) U, Category.comp_id]
  · simp

lemma transition_comp {U V W : X.AffineZariskiSite} (h : U ⟶ V) (k : V ⟶ W) :
    transition I (h ≫ k) = transition I h ≫ transition I k := by
  apply (local_isBlowup I W).hom_ext _ (local_invertible I (h ≫ k))
  · exact transition_projection I (h ≫ k)
  · rw [Category.assoc, transition_projection, ← Category.assoc, transition_projection,
      Category.assoc, Scheme.Cover.trans_comp (baseCover I) h k]

def diagram : X.AffineZariskiSite ⥤ Scheme where
  obj := localScheme I
  map := transition I
  map_id := transition_id I
  map_comp := transition_comp I

def diagramMap : diagram I ⟶ (baseCover I).functorOfLocallyDirected where
  app := localProjection I
  naturality _ _ h := transition_projection I h

lemma diagramMap_equifibered : (diagramMap I).Equifibered := by
  intro U V h
  apply IsPullback.flip
  change IsPullback (localProjection I U) (transition I h)
    ((baseCover I).trans h) (localProjection I V)
  apply (local_isBlowup I V).baseChangeSquare ((baseCover I).trans h)
    (localProjection I U)
  · rw [centre_transition]
    exact local_isBlowup I U
  · exact transition_projection I h

def gluing : (baseCover I).RelativeGluingData where
  functor := diagram I
  natTrans := diagramMap I
  equifibered := diagramMap_equifibered I

abbrev scheme : Scheme := (gluing I).glued
abbrev projection : scheme I ⟶ X := (gluing I).toBase
abbrev cover : (scheme I).OpenCover := (gluing I).cover

@[reassoc (attr := simp)]
lemma cover_projection (U : X.AffineZariskiSite) :
    (cover I).f U ≫ projection I = localProjection I U ≫ U.toOpens.ι :=
  (gluing I).ι_toBase U

end

end MaximalSeshadri.BlowupGluing


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_PlaneCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open MvPolynomial ReesGrading
variable (K : Type) [Field K]
abbrev originIdeal : Ideal (PlaneRing K) := MvPolynomial.idealOfVars (Fin 2) K

def coordinate (i : Fin 2) : originIdeal K :=
  ⟨X i, Ideal.subset_span (Set.mem_range_self i)⟩

def chartSubstitution (i : Fin 2) : PlaneRing K →+* PlaneRing K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j => if j = i then X i else X i * X j)

@[simp] lemma substitution_C (i : Fin 2) (c : K) : chartSubstitution K i (C c) = C c := by
  simp [chartSubstitution]

@[simp] lemma substitution_self (i : Fin 2) : chartSubstitution K i (X i) = X i := by
  simp [chartSubstitution]

@[simp] lemma substitution_other (i j : Fin 2) (h : j ≠ i) :
    chartSubstitution K i (X j) = X i * X j := by
  simp [chartSubstitution, h]

lemma substitution_ideal (i : Fin 2) :
    (originIdeal K).map (chartSubstitution K i) ≤ Ideal.span {X i} := by
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  change chartSubstitution K i (X j) ∈ Ideal.span {X i}
  by_cases h : j = i
  · subst j
    rw [substitution_self]
    exact Ideal.subset_span rfl
  · rw [substitution_other _ _ _ h]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

lemma substitution_regular (i : Fin 2) :
    IsRegular (chartSubstitution K i (coordinate K i).val) := by
  change IsRegular (chartSubstitution K i (X i))
  rw [substitution_self]
  exact isRegular_iff_ne_zero.mpr (MvPolynomial.X_ne_zero i)

def toPolynomial (i : Fin 2) : chart (originIdeal K) (coordinate K i) →+* PlaneRing K :=
  chartLift (originIdeal K) (coordinate K i) (chartSubstitution K i)
    (by simpa [coordinate] using substitution_ideal K i) (substitution_regular K i)

@[simp] lemma toPolynomial_base (i : Fin 2) (p : PlaneRing K) :
    toPolynomial K i (chartBase (originIdeal K) (coordinate K i) p) =
      chartSubstitution K i p := chartLift_base _ _ _ _ _ p

def fromPolynomial (i : Fin 2) : PlaneRing K →+* chart (originIdeal K) (coordinate K i) :=
  MvPolynomial.eval₂Hom
    ((chartBase (originIdeal K) (coordinate K i)).comp MvPolynomial.C)
    (fun j => if j = i then chartBase (originIdeal K) (coordinate K i) (X i)
      else ratio (originIdeal K) (coordinate K i) (coordinate K j))

@[simp] lemma fromPolynomial_C (i : Fin 2) (c : K) :
    fromPolynomial K i (C c) = chartBase (originIdeal K) (coordinate K i) (C c) := by
  simp [fromPolynomial]

@[simp] lemma fromPolynomial_self (i : Fin 2) :
    fromPolynomial K i (X i) = chartBase (originIdeal K) (coordinate K i) (X i) := by
  simp [fromPolynomial]

@[simp] lemma fromPolynomial_other (i j : Fin 2) (h : j ≠ i) :
    fromPolynomial K i (X j) = ratio (originIdeal K) (coordinate K i) (coordinate K j) := by
  simp [fromPolynomial, h]

end

end MaximalSeshadri.PlaneBlowup


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupIntegral
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.ReesGrading
noncomputable section
open AlgebraicGeometry Polynomial
variable {R : Type} [CommRing R] (I : Ideal R)

instance affineBlowup_isReduced [_root_.IsReduced R] : IsReduced (affineBlowup I) := by
  let : _root_.IsReduced (reesAlgebra I) :=
    isReduced_of_injective (reesAlgebra I).val Subtype.val_injective
  exact ProjectiveGeometry.proj_isReduced (piece I)

end
end MaximalSeshadri.ReesGrading

namespace MaximalSeshadri.AffineBlowup
noncomputable section
open AlgebraicGeometry
variable {X : Scheme.{0}} [IsAffine X] (I : X.IdealSheafData)

instance scheme_isReduced [IsReduced X] : IsReduced (scheme I) := by
  dsimp only [scheme]
  infer_instance

end
end MaximalSeshadri.AffineBlowup

namespace MaximalSeshadri.BlowupGluing
noncomputable section
open AlgebraicGeometry
variable {X : Scheme.{0}} (I : X.IdealSheafData)

instance scheme_isReduced [IsReduced X] : IsReduced (scheme I) := by
  let : ∀ U : (cover I).I₀, IsReduced ((cover I).X U) := fun U => by
    change IsReduced (localScheme I U)
    infer_instance
  exact IsReduced.of_openCover _ (cover I)

end
end MaximalSeshadri.BlowupGluing

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupProper
attribute [-instance] _root_.OAI.MaximalSeshadri.AffineBlowup.scheme_isReduced _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

instance AffineBlowup.projection_proper {X : Scheme.{0}} [IsAffine X]
    [IsLocallyNoetherian X] (I : X.IdealSheafData) : IsProper (AffineBlowup.projection I) := by
  let : IsNoetherianRing Γ(X,⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤,isAffineOpen_top X⟩
  unfold AffineBlowup.projection
  infer_instance

end
end MaximalSeshadri

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_FiniteCenters
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.FinitePointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}

variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))

lemma mem_pointOpen (i : α) (x : X) :
    x ∈ pointOpen p i ↔ ∀ j, j ≠ i → x ∉ (p j).ker.support := by
  change (¬ x ∈ (⨆ j : {j : α // j ≠ i}, (p j).ker.support)) ↔ _
  rw [mem_finite_iSup_closed]
  simp

variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)

include hp

variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

include hd
lemma point_mem_own_open (i : α) (z : Spec (.of K)) : p i z ∈ pointOpen p i := by
  rw [mem_pointOpen]
  intro j hji
  change p i z ∉ ((p j).ker.support : Set X)
  rw [point_support p f hp j]
  intro h
  apply hji
  apply hd
  exact (show p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K)) = p j _ from
    (congrArg (p i) (Subsingleton.elim _ z)).trans h).symm

def pointCover : X.OpenCover :=
  .mkOfCovers (Option α)
    (fun i => (i.elim (outsideOpen p) (pointOpen p)).toScheme)
    (fun i => (i.elim (outsideOpen p) (pointOpen p)).ι)
    (by
      intro x
      by_cases hx : x ∈ (pointCentre p).support
      · obtain ⟨i, hi⟩ := (mem_centre_support p x).mp hx
        change x ∈ ((p i).ker.support : Set X) at hi
        rw [point_support p f hp i] at hi
        subst x
        exact ⟨some i, ⟨_, point_mem_own_open p f hp hd i _⟩, rfl⟩
      · exact ⟨none, ⟨x, hx⟩, rfl⟩)
    (by intro i; exact inferInstance)

end
end MaximalSeshadri.FinitePointBlowup

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ClosedPushforwardCohomology
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                     
section

namespace MaximalSeshadri.ClosedPushforward
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.FlasqueCohomology MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]

local instance instHasExtModules_solutions_r7a40b1_1 : HasExt.{1} X.Modules := schemeHasExt
attribute [local instance] OAI.MaximalSeshadri.ClosedPushforward.instHasExtModules_solutions_1
attribute [local instance] OAI.MaximalSeshadri.ClosedPushforward.instEnoughInjectivesModules_solutions
def cohomologyMap (M : X.Modules) (n : ℕ) :
    Ext.{1} (O X) M n →+ Ext.{1} (O Y) ((Scheme.Modules.pushforward f).obj M) n :=
  ((Ext.mk₀ (IdealModule.structureMap f)).precomp _ (zero_add n)).comp
    ((Scheme.Modules.pushforward f).mapExtAddHom (O X) M n)

omit [IsClosedImmersion f] in
lemma globalHom_push (M : X.Modules) (g : O X ⟶ M) :
    globalHomEquiv Y.ringCatSheaf ((Scheme.Modules.pushforward f).obj M)
      (IdealModule.structureMap f ≫ (Scheme.Modules.pushforward f).map g) =
    globalHomEquiv X.ringCatSheaf M g := by
  change (g.val.app (op ⊤)) ((f.app ⊤) 1) = (g.val.app (op ⊤)) (1 : Γ(X,⊤))
  rw [map_one]
  rfl

lemma cohomologyMap_zero_bijective (M : X.Modules) :
    Function.Bijective (cohomologyMap f M 0) := by
  have hhom : Function.Bijective (fun g : O X ⟶ M =>
      IdealModule.structureMap f ≫ (Scheme.Modules.pushforward f).map g) := by
    constructor
    · intro a b h
      apply (globalHomEquiv X.ringCatSheaf M).injective
      exact (globalHom_push f M a).symm.trans
        ((congrArg (globalHomEquiv Y.ringCatSheaf _) h).trans (globalHom_push f M b))
    · intro b
      obtain ⟨a,ha⟩ := (globalHomEquiv X.ringCatSheaf M).surjective
        (globalHomEquiv Y.ringCatSheaf ((Scheme.Modules.pushforward f).obj M) b)
      refine ⟨a,?_⟩
      apply (globalHomEquiv Y.ringCatSheaf _).injective
      exact (globalHom_push f M a).trans ha
  have he : (cohomologyMap f M 0) ∘ Ext.mk₀ = Ext.mk₀ ∘
      (fun g : O X ⟶ M => IdealModule.structureMap f ≫ (Scheme.Modules.pushforward f).map g) := by
    funext g
    change (Ext.mk₀ (IdealModule.structureMap f)).comp
      ((Ext.mk₀ g).mapExactFunctor (Scheme.Modules.pushforward f)) (zero_add 0) = _
    rw [Ext.mapExactFunctor_mk₀]
    exact Ext.mk₀_comp_mk₀ (IdealModule.structureMap f) ((Scheme.Modules.pushforward f).map g)
  exact (Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective _ _)).mp (by
    rw [he]
    exact (Ext.mk₀_bijective _ _).comp hhom)

lemma cohomologyMap_comp {M N : X.Modules} {n m k : ℕ}
    (a : Ext (O X) M n) (b : Ext M N m) (h : n+m=k) :
    cohomologyMap f N k (a.comp b h) =
      (cohomologyMap f M n a).comp
        (b.mapExactFunctor (Scheme.Modules.pushforward f)) h := by
  change (Ext.mk₀ (IdealModule.structureMap f)).comp
    ((a.comp b h).mapExactFunctor _) (zero_add _) = _
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add _) h (by omega)).symm

theorem cohomologyMap_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective (cohomologyMap f M n) := by
  induction n generalizing M with
  | zero => exact cohomologyMap_zero_bijective f M
  | succ n ih =>
    let I : InjectivePresentation M := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    let F := Scheme.Modules.pushforward f
    let : Injective S.X₂ := I.injective
    let : TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj S.X₂) :=
      @ModuleFlasque.injective_isFlasque _ X.ringCatSheaf S.X₂ I.injective
    let hfl : TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf.{0} Y.ringCatSheaf).obj ((S.map F).X₂)) :=
      pushforward_flasque f S.X₂
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (cohomologyMap f S.X₂ n) (cohomologyMap f S.X₃ n) (cohomologyMap f S.X₁ (n+1))
      ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (O X) hS n (n+1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (O Y) (hS.map F) n (n+1) rfl))
      (ih _).surjective (ih _) ?_ ?_
    · ext a
      change (cohomologyMap f S.X₂ n a).comp (Ext.mk₀ (F.map S.g)) (add_zero n) =
        cohomologyMap f S.X₃ n (a.comp (Ext.mk₀ S.g) (add_zero n))
      rw [cohomologyMap_comp, Ext.mapExactFunctor_mk₀]
    · ext a
      change (cohomologyMap f S.X₃ n a).comp (hS.map F).extClass rfl =
        cohomologyMap f S.X₁ (n+1) (a.comp hS.extClass rfl)
      rw [cohomologyMap_comp, Ext.mapExactFunctor_extClass]
      rfl
    · intro a
      exact Ext.covariant_sequence_exact₁ _ hS a (Ext.eq_zero_of_injective _) rfl
    · intro a
      exact Ext.covariant_sequence_exact₁ _ (hS.map F) a
        (@flasque_ext_zero.{0} (Y : TopCat) Y.ringCatSheaf n _ hfl _) rfl

end
end MaximalSeshadri.ClosedPushforward

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_SectionMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}

def sectionFrame {M : X.Modules} (s : O X ⟶ M) :
    M.restrict (SectionOpens.isoOpen s).ι ≅ O (SectionOpens.isoOpen s).toScheme := by
  letI := SectionOpens.isIso_restrict_isoOpen s
  exact (asIso ((Scheme.Modules.restrictFunctor (SectionOpens.isoOpen s).ι).map s)).symm ≪≫
    Scheme.Modules.restrictUnitIso (SectionOpens.isoOpen s).ι

lemma sectionFrame_normalized {M : X.Modules} (s : O X ⟶ M) :
    coefficient (sectionFrame s) (restrictSection (SectionOpens.isoOpen s).ι s) = 1 := by
  exact coefficient_frame (sectionFrame s)

end
end MaximalSeshadri.Projective

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_LinearSections
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.coefficient_scalarEnd _root_.OAI.MaximalSeshadri.Frames.moduleSectionEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}}

lemma coefficient_add {M : X.Modules} (e : M ≅ O X) (s t : O X ⟶ M) :
    coefficient e (s + t) = coefficient e s + coefficient e t := by
  simp [coefficient, endValue, Preadditive.add_comp]
  rfl

lemma coefficient_zero {M : X.Modules} (e : M ≅ O X) :
    coefficient e (0 : O X ⟶ M) = 0 := by
  simp [coefficient, endValue]
  rfl

lemma coefficient_sum {M : X.Modules} (e : M ≅ O X) {ι : Type*}
    (s : ι → (O X ⟶ M)) (T : Finset ι) :
    coefficient e (∑ i ∈ T, s i) = ∑ i ∈ T, coefficient e (s i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [coefficient_zero]
  | @insert i T hi ih => simp [Finset.sum_insert, hi, coefficient_add, ih]

lemma restrictSection_add (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (s t : O X ⟶ M) : restrictSection φ (s + t) = restrictSection φ s + restrictSection φ t := by
  ext U a
  rfl

lemma restrictSection_zero (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules} :
    restrictSection φ (0 : O X ⟶ M) = 0 := by
  ext U value
  rfl

lemma restrictSection_sum (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    {ι : Type*} (s : ι → (O X ⟶ M)) (T : Finset ι) :
    restrictSection φ (∑ i ∈ T, s i) = ∑ i ∈ T, restrictSection φ (s i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [restrictSection_zero]
  | @insert i T hi ih => simp [Finset.sum_insert, hi, restrictSection_add, ih]

lemma coefficient_restrict_scalar_comp (φ : Y ⟶ X) [IsOpenImmersion φ]
    {M : X.Modules} (e : M.restrict φ ≅ O Y) (a : Γ(X, ⊤)) (s : O X ⟶ M) :
    coefficient e (restrictSection φ (scalarEnd a ≫ s)) =
      φ.appTop a * coefficient e (restrictSection φ s) := by
  have h : restrictSection φ (scalarEnd a ≫ s) =
      (restrictSection φ (scalarEnd a) ≫ (Scheme.Modules.restrictUnitIso φ).hom) ≫
        restrictSection φ s := by
    let restriction : X.Modules ⥤ Y.Modules := Scheme.Modules.restrictFunctor φ
    let unitIso : restriction.obj (O X) ≅ O Y := Scheme.Modules.restrictUnitIso φ
    change unitIso.inv ≫ restriction.map (scalarEnd a ≫ s) =
      (unitIso.inv ≫ restriction.map (scalarEnd a) ≫ unitIso.hom) ≫
        unitIso.inv ≫ restriction.map s
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [h]
  calc
    _ = endValue ((restrictSection φ (scalarEnd a) ≫
        (Scheme.Modules.restrictUnitIso φ).hom) ≫ (restrictSection φ s ≫ e.hom)) :=
      congrArg endValue (Category.assoc _ _ _)
    _ = endValue (restrictSection φ (scalarEnd a) ≫
        (Scheme.Modules.restrictUnitIso φ).hom) * coefficient e (restrictSection φ s) :=
      endValue_comp _ _
    _ = _ := by rw [endValue_restrict, endValue_scalarEnd]

end
end MaximalSeshadri.Frames
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_OpenSectionsLinear
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ModuleFlasque

variable {X : Scheme.{0}}

local instance instAddCommGroupHomSheafOfModulesOpensCarrierCarrierCommRingCatRingCatSheafFreeOpen (M : X.Modules) (U : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf U : X.Modules) ⟶ M) :=
  Preadditive.homGroup (C := X.Modules) _ _

local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen (M : X.Modules) (U : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf U : X.Modules) ⟶ M) :=
  sheafHomModule X _ _

def freeOpenLinearEquiv (M : X.Modules) (U : X.Opens) :
    ((freeOpen X.ringCatSheaf U : X.Modules) ⟶ M) ≃ₗ[Γ(X,⊤)] OpenSections M U where
  toEquiv := freeOpenEquiv X.ringCatSheaf M U
  map_add' := by intro f g; rfl
  map_smul' := by intro r f; rfl

lemma freeOpenLinearEquiv_naturality (M : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (f : (freeOpen X.ringCatSheaf V : X.Modules) ⟶ M) :
    freeOpenLinearEquiv M U (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ f) =
      openRestriction M h (freeOpenLinearEquiv M V f) :=
  freeOpenEquiv_naturality X.ringCatSheaf M _ f

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CurveH0Finite
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Abelian
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}}

def BaseSections.globalSectionsLinear (M : X.Modules) :
    GlobalSections X M ≃ₗ[Γ(X,⊤)] Γ(M,⊤) where
  toEquiv := FlasqueCohomology.globalHomEquiv X.ringCatSheaf M
  map_add' := by intro f g; rfl
  map_smul' := by
    intro r f
    change restrictScalar X ⊤ r • f.app ⊤ (1 : Γ(X,⊤)) = r • f.app ⊤ (1 : Γ(X,⊤))
    congr 1
    change (X.presheaf.map (𝟙 (op ⊤))) r = r
    rw [X.presheaf.map_id]
    rfl

def BaseSections.cohomologyZero (k : K →+* Γ(X,⊤)) (M : X.Modules) :
    letI := Module.compHom (cohomology M 0) k
    cohomology M 0 ≃ₗ[K] Sections k M ⊤ := by
  letI := Module.compHom (cohomology M 0) k
  let e := (Ext.linearEquiv₀ (R := Γ(X,⊤)) (X := structureSheaf X) (Y := M)).trans
    (globalSectionsLinear M)
  refine { toFun := e
           invFun := e.symm
           left_inv := e.left_inv
           right_inv := e.right_inv
           map_add' := e.map_add
           map_smul' := ?_ }
  intro r m
  change e (k r • m) = restrictScalar X ⊤ (k r) • e m
  rw [e.map_smul]
  congr 1
  change k r = X.presheaf.map (𝟙 (op ⊤)) (k r)
  rw [X.presheaf.map_id]
  rfl

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_RestrictionComparison
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.RestrictionCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open ModuleFlasque FlasqueCohomology
universe u
variable {X : Scheme.{u}} (U : X.Opens)

attribute [local instance] OAI.MaximalSeshadri.RestrictionCohomology.hasExtScheme
theorem restriction_ext_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective
      (ExtSectionComparison.mapFrom (Scheme.Modules.restrictFunctor U.ι)
        (restrictionGenerator U) M n) := by
  let : EnoughInjectives X.Modules :=
    ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  apply ExtSectionComparison.mapFrom_bijective
  · intro N
    have heq : (fun f : freeOpen X.ringCatSheaf U ⟶ N =>
        restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f) =
        restrictionHomEquiv U N := funext (restrictionGenerator_comp U)
    change Function.Bijective (fun f : freeOpen X.ringCatSheaf U ⟶ N =>
      restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f)
    rw [heq]
    exact (restrictionHomEquiv U N).bijective
  · intro I hI n x
    let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj I) :=
      @ModuleFlasque.injective_isFlasque _ X.ringCatSheaf I hI
    exact flasque_ext_zero U.toScheme.ringCatSheaf n (I.restrict U.ι) x

end
end MaximalSeshadri.RestrictionCohomology

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u w
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

lemma freeOpen_isPushout (U V : Opens X) :
    ((Opens.mayerVietorisSquare U V).toSquare.map (freeOpenFunctor R)).IsPushout := by
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro M
  have h := (Opens.mayerVietorisSquare U V).sheafCondition_of_sheaf
    ((sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M))
  apply (Square.IsPullback.iff_of_equiv _ _
    (freeOpenEquiv R M (U ⊔ V)) (freeOpenEquiv R M U)
    (freeOpenEquiv R M V) (freeOpenEquiv R M (U ⊓ V))
    ?_ ?_ ?_ ?_).mpr h
  all_goals
    ext f
    exact freeOpenEquiv_naturality R M _ f

def shortComplex (U V : Opens X) : ShortComplex (SheafOfModules.{u} R) where
  X₁ := freeOpen R (U ⊓ V)
  X₂ := freeOpen R U ⊞ freeOpen R V
  X₃ := freeOpen R (U ⊔ V)
  f := biprod.lift (freeOpenMap R (homOfLE inf_le_left))
    (-(freeOpenMap R (homOfLE inf_le_right)))
  g := biprod.desc (freeOpenMap R (homOfLE le_sup_left))
    (freeOpenMap R (homOfLE le_sup_right))
  zero := ((Opens.mayerVietorisSquare U V).toSquare.map
    (freeOpenFunctor R)).cokernelCofork.condition

instance shortComplex_mono (U V : Opens X) : Mono (shortComplex R U V).f := by
  have : Mono ((shortComplex R U V).f ≫ biprod.snd) := by
    dsimp [shortComplex]
    simp only [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

lemma shortComplex_shortExact (U V : Opens X) : (shortComplex R U V).ShortExact := by
  have h := (freeOpen_isPushout R U V).isColimitCokernelCofork
  have he : (shortComplex R U V).Exact ∧ Epi (shortComplex R U V).g :=
    (shortComplex R U V).exact_and_epi_g_iff_g_is_cokernel.mpr ⟨h⟩
  let := he.2
  exact ⟨he.1⟩

end
end MaximalSeshadri.ModuleMayerVietoris


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_FiniteCover
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.FiniteCoverCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]

attribute [local instance] OAI.MaximalSeshadri.FiniteCoverCohomology.hasExtScheme
theorem affine_open_ext_zero (U : X.Opens) (hU : IsAffineOpen U)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Ext.{u+1} (C := X.Modules)
      (freeOpenModule U) M (n+1)) : x = 0 := by
  let : IsAffine U := hU
  let : IsNoetherian U := ⟨⟩
  let f : Ext.{u+1} (C := X.Modules) (freeOpenModule U) M (n+1) →+
      Ext.{u+1} (C := U.toScheme.Modules) (AffineCohomology.structureSheafUnit U)
        (M.restrict U.ι) (n+1) :=
    ExtSectionComparison.mapFrom (Scheme.Modules.restrictFunctor U.ι)
      (RestrictionCohomology.restrictionGenerator U) M (n+1)
  apply (RestrictionCohomology.restriction_ext_bijective U M (n+1)).injective
  change f x = f 0
  rw [map_zero]
  exact AffineSchemeCohomology.affine_ext_zero U (M.restrict U.ι) n (f x)

end
end MaximalSeshadri.FiniteCoverCohomology

namespace MaximalSeshadri.FreeOpenUnit
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque FlasqueCohomology
universe u v

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def freeTopIso : freeOpen R ⊤ ≅ SheafOfModules.unit R :=
  isoFromHomEquiv
    (fun M => (freeOpenEquiv R M ⊤).trans (globalHomEquiv R M).symm)
    (by
      intro M N f g
      apply (globalHomEquiv R N).injective
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, globalHomEquiv_comp]
      rfl)

end
end MaximalSeshadri.FreeOpenUnit

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SurfaceCech
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

lemma freeOpenMap_comp {U V W : Opens X} (h : U ⟶ V) (g : V ⟶ W) :
    freeOpenMap R h ≫ freeOpenMap R g = freeOpenMap R (h ≫ g) := by
  exact ((freeOpenFunctor R).map_comp h g).symm

end
end MaximalSeshadri.ModuleMayerVietoris

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque ModuleMayerVietoris

variable {X : Scheme.{0}}

attribute [local instance] OAI.MaximalSeshadri.Geometry.surfaceCechLinear
attribute [local instance] OAI.MaximalSeshadri.Geometry.surfaceCechHasExt
local instance surfaceCechFreeHomGroup_r7a40b1_1 (target : X.Modules) (chart : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  Preadditive.homGroup (C := X.Modules) _ _
local instance surfaceCechFreeHomModule_r7a40b1_1 (target : X.Modules) (chart : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  sheafHomModule X _ _
def openBoundary (M : X.Modules) (U V : X.Opens) (n : ℕ) :
    Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule (U ⊓ V)) M n →ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule (U ⊔ V)) M (n+1) :=
  (shortComplex_shortExact (X := X.carrier) X.ringCatSheaf U V).extClass.precompOfLinear Γ(X,⊤) M
    (by omega)

def overlapIso (U V W : X.Opens) :
    FiniteCoverCohomology.freeOpenModule ((U ⊓ W) ⊔ (V ⊓ W)) ≅
      FiniteCoverCohomology.freeOpenModule ((U ⊔ V) ⊓ W) :=
  (freeOpenFunctor (X := X.carrier) X.ringCatSheaf).mapIso (eqToIso (show ((U ⊓ W) ⊔ (V ⊓ W)) = ((U ⊔ V) ⊓ W) from
    (inf_sup_right U V W).symm))

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionChart
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X : Scheme}

def sectionFrameOn {M : X.Modules} (s : O X ⟶ M) (U : X.Opens)
    (hU : U ≤ SectionOpens.isoOpen s) : M.restrict U.ι ≅ O U.toScheme :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hU).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hU) (SectionOpens.isoOpen s).ι).app M ≪≫
      restrictFrame (X.homOfLE hU) (sectionFrame s)

lemma sectionFrameOn_coefficient {M : X.Modules} (s t : O X ⟶ M) (U : X.Opens)
    (hU : U ≤ SectionOpens.isoOpen s) :
    coefficient (sectionFrameOn s U hU) (restrictSection U.ι t) =
      (X.homOfLE hU).appTop (coefficient (sectionFrame s)
        (restrictSection (SectionOpens.isoOpen s).ι t)) := by
  unfold sectionFrameOn
  rw [coefficient_transport]
  change coefficient
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE hU) (SectionOpens.isoOpen s).ι).app M ≪≫
      restrictFrame (X.homOfLE hU) (sectionFrame s))
    (restrictSection U.ι t ≫ (Scheme.Modules.restrictFunctorCongr
      (X.homOfLE_ι hU).symm).hom.app M) = _
  rw [restrictSection_congr, coefficient_restrict_comp]

lemma sectionFrameOn_normalized {M : X.Modules} (s : O X ⟶ M) (U : X.Opens)
    (hU : U ≤ SectionOpens.isoOpen s) :
    coefficient (sectionFrameOn s U hU) (restrictSection U.ι s) = 1 := by
  rw [sectionFrameOn_coefficient, sectionFrame_normalized, map_one]

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PlaneCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.moduleSectionEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {σ : Type} {X : Scheme.{0}} {M : X.Modules}

def ratioOn (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) : Γ(U.toScheme,⊤) :=
  coefficient (sectionFrameOn (s i) U hi) (restrictSection U.ι (s j))

@[simp] lemma ratioOn_full (s : σ → (O X ⟶ M)) (i j : σ) :
    ratioOn s i j (SectionOpens.isoOpen (s i)) le_rfl =
      coefficient (sectionFrame (s i)) (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) := by
  rw [ratioOn, sectionFrameOn_coefficient, Scheme.homOfLE_rfl]
  rfl

@[simp] lemma ratioOn_self (s : σ → (O X ⟶ M)) (i : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) : ratioOn s i i U hi = 1 :=
  sectionFrameOn_normalized (s i) U hi

def ratioUnitOn (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j)) :
    Γ(U.toScheme,⊤)ˣ :=
  frameChange (sectionFrameOn (s j) U hj) (sectionFrameOn (s i) U hi)

@[simp] lemma ratioUnitOn_val (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j)) :
    (ratioUnitOn s i j U hi hj : Γ(U.toScheme,⊤)) = ratioOn s i j U hi := by
  have h := coefficient_change (sectionFrameOn (s j) U hj)
    (sectionFrameOn (s i) U hi) (restrictSection U.ι (s j))
  dsimp only [ratioUnitOn, ratioOn]
  simpa only [sectionFrameOn_normalized, mul_one] using h.symm

end
end MaximalSeshadri.Projective

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PlaneProjectionModule
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.LaurentPlane MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

abbrev planeTriple (s : Fin 3 → (O X ⟶ M)) : X.Opens :=
  tripleOpen (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
    (SectionOpens.isoOpen (s 0))

lemma planeTriple_le (s : Fin 3 → (O X ⟶ M)) (i : Fin 3) :
    planeTriple s ≤ SectionOpens.isoOpen (s i) := by
  fin_cases i
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_right.trans inf_le_left

end
end MaximalSeshadri.Projective

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlanePairToric
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

abbrev planePair (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) (i j : Fin 3) :=
  (chartRes k L.sheaf (le_inf (planeTriple_le s i) (planeTriple_le s j))).range

end
end MaximalSeshadri.Projective

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_TripleComplex
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

abbrev tripleVertices (U V W : Opens X) := freeOpen R U ⊞ (freeOpen R V ⊞ freeOpen R W)
abbrev triplePairs (U V W : Opens X) := freeOpen R (U ⊓ V) ⊞ (freeOpen R (U ⊓ W) ⊞ freeOpen R (V ⊓ W))
def tripleD (U V W : Opens X) : triplePairs R U V W ⟶ tripleVertices R U V W :=
  biprod.desc
    (freeOpenMap R (homOfLE inf_le_left) ≫ biprod.inl -
      freeOpenMap R (homOfLE inf_le_right) ≫ biprod.inl ≫ biprod.inr)
    (biprod.desc
      (-freeOpenMap R (homOfLE inf_le_left) ≫ biprod.inl +
        freeOpenMap R (homOfLE inf_le_right) ≫ biprod.inr ≫ biprod.inr)
      (freeOpenMap R (homOfLE inf_le_left) ≫ biprod.inl ≫ biprod.inr -
        freeOpenMap R (homOfLE inf_le_right) ≫ biprod.inr ≫ biprod.inr))
def tripleG (U V W : Opens X) : tripleVertices R U V W ⟶ freeOpen R ((U ⊔ V) ⊔ W) :=
  biprod.desc (freeOpenMap R (homOfLE (le_sup_left.trans le_sup_left)))
    (biprod.desc (freeOpenMap R (homOfLE (le_sup_right.trans le_sup_left)))
      (freeOpenMap R (homOfLE le_sup_right)))

lemma tripleDG (U V W : Opens X) : tripleD R U V W ≫ tripleG R U V W = 0 := by
  apply biprod.hom_ext'
  · simp [tripleD,tripleG,Preadditive.sub_comp,Category.assoc,freeOpenMap_comp]
  · apply biprod.hom_ext' <;>
      simp [tripleD,tripleG,Preadditive.sub_comp,Preadditive.add_comp,Preadditive.neg_comp,
        Category.assoc,freeOpenMap_comp]

abbrev tripleRelations (U V W : Opens X) := kernel (tripleG R U V W)
def tripleToRelations (U V W : Opens X) : triplePairs R U V W ⟶ tripleRelations R U V W :=
  kernel.lift (tripleG R U V W) (tripleD R U V W) (tripleDG R U V W)

lemma tripleToRelations_cycle {U V W T : Opens X} (hU : T ≤ U) (hV : T ≤ V) (hW : T ≤ W) :
    freeOpenMap R (homOfLE (le_inf hU hV)) ≫ biprod.inl ≫ tripleToRelations R U V W +
    freeOpenMap R (homOfLE (le_inf hU hW)) ≫ biprod.inl ≫ biprod.inr ≫ tripleToRelations R U V W +
    freeOpenMap R (homOfLE (le_inf hV hW)) ≫ biprod.inr ≫ biprod.inr ≫ tripleToRelations R U V W = 0 := by
  apply (cancel_mono (kernel.ι (tripleG R U V W))).mp
  simp only [Preadditive.add_comp,Category.assoc,tripleToRelations,kernel.lift_ι,Limits.zero_comp]
  apply biprod.hom_ext
  · simp [tripleD,Category.assoc,Preadditive.comp_sub,Preadditive.comp_add,
      Preadditive.comp_neg,freeOpenMap_comp]
  · apply biprod.hom_ext <;> simp [tripleD,Category.assoc,Preadditive.comp_sub,
      Preadditive.comp_add,Preadditive.comp_neg,freeOpenMap_comp]

end
end MaximalSeshadri.ModuleMayerVietoris

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_TripleEvaluation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque

variable {K : Type} [Field K] {X : Scheme.{0}}

attribute [local instance] OAI.MaximalSeshadri.Geometry.BaseSections.baseHomModule
local instance instAddCommGroupHomSheafOfModulesOpensCarrierCarrierCommRingCatRingCatSheafFreeOpen_r7a40b1_1 (target : X.Modules) (chart : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  Preadditive.homGroup (C := X.Modules) _ _
local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen_r7a40b1_1 (target : X.Modules) (chart : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  sheafHomModule X _ _
instance freeBaseHomGroup (baseMap : K →+* Γ(X,⊤)) (target : X.Modules)
    (chart : X.Opens) : AddCommGroup (BaseHom baseMap (freeOpen X.ringCatSheaf chart) target) :=
  baseHomGroup baseMap _ _

instance freeBaseHomModule (baseMap : K →+* Γ(X,⊤)) (target : X.Modules)
    (chart : X.Opens) : Module K (BaseHom baseMap (freeOpen X.ringCatSheaf chart) target) :=
  baseHomModule baseMap _ _

def freeBaseEquiv (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    BaseHom k (freeOpen X.ringCatSheaf U) M ≃ₗ[K] Sections k M U where
  toEquiv := (freeOpenLinearEquiv M U).toEquiv
  map_add' := (freeOpenLinearEquiv M U).map_add
  map_smul' r m := (freeOpenLinearEquiv M U).map_smul (k r) m

def homChart (k : K →+* Γ(X,⊤)) (M : X.Modules) {U T : X.Opens} (h : T ≤ U) :
    BaseHom k (freeOpen X.ringCatSheaf U) M →ₗ[K]
      Sections (T.ι.appTop.hom.comp k) (M.restrict T.ι) ⊤ :=
  (chartTop k M T).symm.toLinearMap.comp ((res k M h).comp (freeBaseEquiv k M U).toLinearMap)

lemma homChart_natural (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V T : X.Opens}
    (h : T ≤ V) (g : V ≤ U) (f : freeOpen X.ringCatSheaf U ⟶ M) :
    homChart k M h (freeOpenMap X.ringCatSheaf (homOfLE g) ≫ f) =
      homChart k M (h.trans g) f := by
  change (chartTop k M T).symm
      (res k M h (freeBaseEquiv k M V (freeOpenMap X.ringCatSheaf (homOfLE g) ≫ f))) =
    (chartTop k M T).symm (res k M (h.trans g) (freeBaseEquiv k M U f))
  apply congrArg (chartTop k M T).symm
  change res k M h (freeOpenLinearEquiv M V (freeOpenMap X.ringCatSheaf (homOfLE g) ≫ f)) = _
  rw [freeOpenLinearEquiv_naturality]
  exact res_comp k M h g _

lemma homChart_range (k : K →+* Γ(X,⊤)) (M : X.Modules) {U T : X.Opens} (h : T ≤ U) :
    (homChart k M h).range = (chartRes k M h).range := by
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    refine ⟨(chartTop k M U).symm (freeBaseEquiv k M U f),?_⟩
    apply (chartTop k M T).injective
    rw [chartTop_nested,LinearEquiv.apply_symm_apply]
    exact ((chartTop k M T).apply_symm_apply _).symm
  · rintro _ ⟨m,rfl⟩
    refine ⟨(freeBaseEquiv k M U).symm (chartTop k M U m),?_⟩
    apply (chartTop k M T).injective
    simp only [homChart,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    rw [chartTop_nested]

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneRelationCycles
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames ModuleFlasque ModuleMayerVietoris MaximalSeshadri.Projective MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
attribute [local instance] baseHomModule

abbrev planeRelations {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) : X.Modules :=
  tripleRelations X.ringCatSheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
abbrev planeVertices {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) : X.Modules :=
  tripleVertices X.ringCatSheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
abbrev planeRelIota {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) :
    planeRelations s ⟶ planeVertices s :=
  kernel.ι (tripleG X.ringCatSheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2)))
abbrev planeRelPi {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) :
    (show X.Modules from triplePairs X.ringCatSheaf (SectionOpens.isoOpen (s 0))
      (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))) ⟶ planeRelations s :=
  tripleToRelations X.ringCatSheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))

def relationA (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    BaseHom k (planeRelations s) L.sheaf →ₗ[K] planePair k s L 0 1 :=
  ((homChart k L.sheaf (le_inf (planeTriple_le s 0) (planeTriple_le s 1))).comp
    (basePrecomp k L.sheaf (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s))).codRestrict _ (by
      intro f; change _ ∈ (chartRes k L.sheaf _).range; rw [← homChart_range]; exact ⟨_,rfl⟩)
def relationB (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    BaseHom k (planeRelations s) L.sheaf →ₗ[K] planePair k s L 0 2 :=
  ((homChart k L.sheaf (le_inf (planeTriple_le s 0) (planeTriple_le s 2))).comp
    (basePrecomp k L.sheaf (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫
      biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s))).codRestrict _ (by
      intro f; change _ ∈ (chartRes k L.sheaf _).range; rw [← homChart_range]; exact ⟨_,rfl⟩)
def relationC (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    BaseHom k (planeRelations s) L.sheaf →ₗ[K] planePair k s L 1 2 :=
  ((homChart k L.sheaf (le_inf (planeTriple_le s 1) (planeTriple_le s 2))).comp
    (basePrecomp k L.sheaf (biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫
      biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s))).codRestrict _ (by
      intro f; change _ ∈ (chartRes k L.sheaf _).range; rw [← homChart_range]; exact ⟨_,rfl⟩)

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionTransport
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.moduleSectionEquiv_apply _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme} {M N : X.Modules}

def restrictEndIso (φ : Y ⟶ X) [IsOpenImmersion φ] (a : O X ≅ O X) : O Y ≅ O Y :=
  (Scheme.Modules.restrictUnitIso φ).symm ≪≫
    (Scheme.Modules.restrictFunctor φ).mapIso a ≪≫ Scheme.Modules.restrictUnitIso φ

def endUnit (a : O X ≅ O X) : Γ(X, ⊤)ˣ := frameChange (Iso.refl _) a
@[simp] lemma endUnit_val (a : O X ≅ O X) : (endUnit a : Γ(X, ⊤)) = endValue a.hom := by
  simp [endUnit, frameChange]

end
end MaximalSeshadri.Frames

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PlaneBoundaries
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames ModuleFlasque ModuleMayerVietoris MaximalSeshadri.Projective MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
local instance planeBoundariesFreeHomGroup (target : X.Modules) (chart : X.Opens) :
    AddCommGroup (freeOpen X.ringCatSheaf chart ⟶ target) :=
  Preadditive.homGroup (C := SheafOfModules X.ringCatSheaf) _ _
attribute [local instance] baseHomModule
variable (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X)

abbrev relationBoundaries := (basePrecomp k L.sheaf (planeRelIota s)).range

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_BinaryJetDimension
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators

def binaryJetEquiv (n : ℕ) : JetIndex (Fin 2) n ≃ (i : Fin n) × Fin (i.val+1) where
  toFun d := ⟨⟨d.val.degree,d.property⟩,⟨d.val 0,by change d.val 0 < d.val.degree+1; rw [binary_degree]; omega⟩⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm ![a.2.val,a.1.val-a.2.val],by
    rw [binary_degree]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have h := a.2.isLt
    have h' := a.1.isLt
    omega⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    fin_cases i
    · simp
    · change d.val.degree - d.val 0 = d.val 1
      rw [binary_degree]
      omega
  right_inv a := by
    rcases a with ⟨i,j⟩
    have hd : (Finsupp.equivFunOnFinite.symm ![j.val,i.val-j.val]).degree = i.val := by
      rw [binary_degree]
      simp only [Finsupp.coe_equivFunOnFinite_symm,Matrix.cons_val_zero,Matrix.cons_val_one]
      omega
    exact Sigma.ext (Fin.ext hd) ((Fin.heq_ext_iff (congrArg (·+1) hd)).mpr rfl)

end
end MaximalSeshadri.AlgebraicJets

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_NodalTaylor
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                     
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open AlgebraicJets FormalCoordinates LocalComparison NodalLocal IsLocalRing
open scoped Topology

variable {R : Type*} [CommRing R] [Algebra ℂ R]

def bivariateTaylor (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) : R →ₐ[ℂ] Bivariate ℂ :=
  analyticFormal.comp (analyticPullback q hq)

end
end MaximalSeshadri.AnalyticCoordinates
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ClosedPushforwardEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MaximalSeshadri.ClosedPushforward
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.FlasqueCohomology MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

variable [IsClosedImmersion f]

local instance instHasExtModules_solutions_2_r7a40b1_1 : HasExt.{1} X.Modules := schemeHasExt
attribute [local instance] OAI.MaximalSeshadri.ClosedPushforward.instHasExtModules_solutions_3
lemma cohomologyMap_base_smul (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ)
    (r : ℂ) (x : Ext.{1} (O X) M n) :
    cohomologyMap f M n ((baseScalars (f ≫ p) r) • x) =
      (baseScalars p r) • cohomologyMap f M n x := by
  rw [Ext.smul_eq_comp_mk₀, cohomologyMap_comp, Ext.smul_eq_comp_mk₀,
    Ext.mapExactFunctor_mk₀]
  congr 2
  ext U m
  change Γ(M, f ⁻¹ᵁ U) at m
  change restrictScalar X (f ⁻¹ᵁ U) (baseScalars (f ≫ p) r) • m =
    f.app U (restrictScalar Y U (baseScalars p r)) • m
  rw [scalar_naturality]

def cohomologyLinearMap (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
    cohomology M n →ₗ[ℂ] cohomology ((Scheme.Modules.pushforward f).obj M) n := by
  letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  exact { toFun := cohomologyMap f M n
          map_add' := (cohomologyMap f M n).map_add
          map_smul' := by
            intro r x
            exact cohomologyMap_base_smul f p M n r x }

lemma cohomologyLinearMap_eq (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    ⇑(cohomologyLinearMap f p M n) = cohomologyMap f M n := rfl

def cohomologyEquiv (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
    cohomology M n ≃ₗ[ℂ] cohomology ((Scheme.Modules.pushforward f).obj M) n := by
  exact LinearEquiv.ofBijective (cohomologyLinearMap f p M n)
    (by rw [cohomologyLinearMap_eq]; exact cohomologyMap_bijective f M n)

end
end MaximalSeshadri.ClosedPushforward

end

end OAI
end


