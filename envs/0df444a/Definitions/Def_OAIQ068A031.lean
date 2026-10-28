-- Prove2me | Definitions.Def_OAIQ068A031
-- name    : OAIQ068A031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:08:57.787932+00:00
-- url     : https://prove2.me/theorems/d982cb20-0f2e-42d0-9c03-5876e0773e7e
-- title:
--   Definitions bundle OAIQ068A031 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 63 declarations of OpenAI's Lean: 11 definitions, 1 inductive type or structure, 2 instances and 49 theorems. The definitions and types are `OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.schemeFreeOpen`, `OAI.PiExponent.GeometrySupport.LaurentCechFinite.freeOpenHomAddCommGroup`, `OAI.PiExponent.GeometrySupport.LaurentCechFinite.schemeFreeOpen`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.fullMonomialUnit`, `OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation`, `OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.toLaurent`, `OAI.PiExponent.ProjectiveTwistCech.schemeFreeOpen`, `OAI.PiExponentSeshadri.Projective.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen`, `OAI.PiExponentSeshadri.Projective.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen_1`, `OAI.PiExponentSeshadri.Projective.schemeFreeOpen`, `OAI.PiExponentSeshadri.ProjectiveChartSections.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen`, `OAI.PiExponentSeshadri.ProjectiveChartSections.schemeFreeOpen`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Approximation_InverseFrameRestriction`, `PiExponent_Cohomology_CechExtFinite`, `PiExponent_Cohomology_CechHigher`, `PiExponent_Cohomology_CechOne`, `PiExponent_Cohomology_CurveNormalizationCohomology`, `PiExponent_Cohomology_LaurentCechFinite`, `PiExponent_Cohomology_LaurentExtFinite`, `PiExponent_Cohomology_ProjectiveLaurentTransitions`, `PiExponent_Cohomology_ProjectiveTwistCech`, `PiExponent_Geometry_CurveGlobalMonomialLocal`, `PiExponent_Geometry_PlaceCenteredBranch`, `PiExponent_Geometry_ProjectiveCoordinateConstants`, `PiExponent_Geometry_ProjectiveCoordinateFiniteValues`, `PiExponent_Geometry_ProjectiveCoordinateRatios`, `PiExponent_Geometry_ProjectiveCoordinateScalars`, `PiExponent_Geometry_ProjectiveCoordinateTransitions`, `PiExponent_Geometry_ProjectiveEmbeddingCharts`, `PiExponent_Geometry_ProjectiveFrameNaturality`, `PiExponent_Geometry_ProjectiveFramedSections`, `PiExponent_Geometry_ProjectiveLocalCoefficients`, `PiExponent_Geometry_ProjectiveNegativeScalars`, `PiExponent_Geometry_ProjectiveNegativeTransitions`, `PiExponent_Geometry_ProjectiveTupleCharts`, `PiExponent_Polynomials_CompositePullbackCoefficient`, `PiExponent_Polynomials_PullbackFrameCoefficient`.
--
--   **Imports.** It imports the bundles `OAIQ068A020`, `OAIQ068A021`, `OAIQ068A022`, `OAIQ068A023`, `OAIQ068A024` and `OAIQ068A025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A037`, `OAIQ068A038` and `OAIQ068A039`; the proofs of `OAI_PiExponent_CurveDerivativeVanishing_logarithmic_words_vanish`, `OAI.PiExponent.CurveDerivativeVanishing.logarithmic_words_vanish_q68`, `OAI_PiExponent_CurveDerivativeVanishing_ordinary_words_vanish`, `OAI.PiExponent.CurveDerivativeVanishing.ordinary_words_vanish_q68`, `OAI_PiExponent_CurveInequality_no_fibre_excess_of_constant_coordinate` and `OAI.PiExponent.CurveInequality.no_fibre_excess_of_constant_coordinate_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ068A020
import Definitions.Def_OAIQ068A021
import Definitions.Def_OAIQ068A022
import Definitions.Def_OAIQ068A023
import Definitions.Def_OAIQ068A024
import Definitions.Def_OAIQ068A025

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_InverseFrameRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}} {M N : X.Modules}

lemma pairing_restrict (E : moduleTensor X M N ≅ O X) {U V : X.Opens}
    (h : V ≤ U) (m : Γ(M,U)) (n : Γ(N,U)) :
    X.presheaf.map (homOfLE h).op (E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U m n)) =
      E.hom.app V (PiExponentSeshadri.TensorPure.pure M N V (M.presheaf.map (homOfLE h).op m)
        (N.presheaf.map (homOfLE h).op n)) := by
  have hn := CategoryTheory.congr_fun (E.hom.mapPresheaf.naturality (homOfLE h).op)
    (PiExponentSeshadri.TensorPure.pure M N U m n)
  change E.hom.app V ((moduleTensor X M N).presheaf.map (homOfLE h).op
    (PiExponentSeshadri.TensorPure.pure M N U m n)) =
    X.presheaf.map (homOfLE h).op (E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U m n)) at hn
  exact hn.symm.trans (congrArg (fun z => E.hom.app V z)
    (pure_restrict M N (homOfLE h) m n))

end
end PiExponent.InverseFrames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechOne
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechOne

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

theorem hom_ext {J : Type u} (U : J → Opens X) (V : Opens X)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (M : SheafOfModules.{u} R) (f g : freeOpen R V ⟶ M)
    (hfg : ∀ i, restrictHom R (hUV i) f = restrictHom R (hUV i) g) : f = g := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := (SheafOfModules.toSheaf R).obj M
  apply (freeOpenEquiv R M V).injective
  apply F.eq_of_locally_eq' U V (fun i => homOfLE (hUV i)) hcover
  intro i
  change M.val.map (homOfLE (hUV i)).op _ = M.val.map (homOfLE (hUV i)).op _
  rw [← freeOpenEquiv_naturality, ← freeOpenEquiv_naturality]
  exact congrArg (freeOpenEquiv R M (U i)) (hfg i)

theorem lift_of_ext_one_zero (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) (U : Opens X)
    (hzero : ∀ x : Ext.{u+1} (freeOpen R U) S.X₁ 1, x = 0)
    (s : freeOpen R U ⟶ S.X₃) : ∃ t : freeOpen R U ⟶ S.X₂, t ≫ S.g = s := by
  obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₃ (freeOpen R U) hS (Ext.mk₀ s)
    (n₁ := 1) rfl (hzero _)
  obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective _ _).surjective t
  refine ⟨t, ?_⟩
  apply (Ext.mk₀_bijective _ _).injective
  simpa only [Ext.mk₀_comp_mk₀] using ht

end
end PiExponent.GeometrySupport.CechOne

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechHigher
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechHigher

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open CechOne
open scoped BigOperators

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

theorem lift_cochain (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (q : ℕ)
    (hzero : ∀ (t : Fin (q + 1) → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (c : Cochain R U S.X₃ q) :
    ∃ b : Cochain R U S.X₂ q, map R U S.X₂ S.g b = c := by
  classical
  choose b hb using fun t =>
    lift_of_ext_one_zero R S hS (intersection U t) (hzero t) (c t)
  exact ⟨b, funext hb⟩

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

end
end PiExponent.GeometrySupport.CechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechExtFinite
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechExtFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Abelian
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
variable {K : Type*} [Field K] (ρ : K →+* Γ(X,⊤))

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

lemma locallyAcyclic_quotient (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Injective S.X₂] (hlocal : LocallyAcyclic U S.X₁) : LocallyAcyclic U S.X₃ := by
  intro q t k y
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃
    (schemeFreeOpen (CechHigher.intersection U t)) hS y
    (n₁ := k+2) rfl (hlocal q t (k+1) _)
  rw [Ext.eq_zero_of_injective z, Ext.zero_comp] at hz
  exact hz.symm

open CechLinear

end
end PiExponent.GeometrySupport.CechExtFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveNormalizationCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponent.CurveZeroPole
open PiExponentSeshadri.Geometry

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E]

local instance instHasExtModulesParameterCurve : HasExt.{1} (parameterCurve f hf).Modules := HasExt.standard _

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveTwistCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveTwistCech

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open PiExponent.ProjectiveMonomialCech

universe u
variable {X : Scheme.{u}} {ι K : Type u} [Fintype ι] [AddCommGroup K]

abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

structure LaurentCechPresentation (U : ι → X.Opens) (M : X.Modules) (d : ℤ) where
  coefficient : ∀ q (t : Fin (q + 1) → ι),
    (schemeFreeOpen (GeometrySupport.CechHigher.intersection U t) ⟶ M) →+
      Laurent ι K d
  injective : ∀ q t, Function.Injective (coefficient q t)
  regular : ∀ q t b, RegularOn (Set.range t) (coefficient q t b)
  surjective : ∀ q t p, RegularOn (Set.range t) p → ∃ b, coefficient q t b = p
  restriction : ∀ q (t : Fin (q + 2) → ι) (k : Fin (q + 2)) b,
    coefficient (q + 1) t
      (GeometrySupport.CechOne.restrictHom X.ringCatSheaf
        (GeometrySupport.CechHigher.faceLE U t k) b) =
      coefficient q (t ∘ k.succAbove) b

namespace LaurentCechPresentation

variable {U : ι → X.Opens} {M : X.Modules} {d : ℤ}
    (P : LaurentCechPresentation (K := K) U M d)

def toLaurent {q : ℕ} (c : GeometrySupport.CechHigher.Cochain X.ringCatSheaf U M q) :
    ProjectiveMonomialCechHigher.Cochain ι (Laurent ι K d) q :=
  fun t => P.coefficient q t (c t)

theorem toLaurent_differential {q : ℕ}
    (c : GeometrySupport.CechHigher.Cochain X.ringCatSheaf U M q) :
    P.toLaurent (GeometrySupport.CechHigher.differential X.ringCatSheaf U M c) =
      ProjectiveMonomialCechHigher.differential (P.toLaurent c) := by
  funext t
  simp only [toLaurent, GeometrySupport.CechHigher.differential,
    ProjectiveMonomialCechHigher.differential]
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [map_zsmul, P.restriction]

end LaurentCechPresentation

end
end PiExponent.ProjectiveTwistCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_LaurentCechFinite
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.LaurentCechFinite
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open ProjectiveTwistCech

variable {X : Scheme.{0}} {ι K : Type} [Fintype ι] [Field K]
  {U : ι → X.Opens} {M : X.Modules} {d : ℤ}

abbrev schemeFreeOpen (V : X.Opens) : X.Modules :=
  PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V

@[instance_reducible] def freeOpenHomAddCommGroup (V : X.Opens) (N : X.Modules) :
    AddCommGroup (PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V ⟶ N) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen V ⟶ N))

attribute [local instance] freeOpenHomAddCommGroup

end
end PiExponent.GeometrySupport.LaurentCechFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_LaurentExtFinite
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ActualLaurentExtFinite
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {ι K : Type} [Fintype ι] [Field K]
variable {U : ι → X.Opens} {M : X.Modules} {d : ℤ}
variable (ρ : K →+* Γ(X,⊤)) (P : ProjectiveTwistCech.LaurentCechPresentation (K := K) U M d)
abbrev schemeFreeOpen (V : X.Opens) : X.Modules :=
  PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V

end
end PiExponent.GeometrySupport.ActualLaurentExtFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveLaurentTransitions
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveLaurentTransitions
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
variable {ι R : Type*} [Fintype ι] [CommRing R]

theorem zeroDegreeExponent_coordinate (i : ι) (j : {j : ι // j ≠ i}) :
    zeroDegreeExponent i (natExponentHom i (Finsupp.single j 1)) =
      standardExponent j.val 1 - standardExponent i 1 := by
  classical
  funext k
  by_cases hk : k = i
  · subst k
    simp [zeroDegreeExponent, fullEncode_self, natExponentHom, standardExponent,
      Ne.symm j.property, Finsupp.single_apply]
  · change (fullEncode i 0 _).val k = _
    rw [show (fullEncode i 0 _).val k =
      natExponentHom i (Finsupp.single j 1) ⟨k, hk⟩ from fullEncode_other i 0 _ ⟨k, hk⟩]
    simp [natExponentHom, standardExponent, hk, Finsupp.single_apply, Subtype.ext_iff, eq_comm]

theorem laurentToFull_injective (d : ℤ) : Function.Injective (laurentToFull (ι := ι) (R := R) d) :=
  AddMonoidAlgebra.coeffAddEquiv.symm.injective.comp
    (Finsupp.mapDomain_injective Subtype.val_injective)

@[simp] theorem overlapToFull_X (i : ι) (s : Finset {j : ι // j ≠ i})
    (k : {j : ι // j ≠ i}) :
    overlapToFull (R := R) i s (algebraMap _ _ (MvPolynomial.X (R := R) k)) =
      AddMonoidAlgebra.single (standardExponent k.val 1 - standardExponent i 1) 1 := by
  simp [overlapToFull, chartToFull, zeroDegreeExponent_coordinate]

@[simp] theorem overlapToFull_C (i : ι) (s : Finset {j : ι // j ≠ i}) (r : R) :
    overlapToFull (R := R) i s (algebraMap _ _ (MvPolynomial.C (σ := {j : ι // j ≠ i}) r)) =
      AddMonoidAlgebra.single 0 r := by
  simp only [overlapToFull, RingHom.comp_apply, overlapToGroupAlgebra_base]
  change AddMonoidAlgebra.mapDomain (zeroDegreeExponent i)
    (AddMonoidAlgebra.mapDomain (natExponentHom i) (AddMonoidAlgebra.single 0 r)) = _
  rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.mapDomain_single]
  simp only [map_zero]

theorem overlapToFull_natural_of_generators (i j : ι)
    (s : Finset {k : ι // k ≠ i}) (t : Finset {k : ι // k ≠ j})
    (f : Localization.Away (chartProduct (R := R) i s) →+*
      Localization.Away (chartProduct (R := R) j t))
    (hC : ∀ r : R, overlapToFull j t
      (f (algebraMap _ _ (MvPolynomial.C (σ := {k : ι // k ≠ i}) r))) =
        AddMonoidAlgebra.single 0 r)
    (hX : ∀ k : {k : ι // k ≠ i}, overlapToFull j t
      (f (algebraMap _ _ (MvPolynomial.X (R := R) k))) =
        AddMonoidAlgebra.single (standardExponent k.val 1 - standardExponent i 1) 1) :
    (overlapToFull j t).comp f = overlapToFull i s := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (chartProduct (R := R) i s))
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa only [RingHom.comp_apply, overlapToFull_C] using hC r
  · intro k
    simpa only [RingHom.comp_apply, overlapToFull_X] using hX k

theorem overlapLaurent_change_pivot (i j : ι) (d : ℤ)
    (s : Finset {k : ι // k ≠ i}) (t : Finset {k : ι // k ≠ j})
    (f : Localization.Away (chartProduct (R := R) i s) →+*
      Localization.Away (chartProduct (R := R) j t))
    (hf : (overlapToFull j t).comp f = overlapToFull i s)
    (u : Localization.Away (chartProduct (R := R) j t))
    (hu : overlapToFull j t u =
      AddMonoidAlgebra.single (standardExponent i d - standardExponent j d) 1)
    (z : Localization.Away (chartProduct (R := R) i s)) :
    overlapLaurent j d t (u * f z) = overlapLaurent i d s z := by
  apply laurentToFull_injective d
  rw [laurentToFull_overlapLaurent, laurentToFull_overlapLaurent, map_mul, hu, ← mul_assoc,
    AddMonoidAlgebra.single_mul_single]
  have he : standardExponent j d + (standardExponent i d - standardExponent j d) =
      standardExponent i d := by abel
  rw [he, one_mul]
  have hz := RingHom.congr_fun hf z
  change overlapToFull j t (f z) = overlapToFull i s z at hz
  rw [hz]

def fullMonomialUnit (a : ι → ℤ) : (FullGroupAlgebra (ι := ι) (R := R))ˣ where
  val := AddMonoidAlgebra.single a 1
  inv := AddMonoidAlgebra.single (-a) 1
  val_inv := by rw [AddMonoidAlgebra.single_mul_single]; simp only [add_neg_cancel, one_mul]; rfl
  inv_val := by rw [AddMonoidAlgebra.single_mul_single]; simp only [neg_add_cancel, one_mul]; rfl

theorem overlapToFull_ratio (i j k : ι) (t : Finset {l : ι // l ≠ j})
    (x y yinv : Localization.Away (chartProduct (R := R) j t))
    (hx : overlapToFull j t x =
      AddMonoidAlgebra.single (standardExponent k 1 - standardExponent j 1) 1)
    (hy : overlapToFull j t y =
      AddMonoidAlgebra.single (standardExponent i 1 - standardExponent j 1) 1)
    (hinv : y * yinv = 1) :
    overlapToFull j t (x * yinv) =
      AddMonoidAlgebra.single (standardExponent k 1 - standardExponent i 1) 1 := by
  have hcancel := congrArg (overlapToFull j t) hinv
  rw [map_mul, hy, map_one] at hcancel
  have hunit : IsUnit (AddMonoidAlgebra.single
      (standardExponent i 1 - standardExponent j 1) (1 : R)) :=
    (fullMonomialUnit (R := R) (standardExponent i 1 - standardExponent j 1)).isUnit
  have hi : overlapToFull j t yinv = AddMonoidAlgebra.single
      (standardExponent j 1 - standardExponent i 1) 1 := by
    apply hunit.mul_left_cancel
    rw [hcancel, AddMonoidAlgebra.single_mul_single]
    have he : standardExponent i 1 - standardExponent j 1 +
        (standardExponent j 1 - standardExponent i 1) = 0 := by abel
    rw [he, one_mul]
    rfl
  rw [map_mul, hx, hi, AddMonoidAlgebra.single_mul_single]
  have he : standardExponent k 1 - standardExponent j 1 +
      (standardExponent j 1 - standardExponent i 1) =
      standardExponent k 1 - standardExponent i 1 := by abel
  rw [he, one_mul]

end
end PiExponent.GeometrySupport.ProjectiveLaurentTransitions

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveFrameNaturality
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology Frames
variable {X : Scheme} {U V : X.Opens} (M : X.Modules)

lemma framedHomCoefficientsEquiv_restrict (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (b : freeOpen X.ringCatSheaf U ⟶ M) :
    framedHomCoefficientsEquiv V M (restrictOpenFrame h e)
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
      X.presheaf.map (homOfLE h).op (framedHomCoefficientsEquiv U M e b) := by
  change framedCoefficientsEquiv V M (restrictOpenFrame h e)
    (freeOpenEquiv X.ringCatSheaf M V
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b)) =
    X.presheaf.map (homOfLE h).op
      (framedCoefficientsEquiv U M e (freeOpenEquiv X.ringCatSheaf M U b))
  erw [freeOpenEquiv_naturality]
  exact framedCoefficientsEquiv_restrict M h e _

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateConstants
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri
namespace Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K] (i : σ)
lemma coordinatesMap_pullback_constant {Y : Scheme}
    (k : K →+* Γ(Y,⊤)) (a : σ → Γ(Y,⊤)) (hi : a i = 1)
    (g : Y ⟶ Spec (CommRingCat.of (PolyChart (R := K) i)))
    (heq : coordinatesMap Y k a i hi =
      g ≫ Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide))
    (r : K) :
    k r = ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
      g.appTop).hom (chartConstants i r) := by
  let F := evalAway (𝒜 := PolyGrade K σ) (eval₂Hom k a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(Y,⊤))))
  have hfactor : Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom F) = g := by
    apply (cancel_mono (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide))).1
    simpa only [coordinatesMap, fromUnitCoordinate, Category.assoc] using heq
  have hf := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
    Scheme.Hom.appTop g) hfactor
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id] at hf
  have h := congrArg (fun g : CommRingCat.of (PolyChart (R := K) i) ⟶ _ =>
    g.hom (chartConstants i r)) hf
  change F (chartConstants i r) = _ at h
  rw [evalAway_constants i k a hi r] at h
  exact h
variable {X : Scheme} (M : X.Modules) (k : K →+* Γ(X,⊤))
    (s : σ → (PiExponentSeshadri.Frames.O X ⟶ M))
    (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
    (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateSectionRingEquiv_symm_constant (r : K) :
    (coordinateSectionRingEquiv M k s hc f hf i).symm (C r) =
      X.presheaf.map (homOfLE (show SectionOpens.isoOpen (s i) ≤ ⊤ from le_top)).op (k r) := by
  let U := SectionOpens.isoOpen (s i)
  let g := coordinateSectionChartIso M k s hc f hf i
  have h := coordinatesMap_pullback_constant i (U.ι.appTop.hom.comp k)
    (fun j => PiExponentSeshadri.Frames.coefficient (sectionFrame (s i))
      (PiExponentSeshadri.Frames.restrictSection U.ι (s j)))
    (sectionFrame_normalized (s i)) g.hom
    ((sectionsMorphism_local k s hc i).symm.trans
      (coordinateSectionChartIso_hom_away M k s hc f hf i).symm) r
  have hp : (polynomialChartEquiv (R := K) i).symm (C r) = chartConstants i r := by
    apply (polynomialChartEquiv i).injective
    rw [RingEquiv.apply_symm_apply]
    exact (chartToPoly_constants i r).symm
  change U.topIso.hom ((schemeIsoGammaEquiv g).symm
    ((polynomialChartEquiv i).symm (C r))) = _
  rw [hp]
  change U.ι.appTop (k r) = (schemeIsoGammaEquiv g).symm (chartConstants i r) at h
  rw [← h]
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) (k r) = _
  erw [← Functor.map_comp]
  rfl

lemma coordinateSectionRingEquiv_constant (r : K) :
    coordinateSectionRingEquiv M k s hc f hf i
      (X.presheaf.map (homOfLE (show SectionOpens.isoOpen (s i) ≤ ⊤ from le_top)).op (k r)) = C r := by
  rw [← coordinateSectionRingEquiv_symm_constant i M k s hc f hf r,
    RingEquiv.apply_symm_apply]

end

end Projective
end PiExponentSeshadri

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PullbackFrameCoefficient
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.PullbackFrameCoefficient

theorem exists_frame_of_factors_through_open {X Y : Scheme.{0}}
    (U : X.Opens) (g : Y ⟶ U.toScheme)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ eF : (Scheme.Modules.pullback (g ≫ U.ι)).obj M ≅ O Y,
      ∀ s : O X ⟶ M,
      coefficient eF (pullbackSection (g ≫ U.ι) s) =
        g.appTop (coefficient e (restrictSection U.ι s)) := by
  let F : X.Modules ⥤ Y.Modules := Scheme.Modules.pullback (g ≫ U.ι)
  let G : X.Modules ⥤ Y.Modules :=
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback g
  let v : F ≅ G := (Scheme.Modules.pullbackComp g U.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
      (Scheme.Modules.pullback g)
  let uG : G.obj (O X) ≅ O Y :=
    (Scheme.Modules.pullback g).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso g
  obtain ⟨eF, he⟩ := exists_frame_natIso_all F G v (pullbackUnitIso (g ≫ U.ι)) uG
    (pullbackFrame g e)
  refine ⟨eF, fun s => ?_⟩
  have hs := he s
  have hs' : coefficient eF (pullbackSection (g ≫ U.ι) s) =
      coefficient (pullbackFrame g e) (pullbackSection g (restrictSection U.ι s)) := by
    let S : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let Q : U.toScheme.Modules ⥤ Y.Modules := Scheme.Modules.pullback g
    let a : S.obj (O X) ≅ O U.toScheme := Scheme.Modules.restrictUnitIso U.ι
    let q : Q.obj (O U.toScheme) ≅ O Y := pullbackUnitIso g
    have hr : pullbackSection g (restrictSection U.ι s) = uG.inv ≫ G.map s := by
      change q.inv ≫ Q.map (a.inv ≫ S.map s) = (q.inv ≫ Q.map a.inv) ≫ Q.map (S.map s)
      exact (congrArg (fun k => q.inv ≫ k) (Q.map_comp a.inv (S.map s))).trans
        (Category.assoc q.inv (Q.map a.inv) (Q.map (S.map s))).symm
    exact hs.trans (congrArg (coefficient (pullbackFrame g e)) hr).symm
  rw [hs', coefficient_pullback]

end PiExponent.PullbackFrameCoefficient

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveLocalCoefficients
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_diagonal_affine _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_noetherian _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_separated _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.Projective PiExponentSeshadri.LineBundleGluing

namespace PiExponent.ProjectiveLocalCoefficients


variable {R A σ : Type} [CommRing R] [CommRing A]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem chart_inverse_ratio (i j : σ) :
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop
      (ProjectiveO1.chartRatios i j) =
        (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv
          (chartCoordinate (R := R) i j) := by
  have h := ProjectiveO1.coordinateOpen_pullback (R := R) i
  have hc := congrArg (fun q => q ≫
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop) h
  simp only [Category.assoc, ← Scheme.Hom.comp_appTop,
    Iso.inv_hom_id, Scheme.Hom.id_appTop, Category.comp_id] at hc
  have hv := ConcreteCategory.congr_hom hc (chartCoordinate (R := R) i j)
  change (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv
      (chartCoordinate (R := R) i j) =
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop
      ((ProjectiveO1.coordinateOpen i).topIso.inv
        (Proj.awayToSection (PolyGrade R σ) (X i) (chartCoordinate (R := R) i j))) at hv
  rw [ProjectiveO1.awayToSection_coordinate] at hv
  exact hv.symm

end PiExponent.ProjectiveLocalCoefficients

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveGlobalMonomialLocal
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveLocalCoefficients
open AlgebraicGeometry CategoryTheory MvPolynomial
open PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R A B σ : Type} [CommRing R] [CommRing A] [CommRing B]

theorem normalizedMap_natural (h : A →+* B) (k : R →+* A)
    (y : σ → A) (i : σ) (hi : y i = 1) :
    Spec.map (CommRingCat.ofHom h) ≫ normalizedMap k y i hi =
      normalizedMap (h.comp k) (fun j => h (y j)) i (by rw [hi, map_one]) := by
  unfold normalizedMap
  rw [fromUnitCoordinate_natural]
  congr 1
  exact coordinates_eval_natural h k y

theorem normalizedMap_scale (k : R →+* A) (a b : σ → A)
    (i j : σ) (hi : a i = 1) (hj : b j = 1)
    (c : Aˣ) (hscale : ∀ q, b q = (c : A) * a q) :
    normalizedMap k a i hi = normalizedMap k b j hj := by
  let f := eval₂Hom k a
  let g := eval₂Hom k b
  have hf : IsUnit (f (MvPolynomial.X (R := R) i)) := by
    simpa only [f, eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : A))
  have hg : IsUnit (g (MvPolynomial.X (R := R) i)) := by
    simpa only [g, eval₂Hom_X', hscale i, hi, mul_one] using c.isUnit
  have hg' : IsUnit (g (MvPolynomial.X (R := R) j)) := by
    simpa only [g, eval₂Hom_X', hj] using (isUnit_one : IsUnit (1 : A))
  have H : ∀ n p, p ∈ homogeneousSubmodule σ R n →
      g p = (c : A) ^ n * f p := by
    intro n p hp
    change eval₂ k b p = _
    have hb : b = fun q => (c : A) * a q := funext hscale
    rw [hb]
    exact homogeneous_eval₂_scale hp k a c
  unfold normalizedMap
  exact (fromUnitCoordinate_scale (𝒜 := homogeneousSubmodule σ R) (d := 1) f (by decide) (coordinates_X_mem (K := R) i)
    hf g hg c H).trans
      (fromUnitCoordinate_eq (𝒜 := homogeneousSubmodule σ R) (d := 1) (e := 1) g (by decide) (by decide)
        (coordinates_X_mem (K := R) i) (coordinates_X_mem (K := R) j) hg hg')

end PiExponent.ProjectiveLocalCoefficients

namespace PiExponent.CurveGlobalMonomialLocal
open AlgebraicGeometry CategoryTheory MvPolynomial
open ProjectiveLatticePullback ProjectiveLocalCoefficients WeightedSectionOrder
open WeightedLocalLattice PiExponentSeshadri.Projective
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem genericMonomialMap_comp_projectiveMonomialMap
    {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (x : ι → E) :
    CurveMonomialMap.genericMonomialMap a z hz coordinate hcoordinate x ≫
      WeightedCompactification.projectiveMonomialMap a =
      normalizedMap (algebraMap F E) (monomialCoordinates (F := F) a x) z
        (monomialCoordinates_zero a x z hz) := by
  have heval : (eval₂Hom (algebraMap F E) x).comp
        (WeightedCompactification.affineMonomialMap (R := F) a) =
      eval₂Hom (algebraMap F E) (monomialCoordinates (F := F) a x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [WeightedCompactification.affineMonomialMap]
    · intro b
      simp [WeightedCompactification.affineMonomialMap, monomialCoordinates]
  rw [CurveMonomialMap.genericMonomialMap, Category.assoc,
    WeightedCompactification.affineChartMap_comp_projectiveMonomialMap,
    fromUnitCoordinate_natural]
  unfold normalizedMap
  congr 1

end PiExponent.CurveGlobalMonomialLocal

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceCenteredBranch
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PlaceCenteredBranch

open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole

variable {E ι : Type*} [Field E] [Algebra ℂ E]

theorem lift_aeval (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (f : MvPolynomial ι ℂ) :
    algebraMap (ring p) E (MvPolynomial.aeval (lift p z c hc) f) =
      MvPolynomial.aeval z f := by
  exact MvPolynomial.comp_aeval_apply (f := lift p z c hc)
    (IsScalarTower.toAlgHom ℂ (ring p) E) f

end PiExponent.PlaceCenteredBranch

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateFiniteValues
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateFiniteRingEquiv_constant (i : σ) (a : Finset (ChartVariables i)) (r : K) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤ ⊤ from le_top)).op (k r)) =
      algebraMap _ _ (MvPolynomial.C (σ := ChartVariables i) r) := by
  have h := coordinateFiniteRingEquiv_restrict_apply M s k hc f hf i a
    (X.presheaf.map (homOfLE (show SectionOpens.isoOpen (s i) ≤ ⊤ from le_top)).op (k r))
  rw [coordinateSectionRingEquiv_constant] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  change _ = coordinateFiniteRingEquiv M s k hc f hf i a
    ((X.presheaf.map _ ≫ X.presheaf.map _) (k r))
  rw [← Functor.map_comp]
  rfl

lemma coordinateFiniteRingEquiv_symm_constant (i : σ) (a : Finset (ChartVariables i)) (r : K) :
    (coordinateFiniteRingEquiv M s k hc f hf i a).symm
      (algebraMap _ _ (MvPolynomial.C (σ := ChartVariables i) r)) =
    X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤ ⊤ from le_top)).op (k r) := by
  apply (coordinateFiniteRingEquiv M s k hc f hf i a).injective
  rw [RingEquiv.apply_symm_apply, coordinateFiniteRingEquiv_constant]

lemma coordinateFiniteTransition_constant (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a) (r : K) :
    coordinateFiniteTransition M s k hc f hf i j a b h
      (algebraMap _ _ (MvPolynomial.C (σ := ChartVariables i) r)) =
      algebraMap _ _ (MvPolynomial.C (σ := ChartVariables j) r) := by
  change coordinateFiniteRingEquiv M s k hc f hf j b
    (X.presheaf.map (homOfLE h).op
      ((coordinateFiniteRingEquiv M s k hc f hf i a).symm _)) = _
  rw [coordinateFiniteRingEquiv_symm_constant]
  change coordinateFiniteRingEquiv M s k hc f hf j b
    ((X.presheaf.map _ ≫ X.presheaf.map _) (k r)) = _
  rw [← Functor.map_comp]
  exact coordinateFiniteRingEquiv_constant M s k hc f hf j b r

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateRatios
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry Frames ModuleFlasque RestrictionCohomology
open PiExponentSeshadri.ProjectiveChartSections
variable {X : Scheme} {M : X.Modules}

lemma coordinateRatioOn_eq_coefficient (si sk : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) :
    coordinateRatioOn si sk hi = W.topIso.hom
      (coefficient (restrictOpenFrame hi (sectionFrame si)) (restrictSection W.ι sk)) := by
  rw [restrictOpenFrame_coefficient_global, topIso_hom_restrict]
  rfl

lemma coordinateRatioOn_change (si sj sk : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj) :
    coordinateRatioOn sj sk hj = coordinateRatioOn sj si hj * coordinateRatioOn si sk hi := by
  rw [coordinateRatioOn_eq_coefficient sj sk hj,
    coefficient_change (restrictOpenFrame hi (sectionFrame si)),
    frameChange_restrictOpenFrame hi hj _ _ si (sectionFrame_normalized si),
    map_mul, topIso_hom_restrict, ← coordinateRatioOn_eq_coefficient]
  rfl

lemma coordinateRatioOn_reciprocal (si sj : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj) :
    coordinateRatioOn sj si hj * coordinateRatioOn si sj hi = 1 := by
  rw [← coordinateRatioOn_change si sj sj hi hj, coordinateRatioOn_self]

lemma coordinateRatioOn_restrict (si sk : O X ⟶ M) {U W : X.Opens}
    (hi : U ≤ SectionOpens.isoOpen si) (h : W ≤ U) :
    X.presheaf.map (homOfLE h).op (coordinateRatioOn si sk hi) =
      coordinateRatioOn si sk (h.trans hi) := by
  unfold coordinateRatioOn
  change (X.presheaf.map (homOfLE hi).op ≫ X.presheaf.map (homOfLE h).op) _ = _
  rw [← Functor.map_comp]
  rfl

lemma framedHomCoefficientsEquiv_change (W : X.Opens) (N : X.Modules)
    (e f : N.restrict W.ι ≅ structureSheaf W.toScheme)
    (b : freeOpen X.ringCatSheaf W ⟶ N) :
    framedHomCoefficientsEquiv W N f b =
      W.topIso.hom (frameChange e f : Γ(W.toScheme,⊤)) *
        framedHomCoefficientsEquiv W N e b := by
  let x := (restrictionSectionsIso W N).inv (freeOpenEquiv X.ringCatSheaf N W b)
  change W.topIso.hom (f.hom.app ⊤ x) =
    W.topIso.hom (frameChange e f : Γ(W.toScheme,⊤)) * W.topIso.hom (e.hom.app ⊤ x)
  erw [← map_mul]
  apply congrArg W.topIso.hom
  have hx : e.inv.app ⊤ (e.hom.app ⊤ x) = x :=
    congrArg (fun g => g.app ⊤ x) e.hom_inv_id
  have hc := end_apply (e.inv ≫ f.hom) ⊤ (e.hom.app ⊤ x)
  change f.hom.app ⊤ (e.inv.app ⊤ (e.hom.app ⊤ x)) =
    (show Γ(W.toScheme,⊤) from e.hom.app ⊤ x) *
      (frameChange e f : Γ(W.toScheme,⊤)) at hc
  rw [hx, mul_comm] at hc
  exact hc

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateTransitions
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveLaurentTransitions
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateFiniteRingEquiv_ratio (i : σ) (a : Finset (ChartVariables i)) (j : σ) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (coordinateRatioOn (s i) (s j)
        (show coordinateFiniteOpen M s i a ≤ SectionOpens.isoOpen (s i) from inf_le_left)) =
      algebraMap _ _ (chartToPoly (R := K) i (chartCoordinate i j)) :=
  coordinateFiniteRingEquiv_coordinate M s k hc f hf i a j

lemma coordinateFiniteTransition_X (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (l : ChartVariables i) :
    coordinateFiniteTransition M s k hc f hf i j a b h
      (algebraMap _ _ (MvPolynomial.X (R := K) l)) =
      coordinateFiniteRingEquiv M s k hc f hf j b
        (coordinateRatioOn (s i) (s l.val) (h.trans inf_le_left)) := by
  change coordinateFiniteRingEquiv M s k hc f hf j b
    (X.presheaf.map (homOfLE h).op
      ((coordinateFiniteRingEquiv M s k hc f hf i a).symm _)) = _
  rw [coordinateFiniteRingEquiv_symm_X]
  change coordinateFiniteRingEquiv M s k hc f hf j b
    (X.presheaf.map (homOfLE h).op (coordinateRatioOn (s i) (s l.val) inf_le_left)) = _
  erw [coordinateRatioOn_restrict]

variable [Fintype σ]

lemma coordinateFiniteRingEquiv_ratio_full (i : σ) (a : Finset (ChartVariables i)) (j : σ) :
    overlapToFull i a (coordinateFiniteRingEquiv M s k hc f hf i a
      (coordinateRatioOn (s i) (s j)
        (show coordinateFiniteOpen M s i a ≤ SectionOpens.isoOpen (s i) from inf_le_left))) =
      AddMonoidAlgebra.single (standardExponent j 1 - standardExponent i 1) 1 := by
  classical
  rw [coordinateFiniteRingEquiv_ratio, chartToPoly_coordinate]
  by_cases hji : j = i
  · subst j
    simp only [dite_true, map_one, sub_self]
    rfl
  · rw [dite_eq_right hji, overlapToFull_X]

lemma coordinateFiniteTransition_X_full (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (l : ChartVariables i) :
    overlapToFull j b (coordinateFiniteTransition M s k hc f hf i j a b h
      (algebraMap _ _ (MvPolynomial.X (R := K) l))) =
      AddMonoidAlgebra.single (standardExponent l.val 1 - standardExponent i 1) 1 := by
  let r := coordinateFiniteRingEquiv M s k hc f hf j b
  let hi : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s i) := h.trans inf_le_left
  let hj : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s j) := inf_le_left
  have hinv : r (coordinateRatioOn (s j) (s i) hj) *
      r (coordinateRatioOn (s i) (s j) hi) = 1 := by
    rw [← map_mul, coordinateRatioOn_reciprocal, map_one]
  calc
    _ = overlapToFull j b
        (r (coordinateRatioOn (s j) (s l.val) hj) *
          r (coordinateRatioOn (s i) (s j) hi)) := by
      rw [coordinateFiniteTransition_X,
        coordinateRatioOn_change (s j) (s i) (s l.val) hj hi, map_mul, mul_comm]
    _ = _ := overlapToFull_ratio i j l.val b _ _ _
      (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b l.val)
      (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b i) hinv

lemma coordinateFiniteTransition_full (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a) :
    (overlapToFull j b).comp (coordinateFiniteTransition M s k hc f hf i j a b h) =
      overlapToFull i a := by
  apply overlapToFull_natural_of_generators
  · intro r
    rw [coordinateFiniteTransition_constant, overlapToFull_C]
  · intro l
    exact coordinateFiniteTransition_X_full M s k hc f hf i j a b h l

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveTupleCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveTupleCharts

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry

universe u
variable {σ : Type u} [Fintype σ]

open PiExponentSeshadri.ModuleFlasque
open PiExponent.ProjectiveMonomialCech
attribute [local instance] MvPolynomial.gradedAlgebra

theorem freeOpenHomCongr_restrict {X : Scheme} (M : X.Modules)
    {U U' V V' : X.Opens} (hU : U' = U) (hV : V' = V) (h : V ≤ U)
    (b : schemeFreeOpen X U ⟶ M) :
    freeOpenHomCongr M hV (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
      freeOpenMap X.ringCatSheaf (homOfLE (hV.le.trans (h.trans hU.ge))) ≫
        freeOpenHomCongr M hU b := by
  subst hU
  subst hV
  simp [freeOpenHomCongr, freeOpenMap]
  erw [Category.id_comp]

attribute [local irreducible] coordinatePowerOverlap modulePow

end
end PiExponent.GeometrySupport.ProjectiveTupleCharts

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateScalars
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ProjectiveChartSections
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque

abbrev schemeFreeOpen_p1 (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} (U : X.Opens) (M : X.Modules)
local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen :
    Module Γ(X,⊤) (schemeFreeOpen_p1 X U ⟶ M) :=
  sheafHomModule X _ M

lemma freeOpenAddEquiv_smul (r : Γ(X,⊤)) (b : schemeFreeOpen_p1 X U ⟶ M) :
    freeOpenAddEquiv U M (r • b) = restrictScalar X U r • freeOpenAddEquiv U M b := by
  rfl

end PiExponentSeshadri.ProjectiveChartSections

namespace PiExponentSeshadri.Projective
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (N : X.Modules)
local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen
    (U : X.Opens) : Module Γ(X,⊤) (schemeFreeOpen_p1 X U ⟶ N) :=
  sheafHomModule X _ N

end PiExponentSeshadri.Projective

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveEmbeddingCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

universe u

namespace Projective

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

instance projectiveBase_separated : IsSeparated (projectiveBase (K := K) (σ := σ)) := by
  unfold projectiveBase
  infer_instance

end Projective

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveFramedSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ ι : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
  (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
  (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
  (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)

theorem framedSectionsMorphism_preimage (j : σ) :
    framedSectionsMorphism k s U hc e a hnorm ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j) = SectionOpens.isoOpen (s j) := by
  ext x
  have hx : x ∈ ⨆ i, U i := by rw [hc]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have H : (U i).ι ⁻¹ᵁ (framedSectionsMorphism k s U hc e a hnorm ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j)) =
      (U i).ι ⁻¹ᵁ SectionOpens.isoOpen (s j) := by
    rw [← Scheme.Hom.comp_preimage, framedSectionsMorphism_local,
      coordinatesMap_preimage, preimage_isoOpen (s j) (U i).ι (e i)]
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : (U i).toScheme)

instance framedSectionsMorphism_proper
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (framedSectionsMorphism k s U hc e a hnorm) := by
  have : IsProper (framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase) := by
    rw [framedSectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

theorem framedSectionsMorphism_closed
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))]
    (hU : ∀ i, SectionOpens.isoOpen (s (a i)) = U i)
    (haff : ∀ i, IsAffine (U i).toScheme)
    (hgen : ∀ i, Function.Surjective
      (eval₂Hom ((U i).ι.appTop.hom.comp k)
        (fun j => coefficient (e i) (restrictSection (U i).ι (s j))))) :
    IsClosedImmersion (framedSectionsMorphism k s U hc e a hnorm) := by
  let V (i : ι) := Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X (a i))
  let k' (i : ι) := (U i).ι.appTop.hom.comp k
  let b (i : ι) (j : σ) := coefficient (e i) (restrictSection (U i).ι (s j))
  let g (i : ι) := (U i).toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom (k' i) (b i)) (MvPolynomial.X (a i))
      (by simpa only [eval₂Hom_X', b, hnorm] using (isUnit_one : IsUnit (1 : Γ((U i).toScheme, ⊤))))))
  let ep (i : ι) := Proj.basicOpenIsoSpec (homogeneousSubmodule σ K) (MvPolynomial.X (a i))
    (isHomogeneous_X K (a i)) (by decide : 0 < (1 : ℕ))
  apply PiExponentSeshadri.Geometry.closedImmersion_of_source_charts
    (framedSectionsMorphism k s U hc e a hnorm) U V hc (fun i => g i ≫ (ep i).inv)
  · intro i
    let : IsAffine (U i).toScheme := haff i
    have : IsClosedImmersion (g i) := normalized_coordinates_closed (k' i) (b i) (a i) (hnorm i) (hgen i)
    infer_instance
  · intro i
    rw [framedSectionsMorphism_local]
    rfl
  · intro i
    exact (framedSectionsMorphism_preimage k s U hc e a hnorm (a i)).trans (hU i)

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ ι κ : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem framedSectionsMorphism_eq (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
    (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)
    (V : κ → X.Opens) (hd : (⨆ i, V i) = ⊤)
    (d : ∀ i, M.restrict (V i).ι ≅ O (V i).toScheme) (b : κ → σ)
    (hnorm' : ∀ i, coefficient (d i) (restrictSection (V i).ι (s (b i))) = 1) :
    framedSectionsMorphism k s U hc e a hnorm =
      framedSectionsMorphism k s V hd d b hnorm' := by
  let W : ι ⊕ κ → X.Opens := Sum.elim U V
  have hw : (⨆ i, W i) = ⊤ := by
    apply top_unique
    rw [← hc]
    apply iSup_le
    intro i
    exact le_iSup W (Sum.inl i)
  let E : ∀ i, M.restrict (W i).ι ≅ O (W i).toScheme :=
    fun i => match i with | Sum.inl j => e j | Sum.inr j => d j
  let A : ι ⊕ κ → σ := Sum.elim a b
  have hN : ∀ i, coefficient (E i) (restrictSection (W i).ι (s (A i))) = 1 := by
    rintro (i | i)
    · exact hnorm i
    · exact hnorm' i
  let F := framedSectionsMorphism k s W hw E A hN
  have hleft : framedSectionsMorphism k s U hc e a hnorm = F := by
    apply (X.openCoverOfIsOpenCover U hc).hom_ext
    intro i
    change ι at i
    change (U i).ι ≫ _ = (U i).ι ≫ F
    rw [framedSectionsMorphism_local]
    exact (framedSectionsMorphism_local k s W hw E A hN (Sum.inl i)).symm
  have hright : framedSectionsMorphism k s V hd d b hnorm' = F := by
    apply (X.openCoverOfIsOpenCover V hd).hom_ext
    intro i
    change κ at i
    change (V i).ι ≫ _ = (V i).ι ≫ F
    rw [framedSectionsMorphism_local]
    exact (framedSectionsMorphism_local k s W hw E A hN (Sum.inr i)).symm
  exact hleft.trans hright.symm

lemma framedSectionsMorphism_eq_sectionsMorphism (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1) :
    framedSectionsMorphism k s U hc e a hnorm = sectionsMorphism k s hs :=
  framedSectionsMorphism_eq k s U hc e a hnorm
    (fun i => SectionOpens.isoOpen (s i)) hs (fun i => sectionFrame (s i)) id
    (fun i => sectionFrame_normalized (s i))

end

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}} {M N : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coefficient_postcomp (f : M ≅ N) (φ : X.Opens)
    (e : M.restrict φ.ι ≅ O φ.toScheme) (s : O X ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctor φ.ι).mapIso f.symm ≪≫ e)
      (restrictSection φ.ι (s ≫ f.hom)) = coefficient e (restrictSection φ.ι s) := by
  simp only [restrictSection]
  let F : X.Modules ⥤ φ.toScheme.Modules := Scheme.Modules.restrictFunctor φ.ι
  let a : O φ.toScheme ⟶ F.obj (O X) := (Scheme.Modules.restrictUnitIso φ.ι).inv
  let e' : F.obj M ≅ O φ.toScheme := e
  change endValue ((a ≫ F.map (s ≫ f.hom)) ≫ F.map f.inv ≫ e'.hom) =
    endValue ((a ≫ F.map s) ≫ e'.hom)
  have hs : (s ≫ f.hom) ≫ f.inv = s := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hm : F.map (s ≫ f.hom) ≫ F.map f.inv = F.map s :=
    (F.map_comp _ _).symm.trans (congrArg F.map hs)
  apply congrArg endValue
  calc
    _ = a ≫ ((F.map (s ≫ f.hom) ≫ F.map f.inv) ≫ e'.hom) := by
      simp only [Category.assoc]
    _ = a ≫ (F.map s ≫ e'.hom) := congrArg (fun t => a ≫ t ≫ e'.hom) hm
    _ = _ := (Category.assoc _ _ _).symm

theorem sectionsMorphism_transport (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (f : M ≅ N) (ht : (⨆ i, SectionOpens.isoOpen (s i ≫ f.hom)) = ⊤) :
    sectionsMorphism k (fun i => s i ≫ f.hom) ht = sectionsMorphism k s hs := by
  let U (i : σ) := SectionOpens.isoOpen (s i)
  let e (i : σ) := (Scheme.Modules.restrictFunctor (U i).ι).mapIso f.symm ≪≫ sectionFrame (s i)
  have he (i j : σ) : coefficient (e i) (restrictSection (U i).ι (s j ≫ f.hom)) =
      coefficient (sectionFrame (s i)) (restrictSection (U i).ι (s j)) :=
    coefficient_postcomp f (U i) (sectionFrame (s i)) (s j)
  have hn (i : σ) : coefficient (e i) (restrictSection (U i).ι (s i ≫ f.hom)) = 1 := by
    rw [he]
    exact sectionFrame_normalized (s i)
  rw [← framedSectionsMorphism_eq_sectionsMorphism k (fun i => s i ≫ f.hom) ht U hs e id hn]
  apply (X.openCoverOfIsOpenCover U hs).hom_ext
  intro i
  change σ at i
  change (U i).ι ≫ _ = (U i).ι ≫ _
  rw [framedSectionsMorphism_local, sectionsMorphism_local]
  congr 1
  funext j
  exact he i j

end PiExponentSeshadri.Projective

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveNegativeTransitions
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveLaurentTransitions
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateFiniteRingEquiv_cross_ratio_full (i j : σ)
    (b : Finset (ChartVariables j))
    (hi : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s i)) (l : σ) :
    overlapToFull j b (coordinateFiniteRingEquiv M s k hc f hf j b
      (coordinateRatioOn (s i) (s l) hi)) =
      AddMonoidAlgebra.single (standardExponent l 1 - standardExponent i 1) 1 := by
  let r := coordinateFiniteRingEquiv M s k hc f hf j b
  let hj : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s j) := inf_le_left
  have hinv : r (coordinateRatioOn (s j) (s i) hj) *
      r (coordinateRatioOn (s i) (s j) hi) = 1 := by
    rw [← map_mul, coordinateRatioOn_reciprocal, map_one]
  calc
    _ = overlapToFull j b
        (r (coordinateRatioOn (s j) (s l) hj) * r (coordinateRatioOn (s i) (s j) hi)) := by
      rw [coordinateRatioOn_change (s j) (s i) (s l) hj hi, map_mul, mul_comm]
    _ = _ := overlapToFull_ratio i j l b _ _ _
      (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b l)
      (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b i) hinv

lemma coordinateNegativeFrameFactor_full (n : ℕ) (i j : σ)
    (b : Finset (ChartVariables j))
    (hi : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s i)) :
    overlapToFull j b
      ((coordinateFiniteRingEquiv M s k hc f hf j b
        (coordinateRatioOn (s i) (s j) hi)) ^ n) =
      AddMonoidAlgebra.single
        (standardExponent i (-(n : ℤ)) - standardExponent j (-(n : ℤ))) 1 := by
  classical
  rw [map_pow, coordinateFiniteRingEquiv_cross_ratio_full,
    AddMonoidAlgebra.single_pow, one_pow]
  congr 1
  funext a
  simp only [Pi.smul_apply, Pi.sub_apply, standardExponent]
  split_ifs <;> simp

lemma coordinateNegativeLaurent_change (n : ℕ) (i j : σ)
    (a : Finset (ChartVariables i)) (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (z : Localization.Away (chartProduct (R := K) i a)) :
    overlapLaurent j (-(n : ℤ)) b
      ((coordinateFiniteRingEquiv M s k hc f hf j b
        (coordinateRatioOn (s i) (s j) (h.trans inf_le_left))) ^ n *
        coordinateFiniteTransition M s k hc f hf i j a b h z) =
      overlapLaurent i (-(n : ℤ)) a z :=
  overlapLaurent_change_pivot i j (-(n : ℤ)) a b
    (coordinateFiniteTransition M s k hc f hf i j a b h)
    (coordinateFiniteTransition_full M s k hc f hf i j a b h) _
    (coordinateNegativeFrameFactor_full M s k hc f hf n i j b (h.trans inf_le_left)) z

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveNegativeScalars
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque
attribute [local instance] MvPolynomial.gradedAlgebra
abbrev schemeFreeOpen_p3 (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (n : ℕ) (N : X.Modules) (E : moduleTensor X (modulePow X M n) N ≅ O X)
local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen_1
    (U : X.Opens) (P : X.Modules) :
    Module Γ(X,⊤) (schemeFreeOpen_p3 X U ⟶ P) := sheafHomModule X _ P

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_CompositePullbackCoefficient
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.CompositePullbackCoefficient


theorem exists_frame {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (e : (Scheme.Modules.pullback (f ≫ g)).obj M ≅ O X) :
    ∃ e' : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅ O X,
      ∀ s : O Z ⟶ M,
      coefficient e' (pullbackSection f (pullbackSection g s)) =
        coefficient e (pullbackSection (f ≫ g) s) := by
  let F := Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f
  let G := Scheme.Modules.pullback (f ≫ g)
  let uF : F.obj (O Z) ≅ O X :=
    (Scheme.Modules.pullback f).mapIso (pullbackUnitIso g) ≪≫ pullbackUnitIso f
  obtain ⟨e', he'⟩ := PullbackFrameCoefficient.exists_frame_natIso_all
    F G (Scheme.Modules.pullbackComp f g) uF (pullbackUnitIso (f ≫ g)) e
  refine ⟨e', fun s => ?_⟩
  simpa only [F, G, uF, pullbackSection, Iso.trans_inv, Functor.mapIso_inv,
    Functor.comp_map, Functor.map_comp, Category.assoc] using he' s

end PiExponent.CompositePullbackCoefficient

end

end OAI
end


