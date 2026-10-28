-- Prove2me | Definitions.Def_OAIQ068A025
-- name    : OAIQ068A025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:59:16.113828+00:00
-- url     : https://prove2.me/theorems/e9ebc76e-ac9b-4dae-9731-dc32391dfa1f
-- title:
--   Definitions bundle OAIQ068A025 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 93 declarations of OpenAI's Lean: 57 definitions, 2 instances and 34 theorems. The definitions and types are `OAI.PiExponent.CartierPowerFrames.sectionMultiplyLeft`, `OAI.PiExponent.CartierPowerFrames.tensorFrame`, `OAI.PiExponent.CartierPowerFrames.tensorUnitTwist`, `OAI.PiExponent.ConstantPullbackDegree.constantPullbackIso`, `OAI.PiExponent.ConstantPullbackDegree.pullbackFrame_of_range_subset`, `OAI.PiExponent.DeterminantContradiction.AnalyticAggregateStatement`, `OAI.PiExponent.DeterminantContradiction.Column`, `OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement`, `OAI.PiExponent.DeterminantContradiction.Row`, `OAI.PiExponent.DeterminantContradiction.actualMatrix`, `OAI.PiExponent.DeterminantContradiction.actualMean`, `OAI.PiExponent.DeterminantContradiction.actualMinor`, `OAI.PiExponent.DeterminantContradiction.actualRowCount`, `OAI.PiExponent.DeterminantContradiction.collisionLimit`, `OAI.PiExponent.DeterminantContradiction.collisionRate`, `OAI.PiExponent.DeterminantContradiction.finiteDenominators`, `OAI.PiExponent.DeterminantContradiction.finiteNumerators`, `OAI.PiExponent.DeterminantContradiction.lowIndexCount`, `OAI.PiExponent.FiniteTupleCech.assemble`, `OAI.PiExponent.FiniteTupleCech.evaluate`, `OAI.PiExponent.GeometrySupport.IdealPullbackMap.comap`, `OAI.PiExponent.GeometrySupport.IdealPullbackMap.map`, `OAI.PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra.chartExponent`, `OAI.PiExponent.GradedCech.evaluate`, `OAI.PiExponent.GradedFreeCech.coordinateCochain`, `OAI.PiExponent.GradedFreeCech.coordinateIntersection`, `OAI.PiExponent.GradedH0.NonnegativeMonomialSet`, `OAI.PiExponent.GradedH0.decode`, `OAI.PiExponent.GradedH0.encode`, `OAI.PiExponent.GradedH0.exponentEquiv`, `OAI.PiExponent.GradedH0.homogeneousPolynomialEquiv`, `OAI.PiExponent.GradedH0.polynomialLaurent`, `OAI.PiExponent.GradedPolynomialCech.cochainToLaurent`, `OAI.PiExponent.GradedPolynomialCech.intersectionToLaurent`, `OAI.PiExponent.GradedPolynomialCech.intersectionToPiece`, `OAI.PiExponent.GradedPolynomialLaurent.pieceToLaurent`, `OAI.PiExponent.GradedSerreStep.HasPrimitive`, `OAI.PiExponent.GradedSerreStep.HasRecovery`, `OAI.PiExponent.IdealSectionRestriction.idealCongr`, `OAI.PiExponent.IdealSectionRestriction.pullback` and 17 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_ExceptionalAffineChart`, `PiExponent_Ampleness_ExceptionalCurveDegree`, `PiExponent_Ampleness_ExceptionalPowerSections`, `PiExponent_Analysis_AnalyticAggregate`, `PiExponent_Analysis_LiteralAnalyticSummand`, `PiExponent_Analysis_LogarithmicContactIdeal`, `PiExponent_Approximation_CoherentCokernels`, `PiExponent_Approximation_CoherentTwistPresentation`, `PiExponent_Approximation_ConstantPullbackDegree`, `PiExponent_Approximation_DeterminantContradiction`, `PiExponent_Approximation_TensorPowerRestriction`, `PiExponent_Cohomology_GradedCech`, `PiExponent_Cohomology_GradedCechBound`, `PiExponent_Cohomology_GradedFreeCech`, `PiExponent_Cohomology_GradedH0`, `PiExponent_Cohomology_GradedPolynomialCech`, `PiExponent_Cohomology_GradedPolynomialLaurent`, `PiExponent_Geometry_AdmissibleCurveInequality`, `PiExponent_Geometry_CartierPowerFrames`, `PiExponent_Geometry_IdealSheafPowers`, `PiExponent_Geometry_PlaceValuationRing`, `PiExponent_Geometry_ProjectiveCoordinateChartMap`, `PiExponent_Geometry_ProjectiveCoordinatePullback`, `PiExponent_Geometry_ProjectiveGlobalPolynomialAlgebra`, `PiExponent_Jets_BranchContact`, `PiExponent_Jets_FormalBranchContact`, `PiExponent_LocalAlgebra_FiniteGlobalPresentation`, `PiExponent_LocalAlgebra_IdealModuleRestriction`, `PiExponent_LocalAlgebra_IdealPullbackMap`, `PiExponent_LocalAlgebra_IdealSectionRestriction`, `PiExponent_LocalAlgebra_IdealTensorPowers`, `PiExponent_Polynomials_GradedSerreStep`.
--
--   **Imports.** It imports the bundles `OAIQ068A012`, `OAIQ068A013`, `OAIQ068A014`, `OAIQ068A015`, `OAIQ068A016` and `OAIQ068A017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A031`, `OAIQ068A032`, `OAIQ068A033` and `OAIQ068A034`; the statements `OAI_PiExponent_GradedSerreStep_exists_syzygy_eventual_step`, `OAI.PiExponent.GradedSerreStep.exists_syzygy_eventual_step_q68`, `OAI_PiExponent_LiteralAnalytic_analyticAggregate`, `OAI.PiExponent.LiteralAnalytic.analyticAggregate_q68`, `OAI_PiExponent_LiteralAnalytic_norm_actual_summand_le`, `OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le_q68`, `OAI_PiExponent_piEventualLowerBound_of_globalInterpolation` and `OAI.PiExponent.piEventualLowerBound_of_globalInterpolation_q68`; the proofs of `OAI_PiExponent_GradedSerreStep_exists_syzygy_eventual_step`, `OAI.PiExponent.GradedSerreStep.exists_syzygy_eventual_step_q68`, `OAI_PiExponent_LiteralAnalytic_analyticAggregate`, `OAI.PiExponent.LiteralAnalytic.analyticAggregate_q68`, `OAI_PiExponent_LiteralAnalytic_norm_actual_summand_le`, `OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le_q68`, `OAI_PiExponent_piEventualLowerBound_of_globalInterpolation` and `OAI.PiExponent.piEventualLowerBound_of_globalInterpolation_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A012
import Definitions.Def_OAIQ068A013
import Definitions.Def_OAIQ068A014
import Definitions.Def_OAIQ068A015
import Definitions.Def_OAIQ068A016
import Definitions.Def_OAIQ068A017

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoherentTwistPresentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace PiExponentSeshadri.Geometry
open MonoidalCategory
variable {X : Scheme}

theorem moduleTwistFunctor_add (L : LineBundle X) (m n : ℕ) :
    moduleTwistFunctor L (m+n) = moduleTwistFunctor L m ⋙ moduleTwistFunctor L n := by
  induction n with
  | zero =>
    change moduleTwistFunctor L m = moduleTwistFunctor L m ⋙ 𝟭 _
    rfl
  | succ n ih =>
    change moduleTwistFunctor L (m+n) ⋙ moduleTensorRightFunctor L.sheaf =
      moduleTwistFunctor L m ⋙ (moduleTwistFunctor L n ⋙ moduleTensorRightFunctor L.sheaf)
    rw [ih]
    rfl

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TensorPowerRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma sectionOpen_le_powerSection {M : X.Modules} (s : structureSheaf X ⟶ M) (n : ℕ) :
    sectionOpen X s ≤ sectionOpen X (powerSection s n) := by
  refine iSup_le fun U => iSup_le fun hU => ?_
  let := hU
  exact le_iSup_of_le U (le_iSup_of_le (powerSection_restrict_isIso U s n) le_rfl)

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealTensorPowers
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

def affineMapCoefficient {M N : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme) (a : M ⟶ N) : Γ(X,U.1) :=
  U.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map a ≫ f.hom))

lemma affineMapCoefficient_comp {M N P : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme)
    (g : P.restrict U.1.ι ≅ O U.1.toScheme) (a : M ⟶ N) (b : N ⟶ P) :
    affineMapCoefficient U e g (a ≫ b) =
      affineMapCoefficient U e f a * affineMapCoefficient U f g b := by
  unfold affineMapCoefficient
  rw [← map_mul,← endValue_comp]
  simp only [Functor.map_comp,Category.assoc,Iso.hom_inv_id_assoc]

lemma affineMapCoefficient_id {M : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme) :
    affineMapCoefficient U e e (𝟙 M) = 1 := by
  simp only [affineMapCoefficient]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, endValue_id, map_one]

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalPowerSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
namespace PiExponentSeshadri.Geometry
variable {X Y : Scheme}

theorem framed_section_range {Z : Scheme} {M : Z.Modules}
    (e : M ≅ O Z) (a : M ⟶ O Z) :
    (a.val.app (.op ⊤)).hom.range =
      Ideal.span {endValue (e.inv ≫ a)} := by
  rw [show endValue (e.inv ≫ a) =
    UnitEndomorphism.equation (e.inv ≫ a) ⊤ from rfl,
    ← UnitEndomorphism.image_principal]
  ext r
  change (∃ s, a.val.app (.op ⊤) s = r) ↔
    ∃ s, a.val.app (.op ⊤) (e.inv.val.app (.op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (.op ⊤) s, ?_⟩
    have h : e.inv.val.app (.op ⊤) (e.hom.val.app (.op ⊤) s) = s := by
      exact congrArg (fun k : M ⟶ M => k.val.app (.op ⊤) s) e.hom_inv_id
    rw [h]
    exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (.op ⊤) s, hs⟩

end PiExponentSeshadri.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_IdealSheafPowers
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme}

lemma comap_pow (I : X.IdealSheafData) (f : Y ⟶ X) (m : ℕ) :
    (I^m).comap f = (I.comap f)^m := by
  have hc : ∀ y : Y, ∃ (U : Y.affineOpens) (V : X.affineOpens),
      y ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V.1 := by
    intro y
    obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show f y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ V from hyV)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hyU, hUV⟩
  choose U V hy hUV using hc
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    rw [comap_ideal (I^m) f (U y) (V y) (hUV y)]
    change (I.ideal (V y)^m).map _ = ((I.comap f).ideal (U y))^m
    rw [Ideal.map_pow, comap_ideal I f (U y) (V y) (hUV y)]

end
end PiExponentSeshadri.IdealPullback

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalAffineChart
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
namespace PiExponent.ExceptionalAffineChart
open PiExponentSeshadri.IdealPullback
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}
variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))

theorem chartPowerIdeal_eq (n : ℕ) :
    chartPowerIdeal I f j n =
      ((((specIdeal I).comap f)^n).comap (chartOpen j).1.ι).ideal
        ⟨⊤, isAffineOpen_top _⟩ := by
  change powerChartIdeal f (specIdeal I) n (chartOpen j)
    ⟨⊤, isAffineOpen_top _⟩ _ = _
  simp only [powerChartIdeal]
  have hlocal := PiExponentSeshadri.IdealPullback.comap_ideal ((specIdeal I)^n)
    f (chartOpen j) ⟨⊤, isAffineOpen_top _⟩ (by simp)
  have hpow := congrArg (fun K : Y.IdealSheafData => K.ideal (chartOpen j))
    (PiExponentSeshadri.IdealPullback.comap_pow (specIdeal I) f n)
  exact (congrArg (Ideal.map (chartOpen j).1.topIso.inv.hom)
    (hlocal.symm.trans hpow)).trans
      (PiExponentSeshadri.IdealPullback.comap_ι_top
        (((specIdeal I).comap f)^n) (chartOpen j)).symm

include hf in

theorem map_chartPowerIdeal (n : ℕ) :
    (chartPowerIdeal I f j n).map (chartFunctionsEquiv j).toRingHom =
      (I^n).map (φ) := by
  let : IsAffine j.opensRange.toScheme := isAffineOpen_opensRange j
  have hlocal : ((((specIdeal I).comap f)^n).comap j).ideal
      ⟨⊤, isAffineOpen_top _⟩ =
      ((I^n).map (φ)).map
        (Scheme.ΓSpecIso (CommRingCat.of (A))).inv.hom := by
    rw [← PiExponentSeshadri.IdealPullback.comap_pow,
      ← PiExponentSeshadri.IdealPullback.specIdeal_pow,
      ← Scheme.IdealSheafData.comap_comp, hf,
      specIdeal_comap, specIdeal_top]
  have hmap : (chartPowerIdeal I f j n).map
      (j.isoOpensRange.hom.appTop.hom) =
      ((((specIdeal I).comap f)^n).comap j).ideal
        ⟨⊤, isAffineOpen_top _⟩ := by
    erw [chartPowerIdeal_eq, ← PiExponentSeshadri.IdealPullback.comap_top,
      ← Scheme.IdealSheafData.comap_comp]
    change (((specIdeal I).comap f ^ n).comap (j.isoOpensRange.hom ≫ j.opensRange.ι)).ideal _ = _
    rw [j.isoOpensRange_hom_ι]
  change (chartPowerIdeal I f j n).map
    ((Scheme.ΓSpecIso (CommRingCat.of (A))).hom.hom.comp
      (j.isoOpensRange.hom.appTop.hom)) = _
  erw [← Ideal.map_map, hmap, hlocal, Ideal.map_map]
  have hi : (Scheme.ΓSpecIso (CommRingCat.of (A))).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (A))).inv.hom = RingHom.id _ := by
    apply RingHom.ext
    intro r
    exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply r
  rw [hi, Ideal.map_id]

end PiExponent.ExceptionalAffineChart
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_BranchContact
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BranchContact

variable {ι : Type*} [Fintype ι]

theorem contact_add_high_tail (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a t : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ht : ∀ i (k : ℕ), (t i).order = (k : ℕ∞) → contact v a hne * v i < (k : ℚ)) :
    contact v (fun i => a i + t i) (add_not_all_zero v hv a t hne ht) = contact v a hne := by
  apply le_antisymm
  · obtain ⟨i,hi,horder,he⟩ := exists_attaining_add v hv a t hne ht
    exact (contact_le v _ _ i hi).trans_eq he.symm
  · apply le_contact v hv _ _
    intro i k hk
    exact order_add_lower _ (a i) (t i) (contact_bound v hv a hne i)
      (fun n hn => (ht i n hn).le) k hk

end PiExponent.BranchContact

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceValuationRing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.PlaceValuationRing

open CurveValuationCenter WeightedCurveDegree

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

instance scalarTower (p : NormalizedPlace F E) : IsScalarTower F (ring p) E :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

end PiExponent.PlaceValuationRing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_AdmissibleCurveInequality
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.AdmissibleParameters

variable {nu Lambda C : ℝ} (d : AdmissibleParameters nu Lambda C)

theorem curveCenters_injective (i : Fin d.m) :
    Function.Injective (fun j => d.curveCenters j i) := by
  have hp : (d.p i.val : ℂ) ≠ 0 := by exact_mod_cast (d.approximations i.val).2.1
  have hq : (d.q i.val : ℂ) ≠ 0 := by
    exact_mod_cast (show d.q i.val ≠ 0 by have := (d.approximations i.val).1; omega)
  have hr : MatrixArithmetic.rationalCenters (fun i : Fin d.m => d.p i.val)
      (fun i : Fin d.m => d.q i.val) i ≠ 0 := by
    unfold MatrixArithmetic.rationalCenters
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
  intro j l h
  dsimp only [curveCenters] at h
  have he := (mul_right_cancel₀ hr h : (j.val : ℂ) = (l.val : ℂ))
  apply Fin.ext
  exact_mod_cast he

end PiExponent.AdmissibleParameters
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FiniteGlobalPresentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FiniteGlobalPresentation
noncomputable section
universe u v₁ v₂ u₁ u₂
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponent.CoherentAffineFinite

theorem kernel_generators_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (s : M.GeneratingSections) [hs : s.IsFiniteType] :
    (kernel s.π).IsFinitePresentation := by
  let : Finite s.I := hs.finite
  have := free_isFinitePresentation X s.I
  exact kernel_isFinitePresentation s.π

end
end PiExponent.FiniteGlobalPresentation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalBranchContact
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchContact

open FormalBranchEvaluation

theorem contact_truncatedBranchCoordinates_eq {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (hne : ∃ i, branchCoordinates c y x i ≠ 0)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    BranchContact.contact v (truncatedBranchCoordinates c y x T)
      (truncatedBranchCoordinates_not_all_zero v hv c y x hy hx hne T hT) =
        BranchContact.contact v (branchCoordinates c y x) hne := by
  have hh := BranchContact.contact_add_high_tail v hv
    (branchCoordinates c y x) (composedLogTails (branchCoordinates c y x) T) hne
    (composedLogTails_strict_contact v hv _ hne
      (branchCoordinates_constantCoeff c y x hy hx) T hT)
  simpa only [← truncatedBranchCoordinates_eq_add_tail c y x T hy] using hh

end PiExponent.FormalBranchContact

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_LogarithmicContactIdeal
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.LogarithmicContactIdeal

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem truncatedCoordinates_nonzero {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    ∃ i, truncatedCoordinates c y x T i ≠ 0 := by
  have hn := FormalBranchContact.truncatedBranchCoordinates_not_all_zero v hv c
    (DVRBranch.expansion ℂ A y) (fun i => DVRBranch.expansion ℂ A (x i))
    (by simpa using hy) (fun i => by simpa using hx i)
    (DVRBranchJet.coordinates_nonzero c y x hnc) T hT
  rw [← expansion_truncatedCoordinates c y x T hy] at hn
  obtain ⟨i, hi⟩ := hn
  refine ⟨i, ?_⟩
  intro hz
  apply hi
  change DVRBranch.expansion ℂ A (truncatedCoordinates c y x T i) = 0
  rw [hz, map_zero]

theorem truncated_contact_eq {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    BranchContactIdeal.contact v (truncatedCoordinates c y x T)
      (truncatedCoordinates_nonzero v hv c y x hy hx hnc T hT) =
        DVRBranchJet.contact v c y x hnc := by
  unfold BranchContactIdeal.contact DVRBranchJet.contact
  trans BranchContact.contact v
    (FormalBranchContact.truncatedBranchCoordinates c (DVRBranch.expansion ℂ A y)
      (fun i => DVRBranch.expansion ℂ A (x i)) T)
    (FormalBranchContact.truncatedBranchCoordinates_not_all_zero v hv c
      (DVRBranch.expansion ℂ A y) (fun i => DVRBranch.expansion ℂ A (x i))
      (by simpa using hy) (fun i => by simpa using hx i)
      (DVRBranchJet.coordinates_nonzero c y x hnc) T hT)
  · apply branchContact_congr
    exact expansion_truncatedCoordinates c y x T hy
  · exact FormalBranchContact.contact_truncatedBranchCoordinates_eq v hv c
      (DVRBranch.expansion ℂ A y) (fun i => DVRBranch.expansion ℂ A (x i))
      (by simpa using hy) (fun i => by simpa using hx i)
      (DVRBranchJet.coordinates_nonzero c y x hnc) T hT

theorem logarithmicIdeal_colength_eq_contact {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length A (A ⧸ logarithmicIdeal c y x T e)).toNat : ℚ) =
      R * DVRBranchJet.contact v c y x hnc := by
  change ((Module.length A (A ⧸ BranchContactIdeal.powerIdeal
    (truncatedCoordinates c y x T) e)).toNat : ℚ) = _
  rw [BranchContactIdeal.colength_eq_contact v hv _
    (truncatedCoordinates_nonzero v hv c y x hy hx hnc T hT) R e he,
    truncated_contact_eq v hv c y x hy hx hnc T hT]

end PiExponent.LogarithmicContactIdeal

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CartierPowerFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CartierPowerFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}
def sectionMultiplyLeft (L M : X.Modules) (s : structureSheaf X ⟶ L) :
    M ⟶ moduleTensor X L M :=
  (moduleTensorUnit M).inv ≫ moduleTensorMap s (𝟙 M)

def tensorFrame (L M : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    (moduleTensor X L M).restrict U.ι ≅ O U.toScheme :=
  moduleTensorRestrict U L M ≪≫ moduleTensorIso e f ≪≫
    moduleTensorUnit (O U.toScheme)

def tensorUnitTwist (M : X.Modules) (U : X.Opens)
    (f : M.restrict U.ι ≅ O U.toScheme) : O U.toScheme ≅ O U.toScheme :=
  f.symm ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTensorUnit M).symm ≪≫
    moduleTensorRestrict U (O X) M ≪≫
      moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f ≪≫ moduleTensorUnit (O U.toScheme)

lemma tensor_multiply_framed (L M : X.Modules) (s : O X ⟶ L) (U : X.Opens)
    (e : L.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    f.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (sectionMultiplyLeft L M s) ≫
      (tensorFrame L M U e f).hom = (tensorUnitTwist M U f).hom ≫
        (restrictSection U.ι s ≫ e.hom) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U (O X) M
  let R' := moduleTensorRestrict U L M
  let E := moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f
  let E' := moduleTensorIso e f
  let T := moduleTensorUnit (O U.toScheme)
  let a : O U.toScheme ⟶ O U.toScheme := restrictSection U.ι s ≫ e.hom
  let p := moduleTensorMap (F.map s) (𝟙 (M.restrict U.ι))
  have hn : F.map (moduleTensorMap s (𝟙 M)) ≫ R'.hom = R.hom ≫ p :=
    (moduleTensorRestrict_natural U s (𝟙 M)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map s) q) (F.map_id M))
  have he : F.map s ≫ e.hom = (Scheme.Modules.restrictUnitIso U.ι).hom ≫ a := by
    simpa only [a, restrictSection] using!
      frame_section (Scheme.Modules.restrictUnitIso U.ι) (F.map s) e
  have h₁ := (moduleTensorMap_comp (F.map s) e.hom (𝟙 (M.restrict U.ι)) f.hom).symm.trans
    (congrArg (moduleTensorMap (F.map s ≫ e.hom)) (Category.id_comp f.hom))
  have h₂ := (moduleTensorMap_comp (Scheme.Modules.restrictUnitIso U.ι).hom a
      f.hom (𝟙 (O U.toScheme))).symm.trans
    (congrArg (moduleTensorMap ((Scheme.Modules.restrictUnitIso U.ι).hom ≫ a))
      (Category.comp_id f.hom))
  have ht : p ≫ E'.hom = E.hom ≫ moduleTensorMap a (𝟙 (O U.toScheme)) :=
    h₁.trans ((congrArg (fun q : F.obj (O X) ⟶ O U.toScheme => moduleTensorMap q f.hom)
      he).trans h₂.symm)
  have hs : moduleTensorMap a (𝟙 (O U.toScheme)) ≫ T.hom = T.hom ≫ a :=
    (moduleTensorUnit_scalar (X := U.toScheme) a (𝟙 (O U.toScheme))).trans
      (congrArg (fun q => T.hom ≫ q) (Category.comp_id a))
  have hfinal := framed_multiply f.inv (F.map (moduleTensorUnit M).inv)
    (F.map (moduleTensorMap s (𝟙 M))) R.hom R'.hom E.hom E'.hom T.hom a p _ hn ht hs
  simpa only [sectionMultiplyLeft, tensorFrame, tensorUnitTwist] using!
    (congrArg (fun q => f.inv ≫ q ≫ (tensorFrame L M U e f).hom)
      (F.map_comp (moduleTensorUnit M).inv (moduleTensorMap s (𝟙 M)))).trans hfinal

lemma tensor_multiply_ideal (L M : X.Modules) (s : O X ⟶ L)
    (U : X.affineOpens) (e : L.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue (f.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (sectionMultiplyLeft L M s) ≫
        (tensorFrame L M U.1 e f).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} := by
  rw [tensor_multiply_framed,endValue_comp,map_mul,← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue (tensorUnitTwist M U.1 f).hom) :=
    (end_isIso_iff _).mp inferInstance
  rw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom),Ideal.top_mul]
  rfl

end
end PiExponent.CartierPowerFrames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateChartMap
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable {M : X.Modules} (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)

def coordinateChartMap (i : σ) : (SectionOpens.isoOpen (s i)).toScheme ⟶
    (PiExponent.ProjectiveO1.coordinateOpen (R := K) i).toScheme :=
  (X.isoOfEq (sectionsMorphism_preimage k s hc i).symm).hom ≫
    (sectionsMorphism k s hc ∣_ PiExponent.ProjectiveO1.coordinateOpen i)

lemma coordinateChartMap_factor (i : σ) :
    coordinateChartMap k s hc i ≫ (PiExponent.ProjectiveO1.coordinateOpen (R := K) i).ι =
      (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hc := by
  simp only [coordinateChartMap, Category.assoc, morphismRestrict_ι,
    Scheme.isoOfEq_hom_ι_assoc]

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinatePullback
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable {M : X.Modules} (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)

def coordinatePullbackModule : X.Modules :=
  (Scheme.Modules.pullback (sectionsMorphism k s hc)).obj
    (PiExponent.ProjectiveO1.lineBundle (R := K) (σ := σ)).sheaf

def coordinatePullbackSection (i : σ) : O X ⟶ coordinatePullbackModule k s hc :=
  pullbackSection (sectionsMorphism k s hc) (PiExponent.ProjectiveO1.coordinateSection i)

attribute [local irreducible] coordinatePullbackModule coordinatePullbackSection

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ConstantPullbackDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ConstantPullbackDegree
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

def pullbackFrame_of_range_subset (K : LineBundle Y) (g : X ⟶ Y)
    (U : Y.Opens) (h : Set.range g ⊆ (U : Set Y))
    (e : K.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    (K.pullback g).sheaf ≅ structureSheaf X := by
  have hr : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact h
  let l := IsOpenImmersion.lift U.ι g hr
  have hl : l ≫ U.ι = g := IsOpenImmersion.lift_fac U.ι g hr
  exact (Scheme.Modules.pullbackCongr hl.symm).app K.sheaf ≪≫
    ((Scheme.Modules.pullbackComp l U.ι).app K.sheaf).symm ≪≫
      (Scheme.Modules.pullback l).mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app
        K.sheaf).symm ≪≫ (Scheme.Modules.pullback l).mapIso e ≪≫ pullbackUnitIso l

def constantPullbackIso (K : LineBundle Y) (g : X ⟶ Y) (y : Y)
    (hg : Set.range g ⊆ ({y} : Set Y)) :
    (K.pullback g).sheaf ≅ structureSheaf X := by
  apply Classical.choice
  obtain ⟨U, hy, ⟨e⟩⟩ := K.locallyRankOne y
  refine ⟨pullbackFrame_of_range_subset K g U ?_ e⟩
  intro z hz
  have hz' : z = y := hg hz
  exact hz'.symm ▸ hy

end
end PiExponent.ConstantPullbackDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoherentCokernels
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CoherentCokernels
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponent.FiniteGlobalPresentation PiExponent.CoherentAffineFinite
universe u

theorem affine_cokernel_exists_finitePresentation {X : Scheme.{u}}
    [IsAffine X] [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (hN : LocallyFinitelyGenerated N) :
    ∃ P : (cokernel f).Presentation, P.IsFinite := by
  let a := X.isoSpec.inv
  let F := Scheme.Modules.restrictFunctor a
  have : IsNoetherianRing Γ(X,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj (N.restrict a)).obj.obj (op ⊤)) :=
    spec_sections_finite_of_localGenerators (N.restrict a) (hN.restrict a)
  obtain ⟨P,hP⟩ := spec_cokernel_exists_finitePresentation (F.map f)
  let e := PreservesCokernel.iso F f
  let P' := presentationOfIso (Spec Γ(X,⊤)) e.symm P
  let b := X.isoSpec.hom
  let G : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor b
  let : PreservesColimitsOfSize.{u,u} G :=
    (Scheme.Modules.restrictAdjunction b).leftAdjoint_preservesColimits
  let Q := P'.map G (Scheme.Modules.restrictUnitIso b).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp b a).app (cokernel f)
  have e₂ : (cokernel f).restrict (𝟙 X) ≅ ((cokernel f).restrict a).restrict b := by
    change (cokernel f).restrict (b ≫ a) ≅ ((cokernel f).restrict a).restrict b at e₁
    simpa only [b, a, Iso.hom_inv_id] using e₁
  let e₃ := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app (cokernel f)
  exact ⟨presentationOfIso X e₃ Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem cokernel_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsFinitePresentation] (f : M ⟶ N) :
    (cokernel f).IsFinitePresentation := by
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  let F := Scheme.Modules.restrictFunctor U.1.ι
  let : N.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData N).choose.isQuasicoherent
  obtain ⟨P,hP⟩ := affine_cokernel_exists_finitePresentation (F.map f)
    ((locallyFinitelyGenerated_of_finitePresentation N).restrict U.1.ι)
  let e := PreservesCokernel.iso F f
  exact ⟨presentationOfIso U.1.toScheme e.symm P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩
end
end PiExponent.CoherentCokernels

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalCurveDegree
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalCurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

section Curve
open CurveNormalizationModel CurveValuationCenter CurvePlaceCenter
open LocalSectionOrder
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem map_powerIdeal_eq_top_of_transcendental {m : ℕ}
    (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i))
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) :
    (CompactJetPolynomial.powerIdeal c (CompactJetPolynomial.logPolynomials T) e).map
      (MvPolynomial.aeval z).toRingHom = ⊤ := by
  classical
  have hn : ∃ i, MvPolynomial.aeval z
      (CompactJetPolynomial.coordinates c (CompactJetPolynomial.logPolynomials T) i) ≠ 0 := by
    by_contra h
    push Not at h
    have hle : Ideal.span (Set.range
        (CompactJetPolynomial.coordinates c (CompactJetPolynomial.logPolynomials T))) ≤
        RingHom.ker (MvPolynomial.aeval z).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact h i
    rw [CompactJetPolynomial.span_coordinates c _
      (CompactJetPolynomial.logPolynomials_eval_zero T)] at hle
    obtain ⟨i, hi⟩ := hz
    have hc : MvPolynomial.X i - MvPolynomial.C (CompactJetPolynomial.center c i) ∈
        WeightedBezout.pointIdeal (CompactJetPolynomial.center c) := by
      change MvPolynomial.aeval (CompactJetPolynomial.center c) _ = 0
      simp
    have he := hle hc
    change MvPolynomial.aeval z _ = 0 at he
    simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, sub_eq_zero] at he
    exact hi (he ▸ isAlgebraic_algebraMap (CompactJetPolynomial.center c i))
  obtain ⟨i, hi⟩ := hn
  apply Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (show
      CompactJetPolynomial.coordinates c (CompactJetPolynomial.logPolynomials T) i ^ e i ∈
        CompactJetPolynomial.powerIdeal c (CompactJetPolynomial.logPolynomials T) e from
          Ideal.subset_span (Set.mem_range_self i)))
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow]
  exact (isUnit_iff_ne_zero.mpr hi).pow (e i)

end Curve

end
end PiExponent.ExceptionalCurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_DeterminantContradiction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace PiExponent.DeterminantContradiction

noncomputable def finiteNumerators {nu : ℝ} (d : FixedData nu) : Fin d.m → ℤ :=
  fun i => d.p i.val

noncomputable def finiteDenominators {nu : ℝ} (d : FixedData nu) : Fin d.m → ℕ :=
  fun i => d.q i.val

abbrev Row {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  InterpolationMatrix.Row d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H

abbrev Column {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  InterpolationMatrix.Column d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H

noncomputable def actualMatrix {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    Matrix (Row d H) (Column d H) ℂ :=
  InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)

noncomputable def actualMinor {nu : ℝ} (d : FixedData nu) (H : ℝ)
    (selection : Row d H → Column d H) : Matrix (Row d H) (Row d H) ℂ :=
  MatrixArithmetic.selectedMinor d.K d.w0 d.v0 d.base.theta d.F0 H
    (finiteNumerators d) (finiteDenominators d) selection

noncomputable def actualMean {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  MatrixArithmetic.meanRowWeight d.K d.v0 d.base.theta (finiteDenominators d) H

noncomputable def actualRowCount {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℕ :=
  Fintype.card (Row d H)

noncomputable def lowIndexCount {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℕ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
    ((d.base.A : ℝ) * H)).card

noncomputable def collisionRate {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  collisionConstant * d.base.eta ^ 2 * (actualRowCount d H : ℝ) /
    (H * (lowIndexCount d H : ℝ))

noncomputable def collisionLimit {nu : ℝ} (d : FixedData nu) : ℝ :=
  collisionConstant *
    (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m))

def GlobalInterpolationStatement : Prop :=
  ∀ nu : ℝ, 2 < nu → ∀ d : FixedData nu,
    ∀ L : ℝ, ∃ H : ℝ, L ≤ H ∧ Function.Surjective (actualMatrix d H).mulVecLin

def AnalyticAggregateStatement : Prop :=
  ∀ nu : ℝ, 2 < nu → ∀ d : FixedData nu,
    ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ H : ℝ in atTop, ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
        Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
          d.analyticError + error H +
            max (-collisionRate d H)
              (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H))

end PiExponent.DeterminantContradiction

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_LiteralAnalyticSummand
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.LiteralAnalytic
open DeterminantContradiction

noncomputable def fixedWeights {nu : ℝ} (d : FixedData nu) : Fin d.m → ℝ :=
  MatrixArithmetic.logWeights (finiteDenominators d)

abbrev Transverse {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  ↥(MatrixTranslation.transverseIndices (fixedWeights d) H)

noncomputable def beta {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) : Fin d.m →₀ ℕ :=
  InterpolationMatrix.exponentVector (fun i => r.2.1 i.succ)

abbrev RowChoice {nu : ℝ} (d : FixedData nu) (H : ℝ) (r : Row d H) :=
  RowTranslation.RowChoices (MatrixTranslation.transverseIndices (fixedWeights d) H)
    (beta d r) (r.2.1 0)

abbrev ChoiceFamily {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  ∀ r : Row d H, RowChoice d H r

noncomputable def indexWeight {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : Transverse d H) : ℝ :=
  MatrixTranslationBounds.weight (fixedWeights d) (fun i => a.1 i)

noncomputable def rowWeight {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) : ℝ :=
  MatrixTranslationBounds.weight (fixedWeights d) (fun i => beta d r i)

noncomputable def choiceScalar {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) : ℂ :=
  RowTranslation.rowScalar
    (fun i => (r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - logarithmicPeriod))
    (fun i => RowTranslation.tail
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) (PowerSeries.log ℂ))
    (beta d r) t.1.1 t.2.1 t.2.2

noncomputable def choiceMatrix {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) : Matrix (Row d H) (Row d H) ℂ :=
  fun r c => PowerSeries.coeff (r.2.1 0 - (f r).2.2)
    ((MatrixTranslation.periodMonomial r.1.val logarithmicPeriod
      ((selection c).1 0) (fun i => (selection c).1 i.succ)).coeff (f r).1.1)

end PiExponent.LiteralAnalytic

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_AnalyticAggregate
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology
open Filter

namespace PiExponent.LiteralAnalytic
open DeterminantContradiction

noncomputable def analyticRemainder {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  Collision.collisionRemainder (actualRowCount d H) H +
    Real.log (translationTermCount d.m d.v0 H : ℝ) / H

end PiExponent.LiteralAnalytic

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedCech
noncomputable section
open scoped BigOperators
open GradedLocalizationExact

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {σR σM : Type*} [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

section Cover
variable {J : Type*} [DecidableEq J] (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)

def evaluate (d : ℤ) {L : Type*} (s : Finset J) (f : L → J)
    (hf : ∀ l, f l ∈ s) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    ProjectiveMonomialCechHigher.Cochain L (IntersectionPiece 𝒜 𝓜 x hx s d) q :=
  fun t => setRestriction 𝒜 𝓜 x hx (tupleSet_subset s f hf t) d (c (f ∘ t))

end Cover

end
end PiExponent.GradedCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedCechBound
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FiniteTupleCech
noncomputable section
open scoped BigOperators
open GradedCech (tupleSet tupleSet_comp_subset tupleSet_subset)
variable {J : Type*} [DecidableEq J] (D : Finset J → Type*)
  [∀ s, AddCommGroup (D s)]
  (r : ∀ {s t : Finset J}, s ⊆ t → D s →+ D t)
  (rid : ∀ s (z : D s), r (s := s) le_rfl z = z)
  (rcomp : ∀ {s t u : Finset J} (hst : s ⊆ t) (htu : t ⊆ u) (z : D s),
    r htu (r hst z) = r (hst.trans htu) z)

def evaluate (s : Finset J) {q : ℕ} (c : Cochain D q) :
    ProjectiveMonomialCechHigher.Cochain s (D s) q :=
  fun t => r (tupleSet_subset s Subtype.val (fun j => j.property) t) (c (Subtype.val ∘ t))

def assemble {q k : ℕ}
    (B : ∀ s : Finset J, s.card = k → ProjectiveMonomialCechHigher.Cochain s (D s) q) :
    Cochain D q := fun t =>
  if h : (tupleSet t).card = k then B (tupleSet t) h (liftTo (tupleSet t) t le_rfl) else 0

end
end PiExponent.FiniteTupleCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedH0
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedH0
noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

def NonnegativeMonomialSet (d : ℤ) : Set (Monomial ι d) :=
  {a | ∀ j, 0 ≤ a.val j}

def encode (n : ℕ) (b : PolynomialExponent (ι := ι) n) : Monomial ι (n : ℤ) :=
  ⟨fun j => (b.val j : ℤ), by
    rw [← Nat.cast_sum, ← Finsupp.degree_eq_sum, b.property]⟩

@[simp] theorem encode_apply (n : ℕ) (b : PolynomialExponent (ι := ι) n) (j : ι) :
    (encode n b).val j = (b.val j : ℤ) := rfl

theorem encode_nonnegative (n : ℕ) (b : PolynomialExponent (ι := ι) n) :
    encode n b ∈ NonnegativeMonomialSet (n : ℤ) := fun _j => Int.natCast_nonneg _

def decode (n : ℕ) (a : NonnegativeMonomialSet (ι := ι) (n : ℤ)) :
    PolynomialExponent (ι := ι) n := by
  let b : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => (a.val.val j).toNat)
  refine ⟨b, ?_⟩
  apply Int.natCast_inj.mp
  calc
    (b.degree : ℤ) = ∑ j, ((a.val.val j).toNat : ℤ) := by
      rw [Finsupp.degree_eq_sum, Nat.cast_sum]
      rfl
    _ = ∑ j, a.val.val j := by
      apply Finset.sum_congr rfl
      intro j _
      exact Int.toNat_of_nonneg (a.property j)
    _ = (n : ℤ) := a.val.property

@[simp] theorem decode_apply (n : ℕ) (a : NonnegativeMonomialSet (ι := ι) (n : ℤ))
    (j : ι) : (decode n a).val j = (a.val.val j).toNat := rfl

def exponentEquiv (n : ℕ) :
    PolynomialExponent (ι := ι) n ≃ NonnegativeMonomialSet (ι := ι) (n : ℤ) where
  toFun b := ⟨encode n b, encode_nonnegative n b⟩
  invFun := decode n
  left_inv b := by
    apply Subtype.ext
    ext j
    simp
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    simp only [encode_apply, decode_apply]
    exact Int.toNat_of_nonneg (a.property j)

def homogeneousPolynomialEquiv (n : ℕ) :
    MvPolynomial.homogeneousSubmodule ι R n ≃ₗ[R]
      Finsupp.supported R R (NonnegativeMonomialSet (ι := ι) (n : ℤ)) :=
  (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported ι R n)).trans <|
    (AddMonoidAlgebra.supportedEquivFinsupp {b : ι →₀ ℕ | b.degree = n}).trans <|
      (Finsupp.domLCongr (exponentEquiv n)).trans
        (Finsupp.supportedEquivFinsupp (NonnegativeMonomialSet (ι := ι) (n : ℤ))).symm

def polynomialLaurent (n : ℕ) :
    MvPolynomial.homogeneousSubmodule ι R n →ₗ[R] Laurent ι R (n : ℤ) :=
  (Finsupp.supported R R (NonnegativeMonomialSet (ι := ι) (n : ℤ))).subtype.comp
    (homogeneousPolynomialEquiv n).toLinearMap

end
end PiExponent.GradedH0

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedPolynomialLaurent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedPolynomialLaurent
noncomputable section
open scoped BigOperators
open PiExponent.GradedCech PiExponent.GradedLocalizationExact PiExponent.ProjectiveMonomialCech
attribute [local instance] Classical.propDecidable MvPolynomial.weightedGradedAlgebra
variable {J R : Type*} [CommRing R]

variable [Fintype J]

def pieceToLaurent (s : Finset J) (d : ℤ) : Piece (R := R) s d →+ Laurent J R d :=
  (Finsupp.subtypeDomainAddMonoidHom (p := fun a : J → ℤ => ∑ j, a j = d)).comp
    ((AddMonoidAlgebra.coeffAddEquiv).toAddMonoidHom.comp
      ((moduleToGroupAlgebra s).comp (degreePiece grading grading (product s)
        s.card (product_mem s) d).subtype))

@[simp] theorem pieceToLaurent_coefficient (s : Finset J) (d : ℤ)
    (z : Piece (R := R) s d) (a : Monomial J d) :
    pieceToLaurent s d z a = (moduleToGroupAlgebra s z.val).coeff a.val := rfl

end
end PiExponent.GradedPolynomialLaurent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedPolynomialCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedPolynomialCech
noncomputable section
open scoped BigOperators
open PiExponent.GradedLocalizationExact PiExponent.GradedCech PiExponent.GradedPolynomialLaurent PiExponent.ProjectiveMonomialCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]

def intersectionToPiece (s : Finset J) (d : ℤ) :
    IntersectionPiece (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem s d →+ Piece (R := R) s d where
  toFun z := ⟨z.val, z.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def intersectionToLaurent (s : Finset J) (d : ℤ) :
    IntersectionPiece (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem s d →+ Laurent J R d :=
  (pieceToLaurent s d).comp (intersectionToPiece s d)

@[simp] theorem intersectionToLaurent_apply (s : Finset J) (d : ℤ)
    (z : IntersectionPiece (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem s d) :
    intersectionToLaurent s d z = pieceToLaurent s d z := rfl

def cochainToLaurent (d : ℤ) (q : ℕ) :
    Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q →+
      ProjectiveMonomialCechHigher.Cochain J (Laurent J R d) q where
  toFun c t := intersectionToLaurent (tupleSet t) d (c t)
  map_zero' := by funext t; exact map_zero _
  map_add' c b := by funext t; exact map_add _ _ _

@[simp] theorem cochainToLaurent_apply (d : ℤ) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q)
    (t : Fin (q + 1) → J) :
    cochainToLaurent d q c t = pieceToLaurent (tupleSet t) d (c t) := rfl

end
end PiExponent.GradedPolynomialCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedFreeCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedFreeCech
noncomputable section
open PiExponent.GradedCech PiExponent.GradedLocalizationFree
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R B : Type*} [DecidableEq J] [CommRing R] [Fintype B]
  (w : B → ℤ)

def coordinateIntersection (s : Finset J) (d : ℤ) :
    IntersectionPiece (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem s d →+
    (∀ b, IntersectionPiece (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem s (d - w b)) where
  toFun z b := coordinatePieces (grading (J := J) (R := R)) w (product s) _ (product_mem s) d z b
  map_zero' := by funext b; exact congrFun (map_zero _) b
  map_add' z z' := by funext b; exact congrFun (map_add _ _ _) b

@[simp] theorem coordinateIntersection_apply (s : Finset J) (d : ℤ)
    (z : IntersectionPiece (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem s d) (b : B) :
    coordinateIntersection w s d z b =
      coordinatePieces (grading (J := J) (R := R)) w (product s) _ (product_mem s) d z b := rfl

def coordinateCochain (d : ℤ) (q : ℕ) :
    Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      (MvPolynomial.X : J → MvPolynomial J R) variable_mem d q →+
    (∀ b, Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem (d - w b) q) where
  toFun c b t := coordinateIntersection w (tupleSet t) d (c t) b
  map_zero' := by funext b t; exact congrFun (map_zero _) b
  map_add' c e := by funext b t; exact congrFun (map_add _ _ _) b

end
end PiExponent.GradedFreeCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveGlobalPolynomialAlgebra
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra
noncomputable section
open scoped BigOperators
open MvPolynomial
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponentSeshadri.Projective


variable {σ K : Type*} [Fintype σ] [CommRing K]

def chartExponent (i : σ) (b : σ →₀ ℕ) : ChartExponent i :=
  Finsupp.equivFunOnFinite.symm (fun j => b j.val)

@[simp] theorem chartExponent_apply (i : σ) (b : σ →₀ ℕ) (j : ChartVariables i) :
    chartExponent i b j = b j.val := rfl

end
end PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealModuleRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma restrictedInclusion_structureMap_eq_zero (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    restrictedInclusion I f ≫ structureMap (I.comap f).subschemeι = 0 := by
  apply hom_ext_affine
  intro U
  ext x
  change (I.comap f).subschemeι.app U.1 ((restrictedInclusion I f).app U.1 x) = 0
  apply RingHom.mem_ker.mp
  rw [(I.comap f).ker_subschemeι_app U, ← restricted_image I f U]
  exact ⟨x,rfl⟩

def restrictedToClosed (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (closedModule I).restrict f ⟶ closedModule (I.comap f) :=
  kernel.lift (structureMap (I.comap f).subschemeι) (restrictedInclusion I f)
    (restrictedInclusion_structureMap_eq_zero I f)

@[reassoc (attr := simp)] lemma restrictedToClosed_inclusion (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    restrictedToClosed I f ≫ closedInclusion (I.comap f) = restrictedInclusion I f :=
  kernel.lift_ι _ _ _

instance restrictedToClosed_isIso (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    IsIso (restrictedToClosed I f) := by
  apply isIso_of_affine_app
  intro U
  let : Mono (closedInclusion (I.comap f)).val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules X).map (closedInclusion (I.comap f))))
  let : Mono (restrictedInclusion I f).val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules X).map (restrictedInclusion I f)))
  have ht : Function.Injective ((closedInclusion (I.comap f)).app U.1) := by
    exact PresheafOfModules.injective_of_mono (closedInclusion (I.comap f)).val (op U.1)
  have hs : Function.Injective ((restrictedInclusion I f).app U.1) := by
    exact PresheafOfModules.injective_of_mono (restrictedInclusion I f).val (op U.1)
  have he (x : Γ((closedModule I).restrict f,U.1)) :
      (closedInclusion (I.comap f)).app U.1 ((restrictedToClosed I f).app U.1 x) =
        (restrictedInclusion I f).app U.1 x :=
    congrArg (fun g => g.app U.1 x) (restrictedToClosed_inclusion I f)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    apply hs
    rw [← he x, ← he y, h]
  · intro x
    have hx : (closedInclusion (I.comap f)).app U.1 x ∈ (I.comap f).ideal U := by
      rw [← closed_image (I.comap f) U]
      exact ⟨x,rfl⟩
    rw [← restricted_image I f U] at hx
    obtain ⟨y,hy⟩ := hx
    exact ⟨y, ht ((he y).trans hy)⟩

def closedModuleRestrictIso (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (closedModule I).restrict f ≅ closedModule (I.comap f) := asIso (restrictedToClosed I f)

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPullbackMap
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.IdealPullbackMap
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (hIJ : I ≤ J.map f)

include hIJ in

theorem comp_quotient_zero :
    (closedInclusion I ≫ structureMap f) ≫
      (Scheme.Modules.pushforward f).map (structureMap J.subschemeι) = 0 := by
  apply hom_ext_affine
  intro U
  ext x
  have hr : (closedInclusion I).app U.1 x ∈ I.ideal U := by
    rw [← closed_image I U]
    exact ⟨x, rfl⟩
  let r : Γ(X, U.1) := (closedInclusion I).app U.1 x
  have hz : r ∈ (J.subschemeι ≫ f).ker.ideal U := (hIJ U) hr
  rw [Scheme.Hom.ker_apply] at hz
  change (J.subschemeι ≫ f).app U.1 r = 0 at hz
  rw [Scheme.Hom.comp_app] at hz
  exact hz

def map : closedModule I ⟶ (Scheme.Modules.pushforward f).obj (closedModule J) :=
  kernel.lift ((Scheme.Modules.pushforward f).map (structureMap J.subschemeι))
    (closedInclusion I ≫ structureMap f) (comp_quotient_zero f I J hIJ) ≫
      (PreservesKernel.iso (Scheme.Modules.pushforward f) (structureMap J.subschemeι)).inv

@[reassoc (attr := simp)] theorem map_inclusion :
    map f I J hIJ ≫ (Scheme.Modules.pushforward f).map (closedInclusion J) =
      closedInclusion I ≫ structureMap f := by
  rw [map]
  erw [Category.assoc]
  have he : (PreservesKernel.iso (Scheme.Modules.pushforward f)
      (structureMap J.subschemeι)).inv ≫
      (Scheme.Modules.pushforward f).map (closedInclusion J) =
      kernel.ι ((Scheme.Modules.pushforward f).map (structureMap J.subschemeι)) :=
    PreservesKernel.iso_inv_ι _ _
  erw [he, kernel.lift_ι]

def comap : closedModule I ⟶ (Scheme.Modules.pushforward f).obj (closedModule (I.comap f)) :=
  map f I (I.comap f) (I.le_map_comap f)

@[reassoc (attr := simp)] theorem comap_inclusion :
    comap f I ≫ (Scheme.Modules.pushforward f).map (closedInclusion (I.comap f)) =
      closedInclusion I ≫ structureMap f := map_inclusion _ _ _ _

end
end PiExponent.GeometrySupport.IdealPullbackMap

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealSectionRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.IdealSectionRestriction
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}}

def sectionsEquiv (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) :
    Γ(closedModule I, f ''ᵁ U) ≃+ Γ(closedModule (I.comap f), U) :=
  ((closedModule I).restrictAppIso f U).symm.addCommGroupIsoToAddEquiv.trans
    (asIso ((closedModuleRestrictIso I f).hom.app U)).addCommGroupIsoToAddEquiv

def pullback (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    Γ(closedModule I,U) →+ Γ(closedModule (I.comap f),V) :=
  ((closedModule (I.comap f)).presheaf.map (homOfLE h).op).hom.comp
    ((GeometrySupport.IdealPullbackMap.comap f I).app U).hom

def idealCongr {I J : Y.IdealSheafData} (h : I = J) (U : Y.Opens) :
    Γ(closedModule I,U) ≃+ Γ(closedModule J,U) := by
  subst J
  exact AddEquiv.refl _

end PiExponent.IdealSectionRestriction

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GradedSerreStep
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedSerreStep
noncomputable section
open PiExponent.GradedCech PiExponent.GradedPolynomialLaurent
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R M σM : Type*} [Fintype J] [DecidableEq J] [CommRing R]
  [IsNoetherianRing R] [AddCommGroup M] [Module (MvPolynomial J R) M]
  [Module.Finite (MvPolynomial J R) M] [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (grading (J := J) (R := R)) 𝓜]

def HasPrimitive (d : ℤ) (q : ℕ) : Prop :=
  ∀ c : Cochain (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d (q + 1),
    differential (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d c = 0 →
    ∃ b : Cochain (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d q,
      differential (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d b = c

def HasRecovery (d : ℤ) : Prop :=
  ∀ c : Cochain (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d 0,
    differential (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d c = 0 →
    ∃ m : 𝓜 d, augmentation (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d m = c

end
end PiExponent.GradedSerreStep

end OAI
end


