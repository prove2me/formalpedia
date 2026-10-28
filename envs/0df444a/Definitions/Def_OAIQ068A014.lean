-- Prove2me | Definitions.Def_OAIQ068A014
-- name    : OAIQ068A014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:45:13.708045+00:00
-- url     : https://prove2.me/theorems/2847a9a5-2920-4e4c-a1f3-d5c7dc5f8f43
-- title:
--   Definitions bundle OAIQ068A014 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 82 declarations of OpenAI's Lean: 27 definitions, 13 instances and 42 theorems. The definitions and types are `OAI.PiExponent.AdmissibleBlowupGeometry.pureIndex`, `OAI.PiExponent.CurveBlowupImage.imageCurve`, `OAI.PiExponent.CurveBlowupImage.imageFunctionFieldIso`, `OAI.PiExponent.CurveBlowupImage.imageMap`, `OAI.PiExponent.CurveModelPlaces.chartValuation`, `OAI.PiExponent.CurveNormalizationModel.infinityChartInclusion`, `OAI.PiExponent.CurveNormalizationModel.infinityChartStalkIso`, `OAI.PiExponent.CurveNormalizationModel.infinityOverlap`, `OAI.PiExponent.CurveNormalizationModel.parameterChartOverlapHom`, `OAI.PiExponent.CurveNormalizationModel.parameterChartProjection`, `OAI.PiExponent.CurveNormalizationModel.parameterCurve`, `OAI.PiExponent.CurveNormalizationModel.parameterCurveFunctionFieldIso`, `OAI.PiExponent.CurveNormalizationModel.zeroChartInclusion`, `OAI.PiExponent.CurveNormalizationModel.zeroChartStalkIso`, `OAI.PiExponent.CurveNormalizationModel.zeroOverlap`, `OAI.PiExponent.InverseFrames.regularValue`, `OAI.PiExponent.ParameterResidueField.parameterChartConstants`, `OAI.PiExponent.PlaceValuationRing.constantsHom`, `OAI.PiExponent.PlaceValuationRing.ring`, `OAI.PiExponent.WeightedPolynomialPole.coordinateOrder`, `OAI.PiExponent.WeightedPolynomialPole.coordinatePole`, `OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.inverse`, `OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.one`, `OAI.PiExponentSeshadri.LineBundleGluing.chartPresheafFrame`, `OAI.PiExponentSeshadri.LineBundleGluing.inverseProduct`, `OAI.PiExponentSeshadri.LineBundleGluing.inverseProductMap`, `OAI.PiExponentSeshadri.ModuleFlasque.freeOpenMap`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AdmissibleBlowupGeometry`, `PiExponent_Ampleness_CurveBlowupImage`, `PiExponent_Ampleness_CurveBlowupImageBase`, `PiExponent_Approximation_CocycleTensor`, `PiExponent_Approximation_CocycleTensorIso`, `PiExponent_Approximation_FrameSubopensCoherence`, `PiExponent_Approximation_IntegralLineSections`, `PiExponent_Approximation_InverseFrames`, `PiExponent_Cohomology_CurveFinitePushforwardCohomology`, `PiExponent_Cohomology_FiniteCoverCohomology`, `PiExponent_Geometry_CurveContactSum`, `PiExponent_Geometry_CurveModelPlaces`, `PiExponent_Geometry_CurveNormalizationDimension`, `PiExponent_Geometry_CurveNormalizationLocalRing`, `PiExponent_Geometry_CurveNormalizationModel`, `PiExponent_Geometry_CurveNormalizationOverlap`, `PiExponent_Geometry_CurveProperImageDimension`, `PiExponent_Geometry_LineBundleGluing`, `PiExponent_Geometry_PlaceValuationRing`, `PiExponent_Geometry_ProjectiveLineCharts`, `PiExponent_Geometry_SheafificationUnitIso`, `PiExponent_LocalAlgebra_ParameterResidueField`, `PiExponent_LocalAlgebra_WeightedLocalLattice`, `PiExponent_Polynomials_WeightedPolynomialPole`.
--
--   **Imports.** It imports the bundles `OAIQ068A000`, `OAIQ068A001`, `OAIQ068A002`, `OAIQ068A003` and `OAIQ068A004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A021`, `OAIQ068A022`, `OAIQ068A023`, `OAIQ068A024`, `OAIQ068A025` and `OAIQ068A026`; the statement `OAI_PiExponent_AdmissibleMatrixInterpolation_globalInterpolation`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A000
import Definitions.Def_OAIQ068A001
import Definitions.Def_OAIQ068A002
import Definitions.Def_OAIQ068A003
import Definitions.Def_OAIQ068A004

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FiniteCoverCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace ModuleFlasque
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

abbrev freeOpenMap {U V : Opens X} (i : U ⟶ V) : freeOpen R U ⟶ freeOpen R V :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (yoneda.map i))

end ModuleFlasque

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_IntegralLineSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Frames
open CategoryTheory AlgebraicGeometry
variable {X Y : Scheme}
lemma coefficient_zero {M : X.Modules} (e : M ≅ O X) :
    coefficient e (0 : O X ⟶ M) = 0 := by
  rw [coefficient, CategoryTheory.Limits.zero_comp]
  rfl
lemma restrictSection_zero (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules} :
    restrictSection φ (0 : O X ⟶ M) = 0 := by
  ext U a
  rfl
end Frames

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_LineBundleGluing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.LineBundleGluing

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry

variable {X : Scheme} {ι : Type} (U : ι → X.Opens)

variable {U} (c : Cocycle U)

def chartPresheafFrame (i : ι) :
    (modulePresheafRestrict (U i).ι).obj (presheaf c) ≅
      (SheafOfModules.unit (U i).toScheme.ringCatSheaf).val :=
  openPresheafFrame c i (U i) le_rfl

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

end PiExponentSeshadri.LineBundleGluing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_WeightedPolynomialPole
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.WeightedPolynomialPole
open WeightedCurveDegree PolynomialPoleBound

variable {K ι : Type*} [Field K] [Fintype ι]

def coordinateOrder (v : AddValuation K (WithTop ℤ)) (x : K) : ℤ := by
  classical
  exact if h : x = 0 then 0 else integerOrder v (Units.mk0 x h)

def coordinatePole (v : AddValuation K (WithTop ℤ)) (x : ι → K) (w : ι → ℚ) : ℚ :=
  weightedPole w (fun i => (coordinateOrder v (x i) : ℚ))

@[simp] theorem realValuation_of_ne_zero (v : AddValuation K (WithTop ℤ))
    (x : K) (hx : x ≠ 0) :
    realValuation v x = ((coordinateOrder v x : ℝ) : WithTop ℝ) := by
  rw [coordinateOrder, dite_eq_right hx, realValuation_apply]
  have h : v x = (integerOrder v (Units.mk0 x hx) : WithTop ℤ) :=
    (coe_integerOrder v (Units.mk0 x hx)).symm
  rw [h, WithTop.map_coe]

end PiExponent.WeightedPolynomialPole

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContactSum
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveContactSum

open WeightedPolynomialPole WeightedCurveDegree CurveValuationCenter PolynomialPoleBound

theorem coordinatePole_eq_zero {E ι : Type*} [Field E] [Fintype ι]
    (v : AddValuation E (WithTop ℤ)) (x : ι → E) (w : ι → ℚ)
    (hx : ∀ i, coordinateOrder v (x i) = 0) : coordinatePole v x w = 0 := by
  unfold coordinatePole weightedPole
  simp only [hx, Int.cast_zero, neg_zero, zero_div]
  have he : (fun i : Option ι => i.elim 0 (fun _ => (0 : ℚ))) = fun _ => 0 := by
    funext i
    cases i <;> rfl
  rw [he]
  exact Finset.sup'_const _ _

theorem coordinatePole_finite_support {E ι P : Type*} [Field E] [Fintype ι]
    (v : P → AddValuation E (WithTop ℤ)) (x : ι → E) (w : ι → ℚ)
    (hfinite : ∀ i, Set.Finite {p | coordinateOrder (v p) (x i) ≠ 0}) :
    Set.Finite {p | coordinatePole (v p) x w ≠ 0} := by
  have hu : Set.Finite (⋃ i, {p | coordinateOrder (v p) (x i) ≠ 0}) :=
    Set.finite_iUnion (fun i => hfinite i)
  apply hu.subset
  intro p hp
  by_contra hn
  apply hp
  apply coordinatePole_eq_zero
  intro i
  by_contra hi
  exact hn (Set.mem_iUnion.mpr ⟨i,hi⟩)

end PiExponent.CurveContactSum

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceValuationRing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.PlaceValuationRing

open CurveValuationCenter WeightedCurveDegree

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

abbrev ring (p : NormalizedPlace F E) : ValuationSubring E :=
  p.valuation.toValuation.valuationSubring

def constantsHom (p : NormalizedPlace F E) : F →+* ring p where
  toFun c := ⟨algebraMap F E c, p.constants_nonneg c⟩
  map_zero' := by ext; exact map_zero _
  map_one' := by ext; exact map_one _
  map_add' _ _ := by ext; exact map_add _ _ _
  map_mul' _ _ := by ext; exact map_mul _ _ _

instance constantsAlgebra (p : NormalizedPlace F E) : Algebra F (ring p) :=
  (constantsHom p).toAlgebra

@[simp] theorem constants_algebraMap (p : NormalizedPlace F E) (c : F) :
    (algebraMap F (ring p) c : E) = algebraMap F E c := rfl

instance valuation_nontrivial (p : NormalizedPlace F E) :
    p.valuation.toValuation.IsNontrivial := by
  obtain ⟨z, hz⟩ := p.normalized
  apply (Valuation.isNontrivial_iff_exists_lt_one _).mpr
  refine ⟨z, z.ne_zero, ?_⟩
  change (0 : WithTop ℤ) < p.valuation (z : E)
  rw [← coe_integerOrder, hz]
  norm_num

instance discreteValuationRing (p : NormalizedPlace F E) :
    IsDiscreteValuationRing (ring p) := by
  let : IsCyclic (Multiplicative (OrderDual (WithTop ℤ)))ˣ :=
    inferInstanceAs (IsCyclic (WithZero (Multiplicative ℤ))ˣ)
  let : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass p.valuation.toValuation)) := by
    infer_instance
  exact Valuation.valuationSubring_isDiscreteValuationRing p.valuation.toValuation

end PiExponent.PlaceValuationRing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ParameterResidueField
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ParameterResidueField
open scoped Polynomial nonZeroDivisors
open CurveZeroPole CurveValuationCenter

abbrev parameterChartConstants
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra F (parameterChart f hf) :=
  let := parameterPolynomialAlgebra f hf
  ((algebraMap F[X] (parameterChart f hf)).comp Polynomial.C).toAlgebra

theorem parameterChartConstants_tower
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    letI := parameterPolynomialAlgebra f hf
    letI := parameterChartConstants f hf
    IsScalarTower F F[X] (parameterChart f hf) := by
  let := parameterPolynomialAlgebra f hf
  let := parameterChartConstants f hf
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem parameter_residue_finite
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) :
    letI := parameterChartConstants f hf
    Module.Finite F (IsLocalRing.ResidueField (Localization.AtPrime q.1)) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let := parameterChartConstants f hf
  let := parameterChartConstants_tower f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  let : Algebra.FiniteType F S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F F[X]) (inferInstance : Algebra.FiniteType F[X] S)
  let : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q.1 (zeroPrime F)
  exact residue_finite q.1

theorem parameter_residue_integral
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) :
    letI := parameterChartConstants f hf
    Algebra.IsIntegral F (IsLocalRing.ResidueField (Localization.AtPrime q.1)) := by
  let := parameterChartConstants f hf
  let := parameter_residue_finite f hf q
  exact Algebra.IsIntegral.of_finite F _

end PiExponent.ParameterResidueField

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_WeightedLocalLattice
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open PiExponent.WeightedCurveDegree PiExponent.CurveLocalOrder

namespace PiExponent.WeightedLocalLattice

theorem exists_local_element_iff_nonnegative_order
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (x : K) :
    (∃ a : A, algebraMap A K a = x) ↔ 0 ≤ fractionAddValuation A K x := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [fractionAddValuation_algebraMap, localAddValuation_apply]
    have h := enatToIntegerOrder_monotone (show (0 : ℕ∞) ≤ IsDiscreteValuationRing.addVal A a from bot_le)
    simpa using h
  · intro hx
    by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0]⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
    have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have ha0 : a ≠ 0 := by
      intro ha
      apply hx0
      simp [ha]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
      (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr ha0)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
      (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hb0)
    rw [AddValuation.map_div, fractionAddValuation_algebraMap,
      fractionAddValuation_algebraMap, localAddValuation_apply,
      localAddValuation_apply, ← hm, ← hn] at hx
    change (0 : WithTop ℤ) ≤ ((m : ℤ) : WithTop ℤ) - ((n : ℤ) : WithTop ℤ) at hx
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_zero, WithTop.coe_le_coe] at hx
    have hnm : n ≤ m := by exact_mod_cast (sub_nonneg.mp hx)
    have hdvd : b ∣ a := IsDiscreteValuationRing.addVal_le_iff_dvd.mp (by
      rw [← hm, ← hn]
      exact_mod_cast hnm)
    obtain ⟨c, rfl⟩ := hdvd
    refine ⟨c, ?_⟩
    rw [map_mul, mul_div_cancel_left₀]
    exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb0

end PiExponent.WeightedLocalLattice

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationModel
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.CurveNormalizationModel

open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole

theorem parameterLaurent_scalarTower {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    letI := parameterPolynomialAlgebra f hf
    letI := parameterLaurentAlgebra f hf
    IsScalarTower F[X] (LaurentPolynomial F) E := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  apply IsScalarTower.of_algebraMap_eq
  intro p
  rw [parameterPolynomialAlgebra_map]
  change Polynomial.aeval f p = parameterLaurentMap f hf (Polynomial.toLaurent p)
  rw [parameterLaurentMap, LaurentPolynomial.eval₂_toLaurent]
  rfl

def parameterChartOverlapHom {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    parameterChart f hf →+* parameterLaurentChart f hf := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  let := parameterLaurent_scalarTower f hf
  exact integralClosureTowerHom

theorem parameterChartOverlap_isOpenImmersion
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (parameterChartOverlapHom f hf))) := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  let := parameterLaurent_scalarTower f hf
  have hunit : IsLocalization.Away f E := IsLocalization.of_le_isUnit (by
    rintro x ⟨n, rfl⟩
    exact (isUnit_iff_ne_zero.mpr hf.ne_zero).pow n)
  have hX : algebraMap F[X] E Polynomial.X = f := by
    rw [parameterPolynomialAlgebra_map]
    simp
  have : IsLocalization.Away (algebraMap F[X] E Polynomial.X) E := by
    simpa only [hX] using hunit
  exact integralClosureTower_SpecMap_isOpenImmersion (S := LaurentPolynomial F) (E := E)
    (Polynomial.X : F[X])

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def zeroOverlap : Spec (.of (parameterLaurentChart f hf)) ⟶ Spec (.of (parameterChart f hf)) :=
  Spec.map (CommRingCat.ofHom (parameterChartOverlapHom f hf))

instance zeroOverlap_isOpenImmersion : IsOpenImmersion (zeroOverlap f hf) :=
  parameterChartOverlap_isOpenImmersion f hf

def infinityOverlap : Spec (.of (parameterLaurentChart f hf)) ⟶
    Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf))) :=
  Spec.map (CommRingCat.ofHom ((reciprocalLaurentChartEquiv f hf).symm.toRingHom.comp
    (parameterChartOverlapHom f⁻¹ (transcendental_inverse f hf))))

instance infinityOverlap_isOpenImmersion : IsOpenImmersion (infinityOverlap f hf) := by
  let e := (reciprocalLaurentChartEquiv f hf).symm
  have : IsIso (CommRingCat.ofHom e.toRingHom) :=
    inferInstanceAs (IsIso e.toCommRingCatIso.hom)
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (parameterChartOverlapHom f⁻¹ (transcendental_inverse f hf)))) :=
    parameterChartOverlap_isOpenImmersion f⁻¹ (transcendental_inverse f hf)
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (e.toRingHom.comp (parameterChartOverlapHom f⁻¹ (transcendental_inverse f hf)))))
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

def parameterCurve : Scheme :=
  Limits.pushout (zeroOverlap f hf) (infinityOverlap f hf)

def zeroChartInclusion : Spec (.of (parameterChart f hf)) ⟶ parameterCurve f hf :=
  Limits.pushout.inl (zeroOverlap f hf) (infinityOverlap f hf)

def infinityChartInclusion : Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf))) ⟶
    parameterCurve f hf :=
  Limits.pushout.inr (zeroOverlap f hf) (infinityOverlap f hf)

instance zeroChartInclusion_isOpenImmersion : IsOpenImmersion (zeroChartInclusion f hf) :=
  inferInstanceAs (IsOpenImmersion (Limits.colimit.ι
    (Limits.span (zeroOverlap f hf) (infinityOverlap f hf)) Limits.WalkingSpan.left))

instance infinityChartInclusion_isOpenImmersion : IsOpenImmersion (infinityChartInclusion f hf) :=
  inferInstanceAs (IsOpenImmersion (Limits.colimit.ι
    (Limits.span (zeroOverlap f hf) (infinityOverlap f hf)) Limits.WalkingSpan.right))

theorem parameterCurve_overlap_compatibility :
    zeroOverlap f hf ≫ zeroChartInclusion f hf =
      infinityOverlap f hf ≫ infinityChartInclusion f hf :=
  Limits.pushout.condition

theorem parameterCurve_twoChartCover (x : parameterCurve f hf) :
    (∃ y, zeroChartInclusion f hf y = x) ∨
      ∃ y, infinityChartInclusion f hf y = x := by
  obtain ⟨j, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (Limits.span (zeroOverlap f hf) (infinityOverlap f hf)) x
  cases j with
  | none =>
    left
    refine ⟨zeroOverlap f hf y, ?_⟩
    have hh := congrArg (fun g => g y)
      (Limits.colimit.w (Limits.span (zeroOverlap f hf) (infinityOverlap f hf))
        Limits.WalkingSpan.Hom.fst)
    exact hh.trans hy
  | some j =>
    cases j with
    | left => exact Or.inl ⟨y, hy⟩
    | right => exact Or.inr ⟨y, hy⟩

def zeroChartStalkIso (x : PrimeSpectrum (parameterChart f hf)) :
    (parameterCurve f hf).presheaf.stalk (zeroChartInclusion f hf x) ≅
      CommRingCat.of (Localization.AtPrime x.asIdeal) := by
  have : IsIso ((zeroChartInclusion f hf).stalkMap x) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (zeroChartInclusion_isOpenImmersion f hf)).2 x
  exact asIso ((zeroChartInclusion f hf).stalkMap x) ≪≫
    Spec.stalkIso (.of (parameterChart f hf)) x

def infinityChartStalkIso
    (x : PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf))) :
    (parameterCurve f hf).presheaf.stalk (infinityChartInclusion f hf x) ≅
      CommRingCat.of (Localization.AtPrime x.asIdeal) := by
  have : IsIso ((infinityChartInclusion f hf).stalkMap x) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (infinityChartInclusion_isOpenImmersion f hf)).2 x
  exact asIso ((infinityChartInclusion f hf).stalkMap x) ≪≫
    Spec.stalkIso (.of (parameterChart f⁻¹ (transcendental_inverse f hf))) x

theorem parameterCurve_genericPoint :
    IsGenericPoint
      (zeroChartInclusion f hf (zeroOverlap f hf
        (genericPoint (Spec (.of (parameterLaurentChart f hf)))))) Set.univ := by
  apply isGenericPoint_iff_specializes.mpr
  intro x
  constructor
  · intro _; trivial
  · intro _
    rcases parameterCurve_twoChartCover f hf x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · rw [genericPoint_eq_of_isOpenImmersion (zeroOverlap f hf)]
      exact (genericPoint_specializes y).map (zeroChartInclusion f hf).continuous
    · have he := congrArg
        (fun g => g (genericPoint (Spec (.of (parameterLaurentChart f hf)))))
        (parameterCurve_overlap_compatibility f hf)
      change zeroChartInclusion f hf (zeroOverlap f hf _) =
        infinityChartInclusion f hf (infinityOverlap f hf _) at he
      rw [he, genericPoint_eq_of_isOpenImmersion (infinityOverlap f hf)]
      exact (genericPoint_specializes y).map (infinityChartInclusion f hf).continuous

instance parameterCurve_irreducibleSpace : IrreducibleSpace (parameterCurve f hf) :=
  (irreducibleSpace_def _).mpr (parameterCurve_genericPoint f hf).isIrreducible

instance parameterCurve_isReduced : IsReduced (parameterCurve f hf) := by
  have (x : parameterCurve f hf) : _root_.IsReduced ((parameterCurve f hf).presheaf.stalk x) := by
    rcases parameterCurve_twoChartCover f hf x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact isReduced_of_injective (zeroChartStalkIso f hf y).hom.hom
        (zeroChartStalkIso f hf y).commRingCatIsoToRingEquiv.injective
    · exact isReduced_of_injective (infinityChartStalkIso f hf y).hom.hom
        (infinityChartStalkIso f hf y).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

instance parameterCurve_isIntegral : IsIntegral (parameterCurve f hf) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

def parameterCurveFunctionFieldIso :
    (parameterCurve f hf).functionField ≅ (Spec (.of (parameterChart f hf))).functionField := by
  let x := genericPoint (Spec (.of (parameterChart f hf)))
  have : IsIso ((zeroChartInclusion f hf).stalkMap x) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (zeroChartInclusion_isOpenImmersion f hf)).2 x
  have hx : zeroChartInclusion f hf x = genericPoint (parameterCurve f hf) :=
    genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)
  exact eqToIso (congrArg (fun y => (parameterCurve f hf).presheaf.stalk y) hx.symm) ≪≫
    asIso ((zeroChartInclusion f hf).stalkMap x)

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationLocalRing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.CurveNormalizationModel
open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole

universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def parameterChartProjection : Spec (.of (parameterChart f hf)) ⟶ Spec (.of F[X]) :=
  letI := parameterPolynomialAlgebra f hf
  Spec.map (CommRingCat.ofHom (algebraMap F[X] (parameterChart f hf)))

instance parameterChartProjection_isFinite [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsFinite (parameterChartProjection f hf) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  rw [parameterChartProjection, IsFinite.SpecMap_iff]
  change (algebraMap F[X] (parameterChart f hf)).Finite
  rw [RingHom.finite_algebraMap]
  infer_instance

theorem parameterChart_localDVR [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : PrimeSpectrum (parameterChart f hf)) (hq : q.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (parameterChart f hf) hq (Localization.AtPrime q.asIdeal)

theorem zeroChart_stalkDVR [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : PrimeSpectrum (parameterChart f hf)) (hq : q.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing
      ((parameterCurve f hf).presheaf.stalk (zeroChartInclusion f hf q)) := by
  let := parameterChart_localDVR f hf q hq
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (zeroChartStalkIso f hf q).commRingCatIsoToRingEquiv.symm

theorem infinityChart_stalkDVR [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf)))
    (hq : q.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing
      ((parameterCurve f hf).presheaf.stalk (infinityChartInclusion f hf q)) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let := parameterChart_localDVR f⁻¹ (transcendental_inverse f hf) q hq
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (infinityChartStalkIso f hf q).commRingCatIsoToRingEquiv.symm

theorem parameterCurve_stalkDVR [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) (hx : x ≠ genericPoint (parameterCurve f hf)) :
    IsDiscreteValuationRing ((parameterCurve f hf).presheaf.stalk x) := by
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · apply zeroChart_stalkDVR f hf q
    intro hq
    have heq : q = genericPoint (Spec (.of (parameterChart f hf))) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext hq
    apply hx
    rw [heq]
    exact genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)
  · apply infinityChart_stalkDVR f hf q
    intro hq
    have heq : q = genericPoint
        (Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext hq
    apply hx
    rw [heq]
    exact genericPoint_eq_of_isOpenImmersion (infinityChartInclusion f hf)

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupGeometry
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open WeightedGeometryScale
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

abbrev pureIndex : Fin (d.m+1) → Index d :=
  (scale d).pureIndex d.curveDegreeWeights_pos

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_CurveBlowupImageBase
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveBlowupImage
open PiExponentSeshadri.Geometry
variable {C X B : Scheme.{0}}

theorem restricted_curve_isClosedImmersion (π : B ⟶ X)
    (C : NumericalAmpleness.IntegralCurve B) (U : X.Opens) [IsIso (π ∣_ U)] :
    IsClosedImmersion ((C.embedding ≫ π) ∣_ U) := by
  rw [morphismRestrict_comp]
  exact IsClosedImmersion.comp (C.embedding ∣_ π ⁻¹ᵁ U) (π ∣_ U)

end PiExponent.CurveBlowupImage

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveProperImageDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveProperImageDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
universe u

theorem target_nongeneric_isClosed {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (f : C ⟶ Y) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim C ≤ 1) (y : Y) (hy : y ≠ genericPoint Y) :
    IsClosed ({y} : Set Y) := by
  obtain ⟨c, rfl⟩ := f.surjective y
  have hc : c ≠ genericPoint C := by
    intro heq
    apply hy
    rw [heq, genericPoint_map f]
  simpa only [Set.image_singleton] using f.isClosedMap {c}
    (CurveMorphismFinite.isClosed_singleton_of_ne_genericPoint C hdim c hc)

theorem dimension_eq_one_of_proper_dominant {C Y : Scheme.{u}}
    [IsIntegral C] [IsIntegral Y] [Nontrivial Y]
    (f : C ⟶ Y) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim C ≤ 1) : topologicalKrullDim Y = 1 := by
  let : PartialOrder Y := specializationOrder Y
  change Order.krullDim (IrreducibleCloseds Y) = 1
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))]
  have hle := (Order.krullDim_le_one_iff_forall_isMin (α := Y)).mpr (by
    intro y hy z hzy
    have hclosed := target_nongeneric_isClosed f hdim y hy
    have hz : z ∈ closure ({y} : Set Y) := specializes_iff_mem_closure.mp hzy
    rw [hclosed.closure_eq] at hz
    exact (show z = y from hz).symm.le)
  have hge := (Order.one_le_krullDim_iff (α := Y)).mpr (by
    obtain ⟨y, hy⟩ := exists_ne (⊤ : Y)
    exact ⟨y, ⊤, lt_top_iff_ne_top.mpr hy⟩)
  exact le_antisymm hle hge

theorem image_dimension_eq_one {C X : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ X) [IsProper f] [IsIntegral f.image] [Nontrivial f.image]
    (hdim : topologicalKrullDim C = 1) : topologicalKrullDim f.image = 1 := by
  have : IsProper (f.toImage ≫ f.imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  let : IsProper f.toImage := IsProper.of_comp f.toImage f.imageι
  exact dimension_eq_one_of_proper_dominant f.toImage hdim.le

theorem image_dimension_eq_one_of_nonconstant {C X : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ X) [IsProper f] [IsIntegral f.image]
    (hdim : topologicalKrullDim C = 1)
    (hnonconstant : ¬ ∃ x : X, Set.range f ⊆ {x}) : topologicalKrullDim f.image = 1 := by
  let : Nontrivial f.image := image_nontrivial_of_nonconstant f hnonconstant
  exact image_dimension_eq_one f hdim

end PiExponent.CurveProperImageDimension

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_CurveBlowupImage
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveBlowupImage
open PiExponentSeshadri.Geometry
variable {X B : Scheme.{0}}

def imageCurve (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    NumericalAmpleness.IntegralCurve X :=
  let f := C.embedding ≫ π
  letI := integral_scheme_image f
  { scheme := f.image
    embedding := f.imageι
    closedImmersion := inferInstance
    integral := inferInstance
    dimension := CurveProperImageDimension.image_dimension_eq_one_of_nonconstant
      f C.dimension hn }

def imageMap (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    C.scheme ⟶ (imageCurve π C hn).scheme := (C.embedding ≫ π).toImage

@[simp] theorem imageMap_comp (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    imageMap π C hn ≫ (imageCurve π C hn).embedding = C.embedding ≫ π :=
  (C.embedding ≫ π).toImage_imageι

instance imageMap_isDominant (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    IsDominant (imageMap π C hn) := by
  change IsDominant (C.embedding ≫ π).toImage
  infer_instance

theorem imageMap_restrict_isIso (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (U : X.Opens) [IsIso (π ∣_ U)] :
    IsIso (imageMap π C hn ∣_ ((imageCurve π C hn).embedding ⁻¹ᵁ U)) := by
  let := restricted_curve_isClosedImmersion π C U
  exact toImage_restrict_isIso (C.embedding ≫ π) U

theorem imageMap_preimage_nonempty (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (U : X.Opens) (hU : ∃ c : C.scheme, (C.embedding ≫ π) c ∈ U) :
    Nonempty (imageMap π C hn ⁻¹ᵁ ((imageCurve π C hn).embedding ⁻¹ᵁ U)) := by
  obtain ⟨c, hc⟩ := hU
  refine ⟨⟨c, ?_⟩⟩
  change (imageCurve π C hn).embedding (imageMap π C hn c) ∈ U
  simpa only [← Scheme.Hom.comp_apply, imageMap_comp] using hc

def imageFunctionFieldIso (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (U : X.Opens) [IsIso (π ∣_ U)]
    (hU : ∃ c : C.scheme, (C.embedding ≫ π) c ∈ U) :
    (imageCurve π C hn).scheme.functionField ≅ C.scheme.functionField :=
  letI := imageMap_restrict_isIso π C hn U
  functionFieldIso (imageMap π C hn) ((imageCurve π C hn).embedding ⁻¹ᵁ U)
    (imageMap_preimage_nonempty π C hn U hU)

theorem imageFunctionFieldIso_generic (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (U : X.Opens) [IsIso (π ∣_ U)]
    (hU : ∃ c : C.scheme, (C.embedding ≫ π) c ∈ U) :
    Spec.map (imageFunctionFieldIso π C hn U hU).hom ≫
      (imageCurve π C hn).scheme.fromSpecStalk
        (genericPoint (imageCurve π C hn).scheme) ≫
      (imageCurve π C hn).embedding =
    C.scheme.fromSpecStalk (genericPoint C.scheme) ≫ C.embedding ≫ π := by
  have h := functionFieldMap_fromSpecStalk (imageMap π C hn)
  change Spec.map (functionFieldMap (imageMap π C hn)) ≫ _ ≫ _ = _
  rw [← Category.assoc, h, Category.assoc, imageMap_comp]

end PiExponent.CurveBlowupImage

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_SheafificationUnitIso
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X : Scheme}

theorem sheafification_unit_isIso_of_iso (P : PresheafOfModules X.ringCatSheaf.obj)
    (M : X.Modules) (e : P ≅ M.val) :
    IsIso ((PiExponentSeshadri.TensorPure.adj X).unit.app P) :=
  (PiExponentSeshadri.TensorPure.adj X).isIso_unit_app_of_iso e

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CocycleTensor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.LineBundleGluing
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

def Cocycle.one : Cocycle U where
  transition _ _ _ _ _ := 1
  restriction _ _ _ _ _ := by simp
  identity _ _ _ := rfl
  cocycle _ _ _ _ _ _ _ := one_mul _

def Cocycle.inverse (c : Cocycle U) : Cocycle U where
  transition i j W hi hj := (c.transition i j W hi hj)⁻¹
  restriction := by
    intro i j V W h hi hj
    have h' : restrictUnit h (c.transition i j _ hi hj) =
        c.transition i j _ (h.trans hi) (h.trans hj) := Units.ext (c.restriction i j h hi hj)
    exact congrArg Units.val ((map_inv (restrictUnit h) _).symm.trans (congrArg Inv.inv h'))
  identity i W hi := by rw [c.identity, inv_one]
  cocycle i j k W hi hj hk := by rw [← mul_inv, c.cocycle]

def inverseProduct (c : Cocycle U) (V : X.Opens)
    (s : sections c V) (t : sections c.inverse V) : sections (Cocycle.one (U := U)) V :=
  ⟨fun p => s.val p * t.val p, by
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op (_ * _) = _
      rw [map_mul, s.property.1 i W W' hW hi h, t.property.1 i W W' hW hi h]
    · intro i j W hW hi hj
      change s.val ⟨i,W,hW,hi⟩ * t.val ⟨i,W,hW,hi⟩ = 1 * _
      rw [s.property.2 i j W hW hi hj, t.property.2 i j W hW hi hj, one_mul]
      change (_ * _) * ((↑((c.transition i j W hi hj)⁻¹ : Γ(X,W)ˣ) : Γ(X,W)) * _) = _
      rw [mul_mul_mul_comm, Units.mul_inv, one_mul]⟩

def inverseProductMap (c : Cocycle U) :
    PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
      (presheaf c) (presheaf c.inverse) ⟶ presheaf (Cocycle.one (U := U)) where
  app V := ModuleCat.MonoidalCategory.tensorLift (inverseProduct c V.unop)
    (by intros; apply Subtype.ext; funext p; exact add_mul _ _ _)
    (by intros; apply Subtype.ext; funext p; exact mul_assoc _ _ _)
    (by intros; apply Subtype.ext; funext p; exact mul_add _ _ _)
    (by intros; apply Subtype.ext; funext p; exact mul_left_comm _ _ _)
  naturality {V W} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    rfl

lemma sheafification_isIso_of_chart {P Q : PresheafOfModules X.ringCatSheaf.obj}
    (f : P ⟶ Q) (hcover : ⊤ ≤ ⨆ i, U i)
    (hf : ∀ i, IsIso ((modulePresheafRestrict (U i).ι).map f)) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f) := by
  apply PiExponent.NumericalAmpleness.isIso_of_locally_isIso
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover (show x ∈ (⊤ : X.Opens) from trivial))
  refine ⟨U i, hi, ?_⟩
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict (U i).ι) f).mpr
  have := hf i
  change IsIso ((PresheafOfModules.sheafification (𝟙 (U i).toScheme.ringCatSheaf.obj)).map
    ((modulePresheafRestrict (U i).ι).map f))
  infer_instance

end PiExponentSeshadri.LineBundleGluing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CocycleTensorIso
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.LineBundleGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

lemma tensorHom_restrict_isIso (W : X.Opens)
    {P P' Q Q' : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ P') (g : Q ⟶ Q')
    [IsIso ((modulePresheafRestrict W.ι).map f)]
    [IsIso ((modulePresheafRestrict W.ι).map g)] :
    IsIso ((modulePresheafRestrict W.ι).map
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) f g)) := by
  let R := modulePresheafRestrict W.ι
  let : MonoidalCategory (PresheafOfModules W.toScheme.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := W.toScheme.presheaf)
  have hh : IsIso (R.map (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) f g) ≫
      (modulePresheafTensorRestrict W P' Q').hom) := by
    rw [modulePresheafTensorRestrict_natural]
    change IsIso (_ ≫ (R.map f ⊗ₘ R.map g))
    infer_instance
  let hc : IsIso (C := PresheafOfModules W.toScheme.ringCatSheaf.obj)
      (modulePresheafTensorRestrict W P' Q').hom :=
    (modulePresheafTensorRestrict W P' Q').isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules W.toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hc).mp hh

end
end PiExponentSeshadri.LineBundleGluing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FrameSubopensCoherence
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X : Scheme} {M : X.Modules} {U V W : X.Opens}

lemma restrictOpenFrame_app (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme)
    (A : V.toScheme.Opens) (x : Γ(M.restrict V.ι,A)) :
    (restrictOpenFrame h e).hom.app A x =
      X.presheaf.map (homOfLE (show V.ι ''ᵁ A ≤ U.ι ''ᵁ (X.homOfLE h ''ᵁ A) from by
        simp [← Scheme.Hom.comp_image])).op
        (e.hom.app (X.homOfLE h ''ᵁ A)
          (M.presheaf.map (homOfLE
            (show U.ι ''ᵁ (X.homOfLE h ''ᵁ A) ≤ V.ι ''ᵁ A from by
              simp [← Scheme.Hom.comp_image])).op x)) := by
  simp only [restrictOpenFrame, Iso.trans_hom, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, Iso.app_inv, Iso.app_hom,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  change ((X.homOfLE h).appIso A).hom (e.hom.app (X.homOfLE h ''ᵁ A)
    ((M.presheaf.map _ ≫ M.presheaf.map _) x)) = _
  simp only [Scheme.Hom.appIso_hom', Scheme.homOfLE_appLE]
  erw [← Functor.map_comp]
  rfl

lemma restrictOpenFrame_trans (h : W ≤ V) (k : V ≤ U)
    (e : M.restrict U.ι ≅ O U.toScheme) :
    restrictOpenFrame h (restrictOpenFrame k e) = restrictOpenFrame (h.trans k) e := by
  apply Iso.ext
  ext A x
  have hh := restrictOpenFrame_app h (restrictOpenFrame k e) A x
  let y := M.presheaf.map (homOfLE
    (show V.ι ''ᵁ (X.homOfLE h ''ᵁ A) ≤ W.ι ''ᵁ A from by
      simp [← Scheme.Hom.comp_image])).op x
  have hk := restrictOpenFrame_app k e (X.homOfLE h ''ᵁ A) y
  have hhk := congrArg (X.presheaf.map (homOfLE
    (show W.ι ''ᵁ A ≤ V.ι ''ᵁ (X.homOfLE h ''ᵁ A) from by
      simp [← Scheme.Hom.comp_image])).op) hk
  have hc := restrictOpenFrame_app (h.trans k) e A x
  refine hh.trans (hhk.trans (Eq.trans ?_ hc.symm))
  change (X.presheaf.map _ ≫ X.presheaf.map _)
    (e.hom.app (X.homOfLE k ''ᵁ (X.homOfLE h ''ᵁ A))
      ((M.presheaf.map _ ≫ M.presheaf.map _) x)) =
    X.presheaf.map _ (e.hom.app (X.homOfLE (h.trans k) ''ᵁ A)
      (M.presheaf.map _ x))
  erw [← Functor.map_comp, ← Functor.map_comp]
  let B := X.homOfLE k ''ᵁ (X.homOfLE h ''ᵁ A)
  let C := X.homOfLE (h.trans k) ''ᵁ A
  have hA : C ≤ B := by
    simp only [B, C, ← Scheme.Hom.comp_image, Scheme.homOfLE_homOfLE]
    exact le_rfl
  have hB : U.ι ''ᵁ B ≤ W.ι ''ᵁ A := by
    simp [B, ← Scheme.Hom.comp_image]
  have hC : W.ι ''ᵁ A ≤ U.ι ''ᵁ C := by
    simp [C, ← Scheme.Hom.comp_image]
  have hn := CategoryTheory.congr_fun
    (e.hom.mapPresheaf.naturality (homOfLE hA).op)
    (M.presheaf.map (homOfLE hB).op x)
  change e.hom.app C ((M.restrict U.ι).presheaf.map (homOfLE hA).op
    (M.presheaf.map (homOfLE hB).op x)) =
    U.toScheme.presheaf.map (homOfLE hA).op
      (e.hom.app B (M.presheaf.map (homOfLE hB).op x)) at hn
  refine Eq.trans ?_ (Eq.trans (congrArg (X.presheaf.map (homOfLE hC).op) hn).symm ?_)
  · change X.presheaf.map _ (e.hom.app B (M.presheaf.map _ x)) =
      (X.presheaf.map _ ≫ X.presheaf.map _) (e.hom.app B (M.presheaf.map _ x))
    erw [← Functor.map_comp]
    rfl
  · apply congrArg (X.presheaf.map (homOfLE hC).op)
    apply congrArg (e.hom.app C)
    change (M.presheaf.map _ ≫ M.presheaf.map _) x = M.presheaf.map _ x
    erw [← Functor.map_comp]
    rfl
end
end PiExponentSeshadri.Frames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_InverseFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
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

def regularValue {P : X.Modules} (f : P ⟶ O X) (U : X.Opens)
    (x : P.val.obj (op U)) : Γ(X,U) := f.app U x

end
end PiExponent.InverseFrames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveFinitePushforwardCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveFinitePushforwardCohomology
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Geometry.BaseSections

variable {K : Type} [Field K] {X Y : Scheme.{0}}

lemma baseScalars_comp (f : Y ⟶ X) (p : X ⟶ Spec (CommRingCat.of ℂ)) :
    baseScalars (f ≫ p) = f.appTop.hom.comp (baseScalars p) := by
  ext c
  simp only [baseScalars, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

end
end PiExponent.CurveFinitePushforwardCohomology

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponent.CurveZeroPole
open scoped Polynomial

universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

attribute [local instance] specializationOrder

theorem parameterCurve_dimension_le_one [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    topologicalKrullDim (parameterCurve f hf) ≤ 1 := by
  have hs (x : parameterCurve f hf) :
      ringKrullDim ((parameterCurve f hf).presheaf.stalk x) ≤ 1 := by
    by_cases hx : x = genericPoint (parameterCurve f hf)
    · subst x
      change ringKrullDim (parameterCurve f hf).functionField ≤ 1
      have h : Ring.KrullDimLE 1 (parameterCurve f hf).functionField := inferInstance
      exact (Ring.krullDimLE_iff.mp h)
    · let := parameterCurve_stalkDVR f hf x hx
      exact (Ring.krullDimLE_iff.mp (inferInstance :
        Ring.KrullDimLE 1 ((parameterCurve f hf).presheaf.stalk x)))
  change Order.krullDim (IrreducibleCloseds (parameterCurve f hf)) ≤ 1
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := parameterCurve f hf)),
    Order.krullDim_eq_iSup_coheight]
  exact iSup_le fun x => by simpa only [ringKrullDim_stalk_eq_coheight] using hs x

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationOverlap
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

theorem zeroOverlap_range :
    letI := parameterPolynomialAlgebra f hf
    Set.range (zeroOverlap f hf) =
      (PrimeSpectrum.basicOpen (algebraMap F[X] (parameterChart f hf) Polynomial.X) :
        Set (PrimeSpectrum (parameterChart f hf))) := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  let := parameterLaurent_scalarTower f hf
  let : Algebra (parameterChart f hf) (parameterLaurentChart f hf) :=
    (parameterChartOverlapHom f hf).toAlgebra
  have hX : algebraMap F[X] E Polynomial.X = f := by
    rw [parameterPolynomialAlgebra_map]; simp
  have : IsLocalization.Away f E := IsLocalization.of_le_isUnit (by
    rintro x ⟨n, rfl⟩
    exact (isUnit_iff_ne_zero.mpr hf.ne_zero).pow n)
  have : IsLocalization.Away (algebraMap F[X] E Polynomial.X) E := by
    simpa only [hX] using (inferInstance : IsLocalization.Away f E)
  have : IsLocalization.Away (algebraMap F[X] (parameterChart f hf) Polynomial.X)
      (parameterLaurentChart f hf) :=
    integralClosureTower_isLocalizationAway (S := LaurentPolynomial F) (E := E) Polynomial.X
  exact PrimeSpectrum.localization_away_comap_range _ _

theorem infinityOverlap_range :
    letI := parameterPolynomialAlgebra f⁻¹ (transcendental_inverse f hf)
    Set.range (infinityOverlap f hf) =
      (PrimeSpectrum.basicOpen
        (algebraMap F[X] (parameterChart f⁻¹ (transcendental_inverse f hf)) Polynomial.X) :
        Set (PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf)))) := by
  let e := (reciprocalLaurentChartEquiv f hf).symm
  have : IsIso (CommRingCat.ofHom e.toRingHom) :=
    inferInstanceAs (IsIso e.toCommRingCatIso.hom)
  let g := Spec.map (CommRingCat.ofHom e.toRingHom)
  have : IsIso g :=
    inferInstanceAs (IsIso (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom)
  have hfac : infinityOverlap f hf =
      g ≫ zeroOverlap f⁻¹ (transcendental_inverse f hf) := by
    unfold infinityOverlap zeroOverlap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hrange : Set.range (infinityOverlap f hf) =
      Set.range (zeroOverlap f⁻¹ (transcendental_inverse f hf)) := by
    rw [hfac]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨g z, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := g.surjective z
      exact ⟨w, rfl⟩
  exact hrange.trans (zeroOverlap_range f⁻¹ (transcendental_inverse f hf))

theorem infinityChart_mem_zero_iff
    (x : Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))) :
    infinityChartInclusion f hf x ∈ Set.range (zeroChartInclusion f hf) ↔
      x ∈ Set.range (infinityOverlap f hf) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨k, fi, fj, z, hzi, hzj⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (Limits.span (zeroOverlap f hf) (infinityOverlap f hf))).mp hy
    cases k with
    | none =>
      refine ⟨z, ?_⟩
      have he : fj = Limits.WalkingSpan.Hom.snd := Subsingleton.elim _ _
      rw [he] at hzj
      exact hzj
    | some k =>
      cases k with
      | left =>
        cases (show Limits.WidePushoutShape.Hom
          (some Limits.WalkingPair.left) (some Limits.WalkingPair.right) from fj)
      | right =>
        cases (show Limits.WidePushoutShape.Hom
          (some Limits.WalkingPair.right) (some Limits.WalkingPair.left) from fi)
  · rintro ⟨z, rfl⟩
    refine ⟨zeroOverlap f hf z, ?_⟩
    exact congrArg (fun g => g z) (parameterCurve_overlap_compatibility f hf)

theorem zeroChart_mem_infinity_iff
    (x : Spec (.of (parameterChart f hf))) :
    zeroChartInclusion f hf x ∈ Set.range (infinityChartInclusion f hf) ↔
      x ∈ Set.range (zeroOverlap f hf) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨k, fi, fj, z, hzi, hzj⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (Limits.span (zeroOverlap f hf) (infinityOverlap f hf))).mp hy.symm
    cases k with
    | none =>
      refine ⟨z, ?_⟩
      have he : fi = Limits.WalkingSpan.Hom.fst := Subsingleton.elim _ _
      rw [he] at hzi
      exact hzi
    | some k =>
      cases k with
      | left =>
        cases (show Limits.WidePushoutShape.Hom
          (some Limits.WalkingPair.left) (some Limits.WalkingPair.right) from fj)
      | right =>
        cases (show Limits.WidePushoutShape.Hom
          (some Limits.WalkingPair.right) (some Limits.WalkingPair.left) from fi)
  · rintro ⟨z, rfl⟩
    refine ⟨infinityOverlap f hf z, ?_⟩
    exact congrArg (fun g => g z) (parameterCurve_overlap_compatibility f hf).symm

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveModelPlaces
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.CurveModelPlaces
universe u
open CurveZeroPole CurveValuationCenter WeightedCurveDegree
open CurveNormalizationModel
open AlgebraicGeometry CategoryTheory

def chartValuation
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf)) :
    AddValuation E (WithTop ℤ) :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  primeFieldValuation (parameterChart f hf) E q

theorem chartValuation_nonneg
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf))
    (a : parameterChart f hf) : 0 ≤ chartValuation f hf q (a : E) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  exact primeFieldValuation_algebraMap_nonneg (parameterChart f hf) E q a

theorem chartValuation_positive_iff
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf))
    (a : parameterChart f hf) : 0 < chartValuation f hf q (a : E) ↔ a ∈ q.asIdeal := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  exact primeFieldValuation_positive_iff (parameterChart f hf) E q a

end PiExponent.CurveModelPlaces

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveLineCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (F : Type u) [CommRing F]

instance boolChartVariablesUnique (i : Bool) : Unique (ChartVariables i) where
  default := ⟨!i, by cases i <;> decide⟩
  uniq j := by
    apply Subtype.ext
    rcases j with ⟨j, hj⟩
    cases i <;> cases j <;> simp_all

lemma unique_dehomogenize (i : Bool) :
    (MvPolynomial.uniqueAlgEquiv F (ChartVariables i)).toRingHom.comp
      (dehomogenize (R := F) i) = lineEvaluation F i := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [dehomogenize, MvPolynomial.uniqueAlgEquiv_apply]
  · intro j
    by_cases h : j = i
    · subst j
      simp
    · simp [dehomogenize, h, MvPolynomial.uniqueAlgEquiv_apply]

end PiExponent.ProjectiveLine

end

end OAI
end


