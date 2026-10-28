-- Prove2me | Definitions.Def_OAIQ10Bp005
-- name    : OAIQ10Bp005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:35:59.367479+00:00
-- url     : https://prove2.me/theorems/65537c5f-2fd6-4004-9ebc-5758d8e2c594
-- title:
--   Definitions bundle OAIQ10Bp005 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 57 definitions and 7 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.FrozenIsomorphismLocal5`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenIsomorphismLocal6`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenOperatorLocal1`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenSurjectiveLocal1`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenSurjectiveLocal2`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenSurjectiveLocal5`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenSurjectiveLocal6`, `OAI.HigherDimensionalBallPacking.Rigidity.affineError`, `OAI.HigherDimensionalBallPacking.Rigidity.affineFamilyCodomainNormedAddCommGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.affineFamilyCodomainNormedSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.affineFamilyDomainNormedSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.affineHolderModuli`, `OAI.HigherDimensionalBallPacking.Rigidity.angularPole`, `OAI.HigherDimensionalBallPacking.Rigidity.blowupPrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.c1Area`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderAffineCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.c1StandardCurl`, `OAI.HigherDimensionalBallPacking.Rigidity.chartCorrection`, `OAI.HigherDimensionalBallPacking.Rigidity.complexDefect`, `OAI.HigherDimensionalBallPacking.Rigidity.correctedPrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.curveDensity`, `OAI.HigherDimensionalBallPacking.Rigidity.curvePrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoffCurl`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoffHolderNormedAddCommGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoffHolderNormedSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.defectDensity`, `OAI.HigherDimensionalBallPacking.Rigidity.densityAffineSize`, `OAI.HigherDimensionalBallPacking.Rigidity.densityCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.densityCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.densityJet`, `OAI.HigherDimensionalBallPacking.Rigidity.densityLinearSlope`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResidual`, `OAI.HigherDimensionalBallPacking.Rigidity.densitySlope`, `OAI.HigherDimensionalBallPacking.Rigidity.dirichletDensity`, `OAI.HigherDimensionalBallPacking.Rigidity.frameConjugation`, `OAI.HigherDimensionalBallPacking.Rigidity.frozenPrincipal`, `OAI.HigherDimensionalBallPacking.Rigidity.gradientLimitsC1NormedAddCommGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.gradientLimitsC1NormedSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.gradientLimitsCompactNormedAddCommGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.gradientLimitsCompactNormedSpace` and 17 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/BallPacking, in whole or in part: `BallPacking_Necessity_AffineEnergy`, `BallPacking_Necessity_AffineSlopes`, `BallPacking_Necessity_C1Energy`, `BallPacking_Necessity_DensityBounds`, `BallPacking_Necessity_DensityLimits`, `BallPacking_Necessity_DensityResidual`, `BallPacking_Necessity_FrozenInverse`, `BallPacking_Necessity_FrozenOperators`, `BallPacking_Necessity_FrozenResponse`, `BallPacking_Necessity_GlobalArea`, `BallPacking_Necessity_GradientLimits`, `BallPacking_Necessity_MarkedProfiles`, `BallPacking_Necessity_NonlinearCR`, `BallPacking_Necessity_PlanarEnergy`, `BallPacking_Necessity_SchauderBounds`, `BallPacking_Rigidity_AngularPoles`, `BallPacking_Rigidity_Correction`, `BallPacking_Rigidity_CurveArea`, `BallPacking_Rigidity_RadialForm`.
--
--   **Imports.** It imports the published bundle `Def_BallPackingNecessity`; the bundles `OAIQ10Bp002` and `OAIQ10Bp003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ10Bp007` and `OAIQ10Bp008`; the statements `OAI.HigherDimensionalBallPacking.Rigidity.affineHolderModuli_isCompact`, `OAI.HigherDimensionalBallPacking.Rigidity.affine_c1_regular`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoff_curl_reconstruct`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResidual_zero_affineLine`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResidual_zero_iff`, `OAI.HigherDimensionalBallPacking.Rigidity.frozenPrincipal_isInvertible`, `OAI.HigherDimensionalBallPacking.Rigidity.frozenPrincipal_surjective`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_Holder_compactness`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_error_energy`, `OAI.HigherDimensionalBallPacking.Rigidity.uniform_density_bounds` and `OAI.HigherDimensionalBallPacking.Rigidity.zero_mem_affineHolderModuli`; the proofs of `OAI.HigherDimensionalBallPacking.Rigidity.affineHolderModuli_isCompact`, `OAI.HigherDimensionalBallPacking.Rigidity.c1_decaying_CR_zero`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoff_curl_reconstruct`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResidual_zero_affineLine`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResidual_zero_iff`, `OAI.HigherDimensionalBallPacking.Rigidity.framed_unmarked_surjective`, `OAI.HigherDimensionalBallPacking.Rigidity.frozenPrincipal_isInvertible`, `OAI.HigherDimensionalBallPacking.Rigidity.frozenPrincipal_surjective`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_Holder_compactness`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_curve_compactness`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_coefficient_extension`, `OAI.HigherDimensionalBallPacking.Rigidity.uniform_density_bounds` and `OAI.HigherDimensionalBallPacking.Rigidity.zero_mem_affineHolderModuli`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/BallPacking at commit adc7f12

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp002
import Definitions.Def_OAIQ10Bp003

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_RadialForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def radialPrimitiveCLM {n : ℕ} (σ τ : ℝ) (x : Phase n) : Phase n →L[ℝ] ℝ :=
  (radialCoefficient σ τ (capacity x) / 2) • stdOmega n x

def infinityGerm {n : ℕ} (u : ℂ → Phase n) (v : Phase n) (w : ℂ) : Phase n :=
  if w = 0 then v else w • u w⁻¹

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CurveArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

def curveDensity {n : ℕ} (σ τ : ℝ) (u : ℂ → Phase n) (z : Plane) : ℝ :=
  radialForm σ τ (realCurve u z)
    (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1))

def curvePrimitive {n : ℕ} (σ τ : ℝ) (u : ℂ → Phase n) : Plane → Plane →L[ℝ] ℝ :=
  planarPullback (realCurve u) (radialPrimitiveCLM σ τ)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def weightedPrimitive {n : ℕ} (g : ℝ → ℝ) (x : Phase n) : Phase n →L[ℝ] ℝ :=
  (g (capacity x) / 2) • stdOmega n x

def blowupPrimitive {n : ℕ} (σ τ : ℝ) : Phase n → Phase n →L[ℝ] ℝ :=
  weightedPrimitive (blowupCoefficient σ τ)



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Correction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def stdPrimitive {n : ℕ} (x : Phase n) : Phase n →L[ℝ] ℝ :=
  (1/2 : ℝ) • stdOmega n x

def inversePullback {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n)
    (α : Phase n → Phase n →L[ℝ] ℝ) (y : Phase n) : Phase n →L[ℝ] ℝ :=
  (α (invFunOn f U y)).comp (fderiv ℝ (invFunOn f U) y)

def chartCorrection {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n)
    (σ τ : ℝ) (y : Phase n) : Phase n →L[ℝ] ℝ := by
  classical
  exact if y ∈ f '' U then inversePullback U f (fun x => blowupPrimitive σ τ x - stdPrimitive x) y
    else 0



open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

def planeRotation (z : Plane) : Plane := (-z.2,z.1)



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_AngularPoles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

def angularPole (p : Plane) (z : Plane) : Plane →L[ℝ] ℝ := angularOneForm (z-p)


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

def correctedPrimitive {n : ℕ} (S T : ℝ) (U : Fin 2 → Set (Phase n))
    (f : Fin 2 → Phase n → Phase n) (σ τ : Fin 2 → ℝ) (y : Phase n) : Phase n →L[ℝ] ℝ :=
  radialPrimitiveCLM S T y + chartCorrection (U 0) (f 0) (σ 0) (τ 0) y +
    chartCorrection (U 1) (f 1) (σ 1) (τ 1) y


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane)



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_GlobalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity


def cutoffCurl (β : Plane → Plane →L[ℝ] ℝ) (A : ℝ) (z : Plane) : ℝ :=
  outerProfile A (radiusSq z) * planarCurl β z

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_AffineEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

def dirichletDensity {n : ℕ} (u : ℂ → Phase n) (z : Plane) : ℝ :=
  stdDot n (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (1,0)) +
  stdDot n (fderiv ℝ (realCurve u) z (0,1)) (fderiv ℝ (realCurve u) z (0,1))

def complexDefect {n : ℕ} (u : ℂ → Phase n) (z : Plane) : Phase n :=
  fderiv ℝ (realCurve u) z (0,1) - standardJ n (fderiv ℝ (realCurve u) z (1,0))

def defectDensity {n : ℕ} (u : ℂ → Phase n) (z : Plane) : ℝ :=
  stdDot n (complexDefect u z) (complexDefect u z)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_PlanarEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

@[simp] theorem euclideanNorm_sq {n : ℕ} (v : Phase n) :
    (euclideanNorm v)^2 = stdDot n v v := by
  simp only [euclideanNorm,phaseEuclidean,PiLp.continuousLinearEquiv_symm_apply,
    EuclideanSpace.norm_sq_eq, stdDot_apply, ←Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]

def horizontalSpeed {n : ℕ} (v : Plane → Phase n) (y x : ℝ) : ℝ :=
  euclideanNorm (fderiv ℝ v (x,y) (1,0))

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_AffineSlopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

def affineError {n : ℕ} (u : ℂ → Phase n) (a : Phase n) : ℂ → Phase n :=
  fun z => u z-z • a








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_C1Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap





open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap







open scoped ContDiff Topology
open Set Filter Function MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open TwoPointContinuation

 def c1Area {n : ℕ} (u : Plane → Phase n) (z : Plane) : ℝ :=
  standardForm (fderiv ℝ u z (1,0)) (fderiv ℝ u z (0,1))

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology
open Set Filter Function MeasureTheory
open SymplecticBallPacking.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_NonlinearCR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction



namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [CompleteSpace E]

def c1HolderAffineCurve (α : ℝ) (c : E) (A : ℂ →L[ℝ] E) (u : C1HolderSpace E α) : ℂ → E :=
  fun z => c+A z+holderValue α (c1HolderValue α u) z

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_MarkedProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction



namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance cutoffHolderNormedAddCommGroup (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedAddCommGroup (HolderSpace K G α) := inferInstance
local instance cutoffHolderNormedSpace (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedSpace ℝ (HolderSpace K G α) := inferInstance

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local instance affineFamilyDomainNormedSpace (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.affineFamilyDomainNormedAddCommGroup
local instance affineFamilyCodomainNormedAddCommGroup (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ F α) := inferInstance
local instance affineFamilyCodomainNormedSpace (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ F α) := inferInstance

end HigherDimensionalBallPacking.Rigidity



open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_SchauderBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open MeasureTheory
open scoped Topology
open Finset
open scoped ContDiff Classical
open scoped BoundedContinuousFunction
open Topology
open scoped NNReal

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance schauderBoundsInst17 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst18 (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst19 (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace F R) := inferInstance
local instance schauderBoundsInst20 (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace F R) := inferInstance

def localSchauderBound (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R D L K : ℝ) : ℝ :=
  2*‖compactCRInverse (E := E) R‖*
    max (3*D) ((2*(3*D))^((2:ℝ)/3)*(3*D*(L+1)+K*D)^((1:ℝ)/3))

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_GradientLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity








open scoped Topology ContDiff
open Set Filter Function







open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance gradientLimitsC1NormedAddCommGroup (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance gradientLimitsC1NormedSpace (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance gradientLimitsCompactNormedAddCommGroup (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace F R) := inferInstance
local instance gradientLimitsCompactNormedSpace (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace F R) := inferInstance

end

 

 

 

open scoped Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function
section
open HigherDimensionalBallPacking.Rigidity

def frameConjugation {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) : End n →L[ℝ] End n :=
  (ContinuousLinearMap.compL ℝ (Phase n) (Phase n) (Phase n) S.toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℝ (Phase n) (Phase n) (Phase n)).flip S.symm.toContinuousLinearMap)

@[simp] theorem frameConjugation_apply {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) (B : End n) :
    frameConjugation S B=S.toContinuousLinearMap.comp (B.comp S.symm.toContinuousLinearMap) := rfl

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def smoothCompactDensity (R : ℝ) (f : ℂ → E) (hf : ContDiff ℝ ∞ f)
    (hs : ∀ z, R < ‖z‖ → f z=0) : CompactHolderSpace E R :=
  ⟨compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) f hf
    (density_compact_support R f hs),hs⟩

@[simp] theorem smoothCompactDensity_apply (R : ℝ) (f : ℂ → E) (hf : ContDiff ℝ ∞ f)
    (hs : ∀ z, R < ‖z‖ → f z=0) (z : ℂ) :
    compactHolderValue R (smoothCompactDensity R f hf hs) z=f z := rfl

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function
section
open HigherDimensionalBallPacking.Rigidity
open FramedCR

def affineHolderModuli {n : ℕ} (J : Phase n → End n) (p q : Phase n) (R : ℝ) :
    Set (ℝ × CompactHolderSpace (Phase n) R) :=
  {y | y.1 ∈ Icc (0:ℝ) 1 ∧ ∃ u : ℂ → Phase n,
    AffineLineCurve (lineHomotopy J y.1) p q u ∧
      ∀ z, compactHolderValue R y.2 z=standardCurl u z}

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function








open scoped ContDiff Topology
open Set Filter Function

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
open FramedCR


def densityCurve {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) : Phase n :=
  p+z • (q-p)+markedCRInverse R g z

def densitySlope {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) : Phase n :=
  q-p-(compactCRInverseValue R g 1-compactCRInverseValue R g 0)

@[simp] theorem densityCurve_zero {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) : densityCurve p q R g 0=p := by
  simp [densityCurve]

@[simp] theorem densityCurve_one {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) : densityCurve p q R g 1=q := by
  simp [densityCurve]

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity FramedCR

 def densityAffineSize {n : ℕ} (p : Phase n) (R : ℝ) (g : CompactHolderSpace (Phase n) R) : ℝ :=
  ‖p-compactCRInverseValue R g 0‖+‖compactCRInverseValue R g‖

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity








open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity

 def densityLinearSlope {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) : ℂ →L[ℝ] Phase n :=
  ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Phase n →L[ℝ] Phase n).flip)
    (densitySlope p q R g)

 @[simp] theorem densityLinearSlope_apply {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    densityLinearSlope p q R g z=z • densitySlope p q R g := rfl

 def timeDensityProfile {n : ℕ} (p q : Phase n) (R : ℝ)
    (y : ℝ × CompactHolderSpace (Phase n) R) :
    ((ℝ × Phase n) × (ℂ →L[ℝ] ℝ × Phase n)) × HolderSpace ℂ (ℝ × Phase n) ((1:ℝ)/3) :=
  (((y.1,p-compactCRInverseValue R y.2 0),
      (0 : ℂ →L[ℝ] ℝ).prod (densityLinearSlope p q R y.2)),
    holderLinearPost ((1:ℝ)/3) (ContinuousLinearMap.inr ℝ ℝ (Phase n))
      (c1HolderValue ((1:ℝ)/3) (compactCRInverse R y.2)))

 def densityCoefficient {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) R) : HolderSpace ℂ (End n) ((1:ℝ)/3) :=
  holderAffineFamily ((1:ℝ)/3) (by norm_num) (by norm_num) A hA hc (timeDensityProfile p q R y)

 def densityJet {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) : HolderSpace ℂ (ℂ →L[ℝ] Phase n) ((1:ℝ)/3) :=
  holderConst ((1:ℝ)/3) (densityLinearSlope p q R g)+
    c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)

 def densityResidual {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) R) : HolderSpace ℂ (Phase n) ((1:ℝ)/3) :=
  y.2.1-holderCLM ((1:ℝ)/3) (densityCoefficient p q R A hA hc y)
    (holderJetEval ((1:ℝ)/3) 1 (densityJet p q R y.2))

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function MeasureTheory
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenFrameLocal1
def c1StandardCurl {n : ℕ} : C1HolderSpace (Phase n) ((1:ℝ)/3) →L[ℝ]
      HolderSpace ℂ (Phase n) ((1:ℝ)/3) :=
  (holderJetEval (E := Phase n) ((1:ℝ)/3) Complex.I).comp (c1HolderDeriv ((1:ℝ)/3))-
    (holderMap ((1:ℝ)/3) (standardJ n)).comp
      ((holderJetEval (E := Phase n) ((1:ℝ)/3) 1).comp (c1HolderDeriv ((1:ℝ)/3)))

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance FrozenSurjectiveLocal1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance FrozenSurjectiveLocal2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance FrozenSurjectiveLocal5 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance FrozenSurjectiveLocal6 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local instance holderInverseHGroup (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ V α) := inferInstance

 omit [CompleteSpace E] in
 theorem inverseField_holder (α : ℝ) (hα : 0<α) (A : HolderSpace ℂ (E →L[ℝ] E) α)
    (hi : ∀ z, (holderValue α A z).IsInvertible) (C : ℝ) (hC : 0≤C)
    (hb : ∀ z, ‖(holderValue α A z).inverse‖≤C) (x y : ℂ) :
    ‖(holderValue α A x).inverse-(holderValue α A y).inverse‖≤
      (C*C*‖A‖)*(dist x y)^α := by
  rw [inverseField_sub (hi x) (hi y)]
  calc
    _ ≤ ‖(holderValue α A x).inverse‖*
        (‖holderValue α A y-holderValue α A x‖*‖(holderValue α A y).inverse‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ C*((‖A‖*(dist y x)^α)*C) :=
      mul_le_mul (hb x) (mul_le_mul (holderSpace_estimate α hα A y x) (hb y)
        (norm_nonneg _) (by positivity)) (by positivity) hC
    _ = _ := by rw [dist_comm y x]; ring

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance FrozenOperatorLocal1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance

 def frozenPrincipal {n : ℕ} (R : ℝ) (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0) :
    CompactHolderSpace (Phase n) R →L[ℝ] CompactHolderSpace (Phase n) R :=
  ContinuousLinearMap.id ℝ _-
    (((holderCLM ((1:ℝ)/3) H).comp
      (((holderJetEval ((1:ℝ)/3) 1).comp (c1HolderDeriv ((1:ℝ)/3))).comp (compactCRInverse R))).codRestrict
        (compactHolderSubmodule R) (by
          intro g z hz
          change holderValue ((1:ℝ)/3) H z (holderValue ((1:ℝ)/3)
            (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)) z 1)=0
          rw [hs z hz,zero_apply]))

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenIsomorphismLocal1
local instance FrozenIsomorphismLocal5 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenIsomorphismLocal2
local instance FrozenIsomorphismLocal6 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
local instance responseHolderGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance responseHolderSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance

end HigherDimensionalBallPacking.Rigidity





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end


