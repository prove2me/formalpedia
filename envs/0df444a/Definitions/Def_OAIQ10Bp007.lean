-- Prove2me | Definitions.Def_OAIQ10Bp007
-- name    : OAIQ10Bp007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:42:20.554079+00:00
-- url     : https://prove2.me/theorems/f7da5094-551f-4dbd-a025-38edc1629c05
-- title:
--   Definitions bundle OAIQ10Bp007 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 36 declarations of OpenAI's Lean: 35 definitions and 1 theorem. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal5`, `OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal6`, `OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal7`, `OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal8`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenResponseLocal1`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenResponseLocal2`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenResponseLocal3`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenResponseLocal4`, `OAI.HigherDimensionalBallPacking.Rigidity.ResponseCoords`, `OAI.HigherDimensionalBallPacking.Rigidity.actualDensityGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.actualDensitySpace`, `OAI.HigherDimensionalBallPacking.Rigidity.compactMapCompactGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.compactMapCompactSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.compactMapHGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.compactMapHSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoffFrozen`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoffValues`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResponse`, `OAI.HigherDimensionalBallPacking.Rigidity.frozenResponse`, `OAI.HigherDimensionalBallPacking.Rigidity.goodDensities`, `OAI.HigherDimensionalBallPacking.Rigidity.holderInverse`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupHolderSpaceComplex`, `OAI.HigherDimensionalBallPacking.Rigidity.packingDilation`, `OAI.HigherDimensionalBallPacking.Rigidity.phaseProjection`, `OAI.HigherDimensionalBallPacking.Rigidity.planarDirichlet`, `OAI.HigherDimensionalBallPacking.Rigidity.poleSum`, `OAI.HigherDimensionalBallPacking.Rigidity.radialPrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.regularCGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.regularCSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.regularCompactGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.responseCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.responseCoords`, `OAI.HigherDimensionalBallPacking.Rigidity.responseFactor`, `OAI.HigherDimensionalBallPacking.Rigidity.responseProfile`, `OAI.HigherDimensionalBallPacking.Rigidity.verticalSpeed`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/BallPacking, in whole or in part: [`BallPacking_Necessity_DensityExistence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/DensityExistence.lean), [`BallPacking_Necessity_DensityMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/DensityMaps.lean), [`BallPacking_Necessity_DensityResidual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/DensityResidual.lean), [`BallPacking_Necessity_FrozenInverse`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/FrozenInverse.lean), [`BallPacking_Necessity_FrozenResponse`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/FrozenResponse.lean), [`BallPacking_Necessity_OrbitRegularity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/OrbitRegularity.lean), [`BallPacking_Necessity_PackingNecessity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/PackingNecessity.lean), [`BallPacking_Necessity_PlanarEnergy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/PlanarEnergy.lean), [`BallPacking_Necessity_SquareBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/SquareBounds.lean), [`BallPacking_Rigidity_AngularPoles`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Rigidity/AngularPoles.lean), [`BallPacking_Rigidity_RadialForm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Rigidity/RadialForm.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPackingNecessity`; the bundles `OAIQ10Bp004` and `OAIQ10Bp005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ10Bp009`; the statements `OAI.HigherDimensionalBallPacking.Rigidity.c1_frozen_response`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoffFrozen_invertible`, `OAI.HigherDimensionalBallPacking.Rigidity.densityFixedPoint_residual_zero`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_contDiffAt`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_locallyPrecompact`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_zero_time`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitResponseDensity_contDiffAt`, `OAI.HigherDimensionalBallPacking.Rigidity.responseCoefficient_invertible` and `OAI.HigherDimensionalBallPacking.Rigidity.responseFactor_contDiffAt`; the proofs of `OAI.HigherDimensionalBallPacking.Rigidity.c1_frozen_response`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoffFrozen_invertible`, `OAI.HigherDimensionalBallPacking.Rigidity.densityFixedPoint_residual_zero`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_zero_time`, `OAI.HigherDimensionalBallPacking.Rigidity.framed_density_equation`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_error_energy`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitResponseDensity_contDiffAt`, `OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction`, `OAI.HigherDimensionalBallPacking.Rigidity.responseCoefficient_invertible`, `OAI.HigherDimensionalBallPacking.Rigidity.responseFactor_contDiffAt` and `OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/BallPacking at commit adc7f12

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp004
import Definitions.Def_OAIQ10Bp005

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

def radialPrimitive {n : ℕ} (σ τ : ℝ) (x : Phase n) : Phase n [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (Phase n) ℝ 0 (radialPrimitiveCLM σ τ x)

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

def poleSum (P : Finset Plane) (c : Plane → ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  ∑ p ∈ P, c p • angularPole p z


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane)



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

def planarDirichlet {n : ℕ} (v : Plane → Phase n) (z : Plane) : ℝ :=
  stdDot n (fderiv ℝ v z (1,0)) (fderiv ℝ v z (1,0)) +
  stdDot n (fderiv ℝ v z (0,1)) (fderiv ℝ v z (0,1))

def verticalSpeed {n : ℕ} (v : Plane → Phase n) (x y : ℝ) : ℝ :=
  euclideanNorm (fderiv ℝ v (x,y) (0,1))

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_SquareBounds
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








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

def phaseProjection {n : ℕ} (a : Phase n) : Phase n →L[ℝ] ℝ :=
  (euclideanNorm a)⁻¹ • stdDot n a

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
local instance instNormedAddCommGroupHolderSpaceComplex (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance

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

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.holderInverseHGroup
def holderInverse (α : ℝ) (hα : 0<α) (R : ℝ) (A : HolderSpace ℂ (E →L[ℝ] E) α)
    (hi : ∀ z, (holderValue α A z).IsInvertible)
    (hout : ∀ z, R<‖z‖ → holderValue α A z=ContinuousLinearMap.id ℝ E) :
    HolderSpace ℂ (E →L[ℝ] E) α := by
  let ex := inverseField_bound R (holderValue α A).continuous hi hout
  let C := Classical.choose ex
  have hC := (Classical.choose_spec ex).1
  have hb := (Classical.choose_spec ex).2
  let f : ℂ →ᵇ (E →L[ℝ] E) := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => (holderValue α A z).inverse) (inverseField_continuous (holderValue α A).continuous hi) C hb
  exact holderSpaceMk α f (C*C*‖A‖) (by positivity) (inverseField_holder α hα A hi C hC.le hb)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

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

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseHolderGroup
local instance FrozenResponseLocal1 : NormedAddCommGroup (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseHolderSpace
local instance FrozenResponseLocal2 : NormedSpace ℝ (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance FrozenResponseLocal3 : NormedAddCommGroup (HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) := inferInstance
local instance FrozenResponseLocal4 : NormedSpace ℝ (HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) := inferInstance

 def cutoffFrozen (b : ContDiffBump (0:ℂ))
    (H : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) :
    CompactHolderSpace E b.rOut →L[ℝ] CompactHolderSpace E b.rOut :=
  ContinuousLinearMap.id ℝ _-(cutoffCompact b).comp ((holderCLM ((1:ℝ)/3) H).comp
    ((holderJetEval ((1:ℝ)/3) 1).comp ((c1HolderDeriv ((1:ℝ)/3)).comp (compactCRInverse b.rOut))))

 def frozenResponse (b : ContDiffBump (0:ℂ))
    (p : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3) × E) : CompactHolderSpace E b.rOut :=
  (cutoffFrozen b p.1).inverse (cutoffCompact b (holderCLM ((1:ℝ)/3) p.1 (holderConstantCLM ((1:ℝ)/3) p.2)))

end HigherDimensionalBallPacking.Rigidity





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_OrbitRegularity
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





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularHGroup
local instance regularCGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace E α) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularHSpace
local instance regularCSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance regularCompactGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance AffineC1RegularityLocal5 (n : ℕ) : NormedAddCommGroup (C1HolderSpace (Phase n) ((1:ℝ)/3)) := inferInstance
local instance AffineC1RegularityLocal6 (n : ℕ) : NormedSpace ℝ (C1HolderSpace (Phase n) ((1:ℝ)/3)) := inferInstance
local instance AffineC1RegularityLocal7 (n : ℕ) (R : ℝ) : NormedAddCommGroup (CompactHolderSpace (Phase n) R) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularCompactSpace
local instance AffineC1RegularityLocal8 (n : ℕ) (R : ℝ) : NormedSpace ℝ (CompactHolderSpace (Phase n) R) := inferInstance

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityMaps
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
open HigherDimensionalBallPacking.Rigidity

 def goodDensities {n : ℕ} (p q : Phase n) (R m M : ℝ) : Set (CompactHolderSpace (Phase n) R) :=
  {g | m < ‖densitySlope p q R g‖ ∧ densityAffineSize p R g < M}

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance compactMapHGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance compactMapHSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance compactMapCompactGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance compactMapCompactSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 def cutoffValues {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : ContDiffBump (0:ℂ)) : C1HolderSpace E ((1:ℝ)/3) →L[ℝ] HolderSpace ℂ E ((1:ℝ)/3) :=
  c1LowerOrderCLM (holderLinearPost ((1:ℝ)/3) (ContinuousLinearMap.lsmul ℝ ℝ)
    (holderSourceCutoff ((1:ℝ)/3) (by norm_num) (by norm_num) b))

 abbrev ResponseCoords (n : ℕ) := (ℝ × Phase n × Phase n) × HolderSpace ℂ (Phase n) ((1:ℝ)/3)

 def responseCoords {n : ℕ} (B : ContDiffBump (0:ℂ)) (p q : Phase n) (R : ℝ)
    (y : ℝ × CompactHolderSpace (Phase n) R) : ResponseCoords n :=
  ((y.1,p-compactCRInverseValue R y.2 0,densitySlope p q R y.2),cutoffValues B (compactCRInverse R y.2))

 def responseProfile {n : ℕ} (B : ContDiffBump (0:ℂ)) (x : ResponseCoords n) :
    HolderSpace ℂ (ℝ × Phase n) ((1:ℝ)/3) :=
  holderConstantCLM ((1:ℝ)/3) (x.1.1,0)+holderLinearPost ((1:ℝ)/3) (ContinuousLinearMap.inr ℝ ℝ (Phase n))
    (holderCutoffAffine ((1:ℝ)/3) (by norm_num) (by norm_num) B (x.1.2.1,affineSlope x.1.2.2)+x.2)

 def responseCoefficient {n : ℕ} (b B : ContDiffBump (0:ℂ))
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (x : ResponseCoords n) : HolderSpace ℂ (End n) ((1:ℝ)/3) :=
  (cutoffCompact b (holderPost ((1:ℝ)/3) (by norm_num) A hA hc (responseProfile B x))).1

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityExistence
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
open HigherDimensionalBallPacking.Rigidity TwoPointContinuation

 def responseFactor {n : ℕ} (b B : ContDiffBump (0:ℂ))
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (x : ResponseCoords n) : CompactHolderSpace (Phase n) b.rOut :=
  frozenResponse b (responseCoefficient b B A hA hc x,x.1.2.2)

 def densityResponse {n : ℕ} (b B : ContDiffBump (0:ℂ)) (p q : Phase n)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut) : CompactHolderSpace (Phase n) b.rOut :=
  responseFactor b B A hA hc (responseCoords B p q b.rOut y)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function







open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity TwoPointContinuation
local instance actualDensityGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance actualDensitySpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_PackingNecessity
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
open Set Function Filter
namespace HigherDimensionalBallPacking







open scoped ENNReal NNReal Topology ContDiff Pointwise
open Set MeasureTheory








open scoped ContDiff Topology
open Set Function
section
namespace Rigidity

def packingDilation (n : ℕ) (c : ℝ) (hc : c≠0) : Phase n ≃L[ℝ] Phase n :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Phase n) (Units.mk0 c hc)

@[simp] theorem packingDilation_apply (n : ℕ) (c : ℝ) (hc : c≠0) (x : Phase n) :
    packingDilation n c hc x=c • x := rfl

end Rigidity
open Rigidity

end

 

 

 

open scoped ContDiff Topology
open Set Function
open Rigidity

end HigherDimensionalBallPacking

end

end OAI
end


