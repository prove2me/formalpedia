-- Prove2me | Definitions.Def_OAIQ10Bp008
-- name    : OAIQ10Bp008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:38:24.839901+00:00
-- url     : https://prove2.me/theorems/cea970cc-8a9e-4a2e-9571-434e04674f01
-- title:
--   Definitions bundle OAIQ10Bp008 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 19 definitions. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.htransHolderGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealCompactHolderSpace_2`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealHolderSpaceComplex`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitC1Group`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitC1Space`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitHGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitHSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitHolderGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitHolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.responseCompactGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.responseCompactSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.responseLocalCompactGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.responseLocalCompactSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.responseLocalGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.responseLocalSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.standardCurvePrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.symplecticBilin`, `OAI.HigherDimensionalBallPacking.Rigidity.translatedPlanarPrimitive`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/BallPacking, in whole or in part: [`BallPacking_Necessity_AffineEnergy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/AffineEnergy.lean), [`BallPacking_Necessity_DensityExistence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/DensityExistence.lean), [`BallPacking_Necessity_DensityResidual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/DensityResidual.lean), [`BallPacking_Necessity_FrozenResponse`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/FrozenResponse.lean), [`BallPacking_Necessity_OrbitRegularity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/OrbitRegularity.lean), [`BallPacking_Necessity_PackingNecessity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/PackingNecessity.lean), [`BallPacking_Necessity_PlanarEnergy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/PlanarEnergy.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPackingNecessity`; the bundles `OAIQ10Bp000`, `OAIQ10Bp002` and `OAIQ10Bp005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ10Bp009`; the statements `OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_contDiff`, `OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_regular`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_contDiffAt`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitCoefficient_support`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitResponseDensity_contDiffAt` and `OAI.HigherDimensionalBallPacking.Rigidity.responseFactor_contDiffAt`; the proofs of `OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_contDiff`, `OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_regular`, `OAI.HigherDimensionalBallPacking.Rigidity.c1_shift_value_continuous`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_error_energy`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitCoefficient_support`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitResponseDensity_contDiffAt`, `OAI.HigherDimensionalBallPacking.Rigidity.responseFactor_contDiffAt` and `OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/BallPacking at commit adc7f12

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp000
import Definitions.Def_OAIQ10Bp002
import Definitions.Def_OAIQ10Bp005

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

def standardCurvePrimitive {n : ℕ} (u : ℂ → Phase n) : Plane → Plane →L[ℝ] ℝ :=
  planarPullback (realCurve u) stdPrimitive

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

def translatedPlanarPrimitive {n : ℕ} (v : Plane → Phase n) (c : Phase n) :
    Plane → Plane →L[ℝ] ℝ := planarPullback (fun z => v z-c) stdPrimitive

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
local instance instNormedSpaceRealHolderSpaceComplex (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance instNormedSpaceRealCompactHolderSpace_2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
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
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseHolderGroup
local instance responseCompactGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseHolderSpace
local instance responseCompactSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

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
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance htransHolderGroup (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ V α) := inferInstance

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance orbitHolderGroup (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ V α) := inferInstance
local instance orbitHolderSpace (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ V α) := inferInstance
local instance orbitC1Group (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace V α) := inferInstance
local instance orbitC1Space (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace V α) := inferInstance

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance orbitHGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance orbitHSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance

 def orbitCoefficient {n : ℕ} (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3)) : HolderSpace ℂ (End n) ((1:ℝ)/3) :=
  holderAffineFamily ((1:ℝ)/3) (by norm_num) (by norm_num) f hf hc ((c+p.1 • a,affineSlope a),p.2)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

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
local instance responseLocalGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance responseLocalSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance responseLocalCompactGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance responseLocalCompactSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function







open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

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
namespace Rigidity

def symplecticBilin (n : ℕ) : LinearMap.BilinForm ℝ (Phase n) where
  toFun u :=
    { toFun := standardForm u
      map_add' := by
        intro v w
        simp only [standardForm, Pi.add_apply, Complex.add_re, Complex.add_im]
        simp only [mul_add, ← Finset.sum_add_distrib]
        congr 1
        funext i
        ring
      map_smul' := by
        intro c v
        simp [standardForm, Finset.mul_sum, mul_sub, mul_left_comm] }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    change standardForm (u + v) w = standardForm u w + standardForm v w
    simp only [standardForm, Pi.add_apply, Complex.add_re, Complex.add_im]
    simp only [add_mul, ← Finset.sum_add_distrib]
    congr 1
    funext i
    ring
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    change standardForm (c • u) v = c * standardForm u v
    simp [standardForm, Finset.mul_sum, mul_sub, mul_assoc]

end Rigidity








open scoped ContDiff Topology
open Set Function







open scoped ContDiff Topology
open Set Function
open Rigidity

end HigherDimensionalBallPacking

end

end OAI
end


