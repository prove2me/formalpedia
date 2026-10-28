-- Prove2me | Definitions.Def_OAIQ10Bp009
-- name    : OAIQ10Bp009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:44:38.542398+00:00
-- url     : https://prove2.me/theorems/a5c3842d-eefe-43b7-87e6-a9ea549a048e
-- title:
--   Definitions bundle OAIQ10Bp009 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 6 definitions and 1 theorem. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupCompactHolderSpace_2`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitResponse`, `OAI.HigherDimensionalBallPacking.Rigidity.principalFrameLower`, `OAI.HigherDimensionalBallPacking.Rigidity.rectangleBoundaryEnergy`, `OAI.HigherDimensionalBallPacking.Rigidity.rectangleBoundaryLength`, `OAI.HigherDimensionalBallPacking.Rigidity.squareEnergy`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/BallPacking, in whole or in part: [`BallPacking_Necessity_DensityResidual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/DensityResidual.lean), [`BallPacking_Necessity_FrozenInverse`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/FrozenInverse.lean), [`BallPacking_Necessity_OrbitRegularity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/OrbitRegularity.lean), [`BallPacking_Necessity_PackingNecessity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/PackingNecessity.lean), [`BallPacking_Necessity_PlanarEnergy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/PlanarEnergy.lean), [`BallPacking_Necessity_SquareBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/SquareBounds.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPackingNecessity`; the bundles `OAIQ10Bp006`, `OAIQ10Bp007` and `OAIQ10Bp008` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.HigherDimensionalBallPacking.Rigidity.orbitResponse_identity`, `OAI.HigherDimensionalBallPacking.Rigidity.principalFrameLower_equation` and `OAI.HigherDimensionalBallPacking.Rigidity.principalFrameLower_support`; the proofs of `OAI.HigherDimensionalBallPacking.Rigidity.affine_c1_regular`, `OAI.HigherDimensionalBallPacking.Rigidity.compatible_frozen_solution`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_contDiffAt`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_locallyPrecompact`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_C0_compactness`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_common_affine_carrier`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_density_common_support`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_limit_has_nonzero_asymptotic`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_slopes_bounded_above`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitResponse_identity`, `OAI.HigherDimensionalBallPacking.Rigidity.principalFrameLower_equation`, `OAI.HigherDimensionalBallPacking.Rigidity.principalFrameLower_support` and `OAI.HigherDimensionalBallPacking.packing_necessity`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/BallPacking at commit adc7f12

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp006
import Definitions.Def_OAIQ10Bp007
import Definitions.Def_OAIQ10Bp008

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

def rectangleBoundaryLength {n : ℕ} (v : Plane → Phase n) (a b : Plane) : ℝ :=
  (∫ x in a.1..b.1, horizontalSpeed v a.2 x) +
  (∫ x in a.1..b.1, horizontalSpeed v b.2 x) +
  (∫ y in a.2..b.2, verticalSpeed v a.1 y) +
  (∫ y in a.2..b.2, verticalSpeed v b.1 y)

def rectangleBoundaryEnergy {n : ℕ} (v : Plane → Phase n) (a b : Plane) : ℝ :=
  (∫ x in a.1..b.1, planarDirichlet v (x,a.2)) +
  (∫ x in a.1..b.1, planarDirichlet v (x,b.2)) +
  (∫ y in a.2..b.2, planarDirichlet v (a.1,y)) +
  (∫ y in a.2..b.2, planarDirichlet v (b.1,y))

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

def squareEnergy {n : ℕ} (v : Plane → Phase n) (c : Plane) (r : ℝ) : ℝ :=
  ∫ z in planeSquare c r, planarDirichlet v z








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
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupHolderSpaceComplex
local instance instNormedAddCommGroupCompactHolderSpace_2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance

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





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 def principalFrameLower {n : ℕ} (R : ℝ) (K : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (A : C1HolderSpace (End n) ((1:ℝ)/3))
    (hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible)
    (hout : ∀ z, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ (Phase n)) :
    HolderSpace ℂ (End n) ((1:ℝ)/3) :=
  holderComp (holderInverse ((1:ℝ)/3) (by norm_num) R (c1HolderValue ((1:ℝ)/3) A) hi hout)
    ((holderJetEval ((1:ℝ)/3) Complex.I (c1HolderDeriv ((1:ℝ)/3) A))-
      holderComp K (holderJetEval ((1:ℝ)/3) 1 (c1HolderDeriv ((1:ℝ)/3) A)))

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

 def orbitResponse {n : ℕ} (b : ContDiffBump (0:ℂ))
    (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (c a : Phase n)
    (p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3)) : C1HolderSpace (Phase n) ((1:ℝ)/3) :=
  compactCRInverse b.rOut (frozenResponse b (orbitCoefficient f hf hc c a p,a))

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

@[simp] theorem packingDilation_symm_apply (n : ℕ) (c : ℝ) (hc : c≠0) (x : Phase n) :
    (packingDilation n c hc).symm x=c⁻¹ • x := rfl

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


