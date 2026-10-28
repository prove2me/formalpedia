-- Prove2me | Definitions.Def_OAIQ10Bp006
-- name    : OAIQ10Bp006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:30:24.766615+00:00
-- url     : https://prove2.me/theorems/3c21af0d-28e1-415b-9a42-fa17a8a8704b
-- title:
--   Definitions bundle OAIQ10Bp006 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 27 definitions. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.localChartsInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.localChartsInst12`, `OAI.HigherDimensionalBallPacking.Rigidity.normalizedHolderFrame`, `OAI.HigherDimensionalBallPacking.Rigidity.packageC1Norm`, `OAI.HigherDimensionalBallPacking.Rigidity.packageC1Space`, `OAI.HigherDimensionalBallPacking.Rigidity.packageCompactNorm`, `OAI.HigherDimensionalBallPacking.Rigidity.packageCompactSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.planeSquare`, `OAI.HigherDimensionalBallPacking.Rigidity.rectangleMean`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst11`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst12`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst13`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst14`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst15`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst16`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.squareMean`, `OAI.HigherDimensionalBallPacking.Rigidity.weightedTwoForm`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/BallPacking, in whole or in part: [`BallPacking_Necessity_FramedCompactness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/FramedCompactness.lean), [`BallPacking_Necessity_FrozenInverse`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/FrozenInverse.lean), [`BallPacking_Necessity_LocalCharts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/LocalCharts.lean), [`BallPacking_Necessity_SchauderBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/SchauderBounds.lean), [`BallPacking_Necessity_SquareBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/SquareBounds.lean), [`BallPacking_Rigidity_CurveArea`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Rigidity/CurveArea.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPackingNecessity`; the bundle `OAIQ10Bp002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ10Bp009`; the proofs of `OAI.HigherDimensionalBallPacking.Rigidity.affineHolderModuli_isCompact`, `OAI.HigherDimensionalBallPacking.Rigidity.c1_decaying_CR_zero`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_curve_compactness`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_error_energy`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitCoefficient_support` and `OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/BallPacking at commit adc7f12

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp002

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
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
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
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance schauderBoundsInst1 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst2 (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst3 (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance schauderBoundsInst4 (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance schauderBoundsInst5 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst6 (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst7 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ F α) := inferInstance
local instance schauderBoundsInst8 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ F α) := inferInstance
local instance schauderBoundsInst9 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace F R) := inferInstance
local instance schauderBoundsInst10 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace F R) := inferInstance

end

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance schauderBoundsInst11 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst12 (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst13 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ F α) := inferInstance
local instance schauderBoundsInst14 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ F α) := inferInstance
local instance schauderBoundsInst15 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace F R) := inferInstance
local instance schauderBoundsInst16 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace F R) := inferInstance

end

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FramedCompactness
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
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
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

open scoped ContDiff Topology
open Set Filter Function

namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance packageC1Norm (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance packageC1Space (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance packageCompactNorm (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace F R) := inferInstance
local instance packageCompactSpace (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace F R) := inferInstance

end

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_LocalCharts
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
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
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

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
local instance localChartsInst10 (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance localChartsInst12 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance

end HigherDimensionalBallPacking.Rigidity

 

open scoped ContDiff Topology
open Set Filter Function

open scoped ContDiff Topology
open Set Filter Function

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

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

def weightedTwoForm {n : ℕ} (g dg : ℝ) (x v w : Phase n) : ℝ :=
  g * standardForm v w + Real.pi * dg *
    (stdDot n x v * standardForm x w - stdDot n x w * standardForm x v)



open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



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
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
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

 def normalizedHolderFrame {n : ℕ} (K : C1HolderSpace (End n) ((1:ℝ)/3)) :
    C1HolderSpace (End n) ((1:ℝ)/3) :=
  c1HolderConstantCLM ((1:ℝ)/3) ((1/2:ℝ) • ContinuousLinearMap.id ℝ (Phase n))-
    c1HolderMap ((1:ℝ)/3)
      ((1/2:ℝ) • (ContinuousLinearMap.compL ℝ (Phase n) (Phase n) (Phase n)).flip (standardJ n)) K

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

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
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
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

def planeSquare (c : Plane) (r : ℝ) : Set Plane :=
  Icc (c.1-r,c.2-r) (c.1+r,c.2+r)








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

def rectangleMean (f : Plane → ℝ) (a b : Plane) : ℝ :=
  lineMean (fun y => lineMean (fun x => f (x,y)) a.1 b.1) a.2 b.2

def squareMean (f : Plane → ℝ) (c : Plane) (r : ℝ) : ℝ :=
  rectangleMean f (c.1-r,c.2-r) (c.1+r,c.2+r)








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


