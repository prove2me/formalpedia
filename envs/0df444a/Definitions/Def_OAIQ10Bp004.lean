-- Prove2me | Definitions.Def_OAIQ10Bp004
-- name    : OAIQ10Bp004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:29:57.367613+00:00
-- url     : https://prove2.me/theorems/d81a4979-fcc1-4098-bfbb-11f2d3ade6b5
-- title:
--   Definitions bundle OAIQ10Bp004 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 12 definitions and 5 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal1`, `OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal2`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderShift`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoffCompact`, `OAI.HigherDimensionalBallPacking.Rigidity.diagonalShift`, `OAI.HigherDimensionalBallPacking.Rigidity.hdiffHolderGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.hdiffHolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.holderShift`, `OAI.HigherDimensionalBallPacking.Rigidity.holderTranspose`, `OAI.HigherDimensionalBallPacking.Rigidity.regularCompactSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.regularHGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.regularHSpace`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/BallPacking, in whole or in part: [`BallPacking_Necessity_FrozenResponse`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/FrozenResponse.lean), [`BallPacking_Necessity_OrbitRegularity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/OrbitRegularity.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPackingNecessity`; the bundle `OAIQ10Bp002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ10Bp007`; the statements `OAI.HigherDimensionalBallPacking.Rigidity.c1_shift_value_continuous`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoff_curl_reconstruct` and `OAI.HigherDimensionalBallPacking.Rigidity.holder_shift_value_hasFDerivAt`; the proofs of `OAI.HigherDimensionalBallPacking.Rigidity.cutoff_curl_reconstruct`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResidual_zero_affineLine` and `OAI.HigherDimensionalBallPacking.Rigidity.holder_shift_value_hasFDerivAt`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/BallPacking at commit adc7f12

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp002

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
namespace HigherDimensionalBallPacking.Rigidity

 def cutoffCompact {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : ContDiffBump (0:ℂ)) : HolderSpace ℂ E ((1:ℝ)/3) →L[ℝ] CompactHolderSpace E b.rOut :=
  (holderCLM ((1:ℝ)/3) (holderLinearPost ((1:ℝ)/3) (ContinuousLinearMap.lsmul ℝ ℝ)
    (holderSourceCutoff ((1:ℝ)/3) (by norm_num) (by norm_num) b))).codRestrict (compactHolderSubmodule b.rOut) (by
      intro g z hz
      change b z • holderValue ((1:ℝ)/3) g z=0
      rw [b.zero_of_le_dist (by simpa using hz.le),zero_smul])

 @[simp] theorem cutoffCompact_value {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : ContDiffBump (0:ℂ)) (g : HolderSpace ℂ E ((1:ℝ)/3)) (z : ℂ) :
    compactHolderValue b.rOut (cutoffCompact b g) z=b z • holderValue ((1:ℝ)/3) g z := rfl

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
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 def diagonalShift (h : ℂ) : C(OffDiagonal ℂ,OffDiagonal ℂ) :=
  ⟨fun p => ⟨(p.val.1+h,p.val.2+h),fun he => p.property (add_right_cancel he)⟩,
    Continuous.subtype_mk (((continuous_fst.comp continuous_subtype_val).add continuous_const).prodMk
      ((continuous_snd.comp continuous_subtype_val).add continuous_const)) _⟩

 def holderShift (α : ℝ) (h : ℂ) : HolderSpace ℂ E α →L[ℝ] HolderSpace ℂ E α :=
  ((((BoundedContinuousFunction.compContinuousCLM E ℝ ⟨fun z => z+h,continuous_id.add continuous_const⟩).comp
      (holderValue α)).prod
    ((BoundedContinuousFunction.compContinuousCLM E ℝ (diagonalShift h)).comp
      (holderDifference α))).codRestrict (holderGraph ℂ E α) (by
        intro f p
        change holderValue α f (p.val.1+h)-holderValue α f (p.val.2+h)=
          (dist p.val.1 p.val.2)^α • holderDifference α f (diagonalShift h p)
        have hh := f.property (diagonalShift h p)
        change holderValue α f (p.val.1+h)-holderValue α f (p.val.2+h)=
          (dist (p.val.1+h) (p.val.2+h))^α • holderDifference α f (diagonalShift h p) at hh
        simpa only [dist_add_right] using hh))

 omit [CompleteSpace E] in
 @[simp] theorem holderShift_value (α : ℝ) (h : ℂ) (f : HolderSpace ℂ E α) (z : ℂ) :
    holderValue α (holderShift α h f) z=holderValue α f (z+h) := rfl

 def c1HolderShift (α : ℝ) (h : ℂ) : C1HolderSpace E α →L[ℝ] C1HolderSpace E α :=
  (((holderShift α h).comp (c1HolderValue α)).prod
    ((holderShift α h).comp (c1HolderDeriv α))).codRestrict (c1HolderGraph α) (by
      intro f
      apply c1HolderGraph_mem_of_hasFDerivAt
      intro z
      exact (c1Holder_hasFDerivAt α f (z+h)).comp z ((hasFDerivAt_id z).add_const h))

 @[simp] theorem c1HolderShift_value (α : ℝ) (h : ℂ) (f : C1HolderSpace E α) (z : ℂ) :
    holderValue α (c1HolderValue α (c1HolderShift α h f)) z=
      holderValue α (c1HolderValue α f) (z+h) := rfl

 @[simp] theorem c1HolderShift_Deriv (α : ℝ) (h : ℂ) (f : C1HolderSpace E α) :
    c1HolderDeriv α (c1HolderShift α h f)=holderShift α h (c1HolderDeriv α f) := rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
local instance hdiffHolderGroup (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ V α) := inferInstance
local instance hdiffHolderSpace (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ V α) := inferInstance

 def holderTranspose (α : ℝ) : HolderSpace ℂ (X →L[ℝ] E) α →L[ℝ] (X →L[ℝ] HolderSpace ℂ E α) :=
  (ContinuousLinearMap.compL ℝ X (HolderSpace ℂ X α) (HolderSpace ℂ E α)).flip
    (holderConstantCLM α) |>.comp (holderOperatorCLM α)

 omit [CompleteSpace E] in
 @[simp] theorem holderTranspose_value (α : ℝ) (D : HolderSpace ℂ (X →L[ℝ] E) α) (v : X) (z : ℂ) :
    holderValue α (holderTranspose α D v) z=holderValue α D z v := rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance regularHGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance regularHSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance regularCompactSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

local instance AffineC1RegularityLocal1 (n : ℕ) : NormedAddCommGroup (HolderSpace ℂ (Phase n) ((1:ℝ)/3)) := inferInstance
local instance AffineC1RegularityLocal2 (n : ℕ) : NormedSpace ℝ (HolderSpace ℂ (Phase n) ((1:ℝ)/3)) := inferInstance

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end


