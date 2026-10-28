-- Prove2me | Definitions.Def_OAIQ10Bp003
-- name    : OAIQ10Bp003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:25:31.42273+00:00
-- url     : https://prove2.me/theorems/cbf1b551-e589-4953-a59f-e63dd36ef312
-- title:
--   Definitions bundle OAIQ10Bp003 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 24 definitions and 1 theorem. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.cayleyOperator`, `OAI.HigherDimensionalBallPacking.Rigidity.centeredFrame`, `OAI.HigherDimensionalBallPacking.Rigidity.frozenCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.holderCalculusNormedSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.holderLipschitzSet`, `OAI.HigherDimensionalBallPacking.Rigidity.holderPostDifference`, `OAI.HigherDimensionalBallPacking.Rigidity.imageJ`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupC1HolderSpaceHDivRealOfNat_1`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupHolderSpaceComplexContinuousLinearMapRealIdHDivOfNat`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupHolderSpaceComplexHDivRealOfNat_1`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupHolderSpaceComplexHDivRealOfNat_2`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupHolderSpace_3`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealC1HolderSpaceHDivOfNat_1`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealHolderSpaceComplexHDivOfNat_1`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealHolderSpaceComplexHDivOfNat_2`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealHolderSpace_3`, `OAI.HigherDimensionalBallPacking.Rigidity.interpolateJ`, `OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy`, `OAI.HigherDimensionalBallPacking.Rigidity.localizeJ`, `OAI.HigherDimensionalBallPacking.Rigidity.morreyConstant`, `OAI.HigherDimensionalBallPacking.Rigidity.planarPullback`, `OAI.HigherDimensionalBallPacking.Rigidity.radialForm`, `OAI.SymplecticBallPacking.Hamiltonian.angularOneForm`, `OAI.SymplecticBallPacking.Hamiltonian.cutoffWedge`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/BallPacking, in whole or in part: [`BallPacking_Necessity_FrameFredholm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/FrameFredholm.lean), [`BallPacking_Necessity_FreezeJ`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/FreezeJ.lean), [`BallPacking_Necessity_HolderCalculus`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/HolderCalculus.lean), [`BallPacking_Necessity_HolderCompactness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/HolderCompactness.lean), [`BallPacking_Necessity_NonlinearCR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/NonlinearCR.lean), [`BallPacking_Necessity_SquareBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/SquareBounds.lean), [`BallPacking_Rigidity_Adapted`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Rigidity/Adapted.lean), [`BallPacking_Rigidity_CompatibleStructures`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Rigidity/CompatibleStructures.lean), [`BallPacking_Rigidity_CurveArea`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Rigidity/CurveArea.lean), [`BallPacking_Rigidity_PlanarResidueCutoff`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Rigidity/PlanarResidueCutoff.lean), [`BallPacking_Rigidity_RadialForm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Rigidity/RadialForm.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPackingNecessity`; the bundles `OAIQ10Bp000` and `OAIQ10Bp001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ10Bp005`; the statements `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_C0_compactness`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_curve_compactness`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_coefficient_extension`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_common_affine_carrier`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_density_common_support`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_limit_has_nonzero_asymptotic` and `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_slopes_bounded_above`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/BallPacking at commit adc7f12

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp000
import Definitions.Def_OAIQ10Bp001

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CompatibleStructures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

noncomputable section
open scoped Topology
open Set Function Filter

namespace Rigidity

def imageJ {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n) (y : Phase n) : End n :=
  let D := fderiv ℝ f (invFunOn f U y)
  D.comp ((standardJ n).comp D.inverse)

end Rigidity
end
end HigherDimensionalBallPacking

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

def cayleyOperator {n : ℕ} (J : End n) (a b : ℝ) : End n :=
  (cayleyP J a b).comp (cayleyP J b a).inverse

def interpolateJ {n : ℕ} (J : End n) (t : ℝ) : End n :=
  (standardJ n).comp (cayleyOperator J (1 + t) (1 - t))

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Adapted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology Manifold
open Set Function Filter


def localizeJ {n : ℕ} (V : Set (Phase n)) (J : Phase n → End n)
    (χ : Phase n → ℝ) (x : Phase n) : End n := by
  classical
  exact if x ∈ V then interpolateJ (J x) (χ x) else standardJ n


end

section
open scoped ContDiff Topology
open Set Function Filter

def lineHomotopy {n : ℕ} (J : Phase n → End n) (t : ℝ) (x : Phase n) : End n :=
  interpolateJ (J x) t


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

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

def radialForm {n : ℕ} (σ τ : ℝ) (x v w : Phase n) : ℝ :=
  radialCoefficient σ τ (capacity x) * standardForm v w +
    Real.pi * radialSlope σ τ (capacity x) *
      (stdDot n x v * standardForm x w - stdDot n x w * standardForm x v)

end HigherDimensionalBallPacking.Rigidity

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

@[simp] theorem radiusSq_polar (R t : ℝ) : radiusSq (polarCoord.symm (R,t)) = R^2 := by
  simp only [radiusSq,polarCoord_symm_apply]
  linear_combination R^2 * Real.cos_sq_add_sin_sq t

def angularOneForm (z : Plane) : Plane →L[ℝ] ℝ := (radiusSq z)⁻¹ • planarArea z

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCompactness
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.c1HolderGraph_isClosed _root_.OAI.HigherDimensionalBallPacking.Rigidity.c1HolderSpace_complete _root_.OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSpace_complete _root_.OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSubmodule_isClosed
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

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



def holderLipschitzSet (R M : ℝ) (L : NNReal) : Set (HolderSpace ℂ E ((1:ℝ)/3)) :=
  {u | (∀ x : ℂ, R < ‖x‖ → holderValue ((1:ℝ)/3) u x=0) ∧
    ‖holderValue ((1:ℝ)/3) u‖ ≤ M ∧ LipschitzWith L (holderValue ((1:ℝ)/3) u)}

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrameFredholm
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

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
section
universe v
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance instNormedAddCommGroupHolderSpaceComplexHDivRealOfNat_1 : NormedAddCommGroup (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance instNormedSpaceRealHolderSpaceComplexHDivOfNat_1 : NormedSpace ℝ (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance instNormedAddCommGroupHolderSpaceComplexContinuousLinearMapRealIdHDivOfNat : NormedAddCommGroup (HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3)) := inferInstance
local instance instNormedAddCommGroupC1HolderSpaceHDivRealOfNat_1 : NormedAddCommGroup (C1HolderSpace E ((1:ℝ)/3)) := inferInstance
local instance instNormedSpaceRealHolderSpaceComplexContinuousLinearMapIdHDivOfNat_r6d2cc8_1 : NormedSpace ℝ (HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3)) := inferInstance
local instance instNormedSpaceRealC1HolderSpaceHDivOfNat_1 : NormedSpace ℝ (C1HolderSpace E ((1:ℝ)/3)) := inferInstance
local instance instNormedAddCommGroupHolderSpaceComplexHDivRealOfNat_2 : NormedAddCommGroup (HolderSpace ℂ F ((1:ℝ)/3)) := inferInstance
local instance instNormedSpaceRealHolderSpaceComplexHDivOfNat_2 : NormedSpace ℝ (HolderSpace ℂ F ((1:ℝ)/3)) := inferInstance

end

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter





open Set Function Filter Topology

 

 

open Set Function Filter Topology
open scoped NNReal

 

 

open scoped NNReal
open Set Function Filter Topology

 

 

open Set Function Filter Topology

 

 

open Set Function Filter Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped ContDiff Topology
open Set Function Filter

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FreezeJ
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

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity

def centeredFrame {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) (p : Phase n)
    (u : ℂ → Phase n) : ℂ → Phase n := fun z => S (u z-p)

def frozenCoefficient {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) (J : End n)
    (B : ℂ → End n) : ℂ → End n := fun z =>
      S.toContinuousLinearMap.comp ((B z-J).comp S.symm.toContinuousLinearMap)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCalculus
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

open scoped ContDiff Topology
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

namespace HigherDimensionalBallPacking.Rigidity
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance holderCalculusNormedSpace
    (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedSpace ℝ (HolderSpace K G α) := inferInstance



variable [CompleteSpace F]

def holderPostDifference (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) : OffDiagonal K →ᵇ F :=
  sectionMeanCLM (sectionCLM
    (superposeBCF (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      0 (segmentSection (holderValue α u))) (differencePull (holderDifference α u)))

end HigherDimensionalBallPacking.Rigidity

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
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local instance instNormedAddCommGroupHolderSpace_3 (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedAddCommGroup (HolderSpace K G α) := inferInstance
local instance instNormedSpaceRealHolderSpace_3 (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedSpace ℝ (HolderSpace K G α) := inferInstance

end HigherDimensionalBallPacking.Rigidity



end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_PlanarResidueCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SymplecticBallPacking.Hamiltonian
open Set Function MeasureTheory Filter
open scoped ContDiff Topology

def cutoffWedge (f : Plane → ℝ) (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) : ℝ :=
  fderiv ℝ f z (1,0)*β z (0,1)-fderiv ℝ f z (0,1)*β z (1,0)

end SymplecticBallPacking.Hamiltonian
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

def planarPullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Plane → E) (α : E → E →L[ℝ] ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  (α (v z)).comp (fderiv ℝ v z)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



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

def morreyConstant (C : ℝ) : ℝ := 4/(1-Real.sqrt (decayRatio C))








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


