-- Prove2me | Definitions.Def_OAIQ091C016
-- name    : OAIQ091C016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T17:06:15.498744+00:00
-- url     : https://prove2.me/theorems/2ea0ad4e-d70c-47de-a84a-1535387636c7
-- title:
--   Definitions bundle OAIQ091C016 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 14 definitions. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.ricciCompressionTensor`, `OAI.PositiveEinsteinFour.HighestHessian.rightDerivativeSlotForm`, `OAI.PositiveEinsteinFour.HighestHessian.rightSector`, `OAI.PositiveEinsteinFour.HighestHessian.rightTwist`, `OAI.PositiveEinsteinFour.HighestHessian.rightVectorGram`, `OAI.PositiveEinsteinFour.ScalarHessian.blockAction`, `OAI.PositiveEinsteinFour.ScalarHessian.blockActionLinear`, `OAI.PositiveEinsteinFour.ScalarHessian.coefficients`, `OAI.PositiveEinsteinFour.ScalarHessian.reconstruct`, `OAI.PositiveEinsteinFour.ScalarHessian.scalarCurvatureContraction`, `OAI.PositiveEinsteinFour.ScalarHessian.traceFreePart`, `OAI.PositiveEinsteinFour.TraceHessian.instNormedAlgebraRealMat`, `OAI.PositiveEinsteinFour.TraceHessian.liftSlicePairing`, `OAI.PositiveEinsteinFour.hessianQuadraticContribution`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_CurvatureTensors00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/CurvatureTensors00.lean), [`EinsteinFour_HighestMinusForm`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HighestMinusForm.lean), [`EinsteinFour_MinusProjectionCost`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/MinusProjectionCost.lean), [`EinsteinFour_TraceAdjoint`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/TraceAdjoint.lean), [`EinsteinFour_WeylEstimates01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean).
--
--   **Imports.** It imports the bundles `OAIQ091C006`, `OAIQ091C007`, `OAIQ091C010`, `OAIQ091C011` and `OAIQ091C012` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI_PositiveEinsteinFour_Potential_q2_nonneg` and `OAI_PositiveEinsteinFour_QuarticEnergy_quartic_energy_bound_gradient`; the proofs of `OAI.PositiveEinsteinFour.Geometry.FrameReflectionData.jointEnergyCancellation`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.matrixGreen`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusHVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusNormVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.normDifferenceVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusHVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusNormVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.preVarianceGreen_oriented`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.regularizedHessianGreen`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.traceGreen`, `OAI.PositiveEinsteinFour.HighestHessian.general_highestProjection_curvature_le`, `OAI.PositiveEinsteinFour.HighestHessian.general_weighted_trace_subtraction`, `OAI_PositiveEinsteinFour_Potential_potential_nonneg`, `OAI_PositiveEinsteinFour_Potential_q2_nonneg`, `OAI_PositiveEinsteinFour_QuarticClosed_quartic_energy_bound_closed`, `OAI_PositiveEinsteinFour_QuarticEnergy_quartic_energy_bound_gradient`, `OAI_PositiveEinsteinFour_Quartic_enlarged_quartic_bound` and `OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ091C006
import Definitions.Def_OAIQ091C007
import Definitions.Def_OAIQ091C010
import Definitions.Def_OAIQ091C011
import Definitions.Def_OAIQ091C012

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors00
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The scalar axial completion is applied coordinatewise to the actual
four-dimensional tangent vectors, retaining all mixed inner products. -/

namespace PositiveEinsteinFour

open scoped BigOperators
open Quadratic Potential Bianchi

noncomputable section

/-- The complete plus-block quadratic contribution before axial reduction.
The opposite cubic invariant is kept as `τ`. -/
def hessianQuadraticContribution (S : Shape) (v b τ : ℝ) (p k l : Vec) : ℝ :=
  weight v b * hessianTensorForm S v b p k l +
    (17 / 10 : ℝ) *
      ((6 * (S.sigma * v ^ 2 + τ * b ^ 2 - v - b) - 26 * (2 - v - b)) *
          ((parameters S p k l).squaredNorm / 6) +
        40 * (2 - v - b) * curvatureContraction S v (parameters S p k l)) +
    kappa v b * (((parameters S p k l).squaredNorm / 6 - ‖p‖ ^ 2) / v)

end
end PositiveEinsteinFour
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceAdjoint
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit trace lift is the actual adjoint on the Bianchi subspace. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open Bianchi

/-- Pairing of one outer-derivative slice of the lift with an actual Bianchi
matrix of four-vectors. -/
def liftSlicePairing (M : Mat) (i : Fin 4) (Z : Tensor) : ℝ :=
  ∑ a, ∑ b, ∑ j, traceLift M i j a b * Z.matrix a b j

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestMinusForm
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the actual anti-self-dual derivative curvature term. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The uncontracted right-quaternion curvature on the two derivative slots. -/
def rightDerivativeSlotForm (s : Fin 3) (X : Hessian) : ℝ :=
  ∑ a, ∑ b, ∑ i, ∑ j, ∑ k, ∑ l,
    rightQuaternion s i k * rightQuaternion s j l * X k l a b * X i j a b

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MinusProjectionCost
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp anti-self-dual upper cost on actual derivative tensors. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open TraceHessian

/-- Simultaneous right-quaternion action on the two derivative slots. -/
def rightTwist (s : Fin 3) (X : Hessian) : Hessian := fun i j a b =>
  ∑ k, ∑ l, rightQuaternion s i k * rightQuaternion s j l * X k l a b

/-- The four orthogonal sectors of the two real quaternion slots. -/
def rightSector (r : Fin 4) (X : Hessian) : Hessian := fun i j a b =>
  (X i j a b +
    (if r = 0 ∨ r = 1 then 1 else -1) * rightTwist 0 X i j a b +
    (if r = 0 ∨ r = 2 then 1 else -1) * rightTwist 1 X i j a b +
    (if r = 0 ∨ r = 3 then 1 else -1) * rightTwist 2 X i j a b) / 4

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Differentiate the invariant matrix Weyl equation before choosing a
diagonal frame. The derivative of its quadratic term is exactly twice
the concrete matrix-slot operator. -/

namespace PositiveEinsteinFour.TraceHessian

open Matrix PositiveEinsteinFour.Geometry
open scoped BigOperators

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.TraceHessian.instNormedRingMat
attribute [local instance] OAI.PositiveEinsteinFour.TraceHessian.instNormedSpaceRealMat
local instance instNormedAlgebraRealMat : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra

end
end PositiveEinsteinFour.TraceHessian
end


section

/-! The invariant Ricci equation has the actual Bianchi compression in
every orthonormal frame, without imposing a diagonal Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open Bianchi TraceHessian

noncomputable section

def ricciCompressionTensor (Z L : Tensor) : Tensor where
  diagonal i := (1 / 20 : ℝ) • ((13 : ℝ) • Z.diagonal i - L.diagonal i)
  off i := (1 / 20 : ℝ) • ((13 : ℝ) • Z.off i - L.off i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sharp opposite-block cost for an arbitrary symmetric coefficient
matrix.  A concrete orthogonal quaternion expansion of the two derivative
slots replaces a second choice of eigenframe. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- Their ordinary three-dimensional coefficient Gram form. -/
def rightVectorGram (U : Mat) (X : Hessian) : ℝ :=
  ∑ a, ∑ b, ∑ t : Fin 4, ∑ r, ∑ s,
    U r s * rightQuaternionCoefficients (fun i j => X i j a b) t r.succ *
      rightQuaternionCoefficients (fun i j => X i j a b) t s.succ

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The nine commuting-quaternion products are an actual orthogonal
basis for symmetric trace-free scalar Hessians in four dimensions. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular HighestHessian

noncomputable section

/-- Coefficients of the basis `-I_i J_j`, whose squared norms are four. -/
def coefficients (S : Matrix4) : Mat := fun i j =>
  rightQuaternionCoefficients S i.succ j.succ / 2

def reconstruct (C : Mat) : Matrix4 := ∑ i, ∑ j, C i j • mixingCoefficient i j

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! Actual scalar-Hessian Weyl operators, on the nine quaternion-product
coordinates. Only the algebra needed by the weighted variance is used. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular HighestHessian CurvatureContraction

noncomputable section

def blockActionLinear (Q : Fin 3 → Matrix4) (A : Mat) : Matrix4 →ₗ[ℝ] Matrix4 where
  toFun S := -(1 / 2 : ℝ) • ∑ r, ∑ s, A r s • (Q r * S * Q s)
  map_add' S T := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
  map_smul' c S := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
    calc
      _ = -(1 / 2 : ℝ) • ∑ r, ∑ s, c • (A r s • (Q r * S * Q s)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro s _
        exact smul_comm _ _ _
      _ = _ := by
        simp only [← Finset.smul_sum]
        exact smul_comm _ _ _

def blockAction (Q : Fin 3 → Matrix4) (A : Mat) (S : Matrix4) : Matrix4 :=
  blockActionLinear Q A S

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The scalar-Hessian curvature contraction in the weighted-variance
argument, with the actual Einstein curvature tensor and arbitrary
symmetric trace-free Weyl matrices. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Bianchi Angular CurvatureContraction
open PositiveEinsteinFour.Geometry

noncomputable section

def scalarCurvatureContraction (A U : Mat) (p : Vec) : ℝ :=
  ∑ l, ∑ h, ((1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k,
    (generalCoefficient quaternionMatrix A i k j l +
      generalCoefficient oppositeMatrix U i k j l) *
      generalEinsteinCoefficient A U i k j h)) * p h * p l

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The scalar Weyl operators annihilate the metric trace.  This identifies
actual Hessian contractions with their trace-free parts. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular CurvatureContraction

noncomputable section

def traceFreePart (S : Matrix4) : Matrix4 := S - (Matrix.trace S / 4) • (1 : Matrix4)

end
end PositiveEinsteinFour.ScalarHessian
end


end OAI
end


