-- Prove2me | Definitions.Def_OAIQ091C012
-- name    : OAIQ091C012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:55:45.734949+00:00
-- url     : https://prove2.me/theorems/8c726304-d0d2-4abb-abcd-00d2c18dbe82
-- title:
--   Definitions bundle OAIQ091C012 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 63 declarations of OpenAI's Lean: 36 definitions, 3 instances and 24 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Averages.outerSwap`, `OAI.PositiveEinsteinFour.Bianchi.costMatrix`, `OAI.PositiveEinsteinFour.HighestHessian.minusKernel`, `OAI.PositiveEinsteinFour.HighestHessian.rightCoefficientAction`, `OAI.PositiveEinsteinFour.HighestHessian.rightMatrixAction`, `OAI.PositiveEinsteinFour.HighestHessian.rightQuaternionCoefficients`, `OAI.PositiveEinsteinFour.HighestHessian.symmetricUnit`, `OAI.PositiveEinsteinFour.Jacobi.sineLogWronskian`, `OAI.PositiveEinsteinFour.Jacobi.weightedSinc`, `OAI.PositiveEinsteinFour.Quadratic.A11`, `OAI.PositiveEinsteinFour.Quadratic.A22`, `OAI.PositiveEinsteinFour.Quadratic.Hdiag`, `OAI.PositiveEinsteinFour.Quadratic.Hmixed`, `OAI.PositiveEinsteinFour.Quadratic.diagonalDifference`, `OAI.PositiveEinsteinFour.Quadratic.mixedCoefficient`, `OAI.PositiveEinsteinFour.Quadratic.mixedNumerator`, `OAI.PositiveEinsteinFour.Quadratic.quadraticCoefficient`, `OAI.PositiveEinsteinFour.QuarticClosed.axisEnergy`, `OAI.PositiveEinsteinFour.QuaternionFrame.projectionBracket`, `OAI.PositiveEinsteinFour.QuaternionFrame.quarticNormLoss`, `OAI.PositiveEinsteinFour.QuaternionFrame.radialQuadraticTerm`, `OAI.PositiveEinsteinFour.QuaternionFrame.rawQuaternion`, `OAI.PositiveEinsteinFour.QuaternionFrame.scalarCouplingTerm`, `OAI.PositiveEinsteinFour.QuaternionFrame.scalarHessianCorrection`, `OAI.PositiveEinsteinFour.QuaternionFrame.weightedCubicField`, `OAI.PositiveEinsteinFour.ScalarHessian.coefficientQuadratic`, `OAI.PositiveEinsteinFour.ScalarHessian.columnGram`, `OAI.PositiveEinsteinFour.ScalarHessian.rowGram`, `OAI.PositiveEinsteinFour.TraceHessian.derivativePairing`, `OAI.PositiveEinsteinFour.TraceHessian.plusKernel`, `OAI.PositiveEinsteinFour.TraceHessian.referenceShape`, `OAI.PositiveEinsteinFour.TraceHessian.slicesHessian`, `OAI.PositiveEinsteinFour.TraceHessian.slicesTrace`, `OAI.PositiveEinsteinFour.cp2Normalize`, `OAI.PositiveEinsteinFour.lowerBlock`, `OAI.PositiveEinsteinFour.reducedIntegrand`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_H1`, `EinsteinFour_AveragedRadial`, `EinsteinFour_CP2WeightedBessel`, `EinsteinFour_CurvatureGreen`, `EinsteinFour_CurvatureTensors00`, `EinsteinFour_CurvatureTensors02`, `EinsteinFour_GeneralMatrixCompression`, `EinsteinFour_HighestMinus`, `EinsteinFour_JacobiTraceAverage`, `EinsteinFour_QuarticClosed`, `EinsteinFour_SineLogPolynomial`, `EinsteinFour_SineLogRemainder`, `EinsteinFour_TensorPairing`, `EinsteinFour_TraceAdjoint`, `EinsteinFour_WeylEstimates00`, `EinsteinFour_WeylEstimates01`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C000`, `OAIQ091C001`, `OAIQ091C003` and `OAIQ091C004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C015` and `OAIQ091C016`; the statements `OAI_PositiveEinsteinFour_MetricDoubleCover_not_projective`, `OAI.PositiveEinsteinFour.Quadratic.B_ACE`, `OAI.PositiveEinsteinFour.Quadratic.B_ASE`, `OAI.PositiveEinsteinFour.Quadratic.B_CBE`, `OAI.PositiveEinsteinFour.Quadratic.B_SBE`, `OAI.PositiveEinsteinFour.Quadratic.B_SUB`, `OAI.PositiveEinsteinFour.Quadratic.axial_matrix_nonneg`, `OAI.PositiveEinsteinFour.hilbert_quadratic_bound_closed` and `OAI.PositiveEinsteinFour.reduced_integrand_bound`; the proofs of `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_0_1`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_0_2`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_1_0`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_1_1`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_1_2`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_0`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_1`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_2`, `OAI.PositiveEinsteinFour.Quadratic.B_ACE`, `OAI.PositiveEinsteinFour.Quadratic.B_ASE`, `OAI.PositiveEinsteinFour.Quadratic.B_CBE`, `OAI.PositiveEinsteinFour.Quadratic.B_SBE`, `OAI.PositiveEinsteinFour.Quadratic.B_SUB`, `OAI.PositiveEinsteinFour.Quadratic.axial_matrix_nonneg`, `OAI.PositiveEinsteinFour.hilbert_quadratic_bound_closed` and `OAI.PositiveEinsteinFour.reduced_integrand_bound`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C000
import Definitions.Def_OAIQ091C001
import Definitions.Def_OAIQ091C003
import Definitions.Def_OAIQ091C004

section
-- module Solutions.OAIQ091_EF.Compat
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1`

An upstream-friendly **definition** of a Euclidean `H¹`-type energy space built from `L²`.

At the current Mathlib pin, we do not have a ready-made Sobolev-space development for domains or
manifolds. For the Laplace–Beltrami compact-resolvent discharge, we mainly need:

1. a Hilbert space `H¹` equipped with a continuous embedding into `L²`;
2. a continuous “gradient” map `H¹ → L²(E)`; and later
3. a compactness theorem for the inclusion on bounded domains / compact manifolds (Rellich).

This file defines `H¹` as the closed submodule of `L² × L²(E)` generated by `C¹`-functions with
compact support and their gradients (expressed using the Riesz representation `toDual`).

## Main definitions

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c`:
  the `ℝ`-submodule of `C¹` compactly supported functions `E → ℝ`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1`:
  the (closed) `H¹` submodule of `L²(E) × L²(E,E)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2`:
  the continuous embedding `H¹ → L²`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2Grad`:
  the continuous gradient map `H¹ → L²(E)`.

No analytic “Sobolev theorems” are proved here; those are tracked separately (Rellich / elliptic
regularity beads).
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory
open MeasureTheory

section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpace_solutions
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpace_solutions
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpace_solutions
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

/-- `H¹` is complete (a Hilbert space once the ambient `L²` spaces are). -/
instance instCompleteSpace_h1 : CompleteSpace (↥(h1 (μ := μ) (E := E))) := by
  classical
  exact (isClosed_h1 (μ := μ) (E := E)).isComplete.completeSpace_coe

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AveragedRadial
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the proved Jacobi determinant deficit over initial geodesics.
The density is explicitly truncated at the first conjugate point. -/

namespace PositiveEinsteinFour.Jacobi

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

local instance instNormedAddCommGroupNormalMatrix_2_rbd5990_1 : NormedAddCommGroup NormalMatrix := Matrix.frobeniusNormedAddCommGroup
local instance instNormedSpaceRealNormalMatrix_1_rbd5990_1 : NormedSpace ℝ NormalMatrix := Matrix.frobeniusNormedSpace
instance matrixContinuousENorm_p0 : ContinuousENorm NormalMatrix :=
  @SeminormedAddGroup.toContinuousENorm NormalMatrix
    (inferInstanceAs (SeminormedAddGroup NormalMatrix))

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CP2WeightedBessel
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bessel's inequality for the two orthogonal directions used in the
projective midpoint construction. -/

namespace PositiveEinsteinFour

open EinsteinFour
open scoped BigOperators

noncomputable section

def cp2Normalize (v : CP2Vector) : CP2Vector :=
  (((‖v‖⁻¹ : ℝ) : ℂ)) • v

end
end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative-slot curvature integration. Divergence freedom removes
the differentiated coefficient, and skew-symmetry leaves exactly one half
of the covariant commutator. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

def outerSwap : CurvatureIndex ≃ CurvatureIndex :=
  Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl _)

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuarticClosed
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quartic estimate at vanishing Weyl blocks, with totalized division. -/

namespace PositiveEinsteinFour.QuarticClosed

open Energy QuarticEnergy

noncomputable section

/-- The surviving part of (19) when the first block and its energy vanish.
This expression has no division by the norm of that vanished block. -/
def axisEnergy (x b τ χ d f : ℝ) : ℝ :=
  (1 / 2) * Real.sqrt (3 / 5) * gradientSum 0 ((5 / 3) * d) *
    (scalarWeight b x * (f * Real.sqrt f)) +
    (9 / 64) * (gradientSum 0 ((5 / 3) * d)) ^ 2 *
      (projectionCoefficient b x τ χ * ((5 / 3) * d) +
        defectCoefficient b x * (f - (5 / 3) * d)) -
    (17 / 10) * f * ((f - (3 / 5) * ((5 / 3) * d)) / b)

end
end PositiveEinsteinFour.QuarticClosed

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates00
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The finite matrix certificates for the quadratic coupling estimate. -/

namespace PositiveEinsteinFour.Quadratic

open Potential

noncomputable section

def A11 (v b σ : ℝ) : ℝ :=
  P0 v b * (v * K1 v b σ - 5 * kappa v b) - (1 + σ) * v ^ 2 * (Pk v b) ^ 2
def A22 (v b σ : ℝ) : ℝ :=
  P0 v b * (v * K2 v b σ - kappa v b) - (1 + σ) * v ^ 2 * (Pl v b) ^ 2
def Hdiag (v b : ℝ) : ℝ :=
  8 * v * denominator v b * theta v b * (1 + v) -
    radialDenominator v * (158 * v + denominator v b *
      (v * (axialCoefficient v b + kappaV v b) + 2 * kappa v b / 3))
def mixedNumerator (v b : ℝ) : ℝ :=
  denominator v b * (kappaB v b + kappaB b v) / 2 - 158
def Hmixed (v b : ℝ) : ℝ := Sbound v b * mixedNumerator v b

end

end PositiveEinsteinFour.Quadratic
end


section

/-! The quadratic coupling bound (22), derived from the finite matrix certificate. -/

namespace PositiveEinsteinFour.Quadratic

open Potential

noncomputable section

def quadraticCoefficient (v b : ℝ) : ℝ :=
  axialCoefficient v b + 158 / denominator v b + kappaV v b + 2 * kappa v b / (3 * v)

def mixedCoefficient (v b : ℝ) : ℝ :=
  (kappaB v b + kappaB b v) / 2 - 158 / denominator v b

def diagonalDifference (v b : ℝ) : ℝ :=
  2 * theta v b * normWeight v - quadraticCoefficient v b

end

end PositiveEinsteinFour.Quadratic
end


section

/-!
# Assembly of the scalar integrand bounds

The quartic, quadratic, and potential estimates bound the scalar integrand.
The tangent pairing is the real inner product.
-/

namespace PositiveEinsteinFour

open Energy QuarticEnergy QuarticClosed Quadratic Boundary Potential

noncomputable section

/-- The explicit upper expression obtained after the quartic projection and
quadratic axial reductions. It retains the two actual total derivative
energies and the inner product of the two norm gradients. -/
def reducedIntegrand
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v b r s σ τ ρ χ e f : ℝ) (p q : E) : ℝ :=
  quarticEnergy v b ((5 / 3) * ‖p‖ ^ 2) ((5 / 3) * ‖q‖ ^ 2)
      (projectionCoefficient v (b * s) σ ρ) (projectionCoefficient b (v * r) τ χ)
      (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) e f +
    (quadraticCoefficient v b * ‖p‖ ^ 2 + 2 * mixedCoefficient v b * inner ℝ p q +
      quadraticCoefficient b v * ‖q‖ ^ 2) +
    zeroOrderIntegrand v b σ τ

end
end PositiveEinsteinFour
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors00
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-!
# The axial reduction of the quadratic coupling terms

The exact matrix certificate (21) implies the full three-variable quadratic
inequality. The proof multiplies by the positive `P0 * v` and applies the
closed two-by-two determinant criterion, so it also covers the axial endpoint.
-/

namespace PositiveEinsteinFour

open Quadratic Potential

noncomputable section

/-- The pure non-axial block in the quadratic part of the plus Weyl estimate. -/
def lowerBlock (v b σ k l : ℝ) : ℝ :=
  (K1 v b σ - 5 * kappa v b / v) * k ^ 2 +
    2 * K12 v b σ * k * l + (K2 v b σ - kappa v b / v) * l ^ 2

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

def referenceShape : Shape where
  s := ![-1, -1, 2]
  trace := by norm_num [Fin.sum_univ_succ]
  square := by norm_num [Fin.sum_univ_succ]

/-- Pairing with the corresponding derivative component of the gradient. -/
def derivativePairing (M : Mat) (i : Fin 4) (Z : Tensor) : ℝ :=
  ∑ a, ∑ b, M a b * Z.matrix a b i

/-- Trace of the two derivative slots, for a family of Bianchi gradients. -/
def slicesTrace (Z : Fin 4 → Tensor) : Mat := fun a b => ∑ i, (Z i).matrix a b i

/-- The actual four-index array associated to differentiated Bianchi tensors. -/
def slicesHessian (Z : Fin 4 → Tensor) : Hessian :=
  fun i j a b => (Z i).matrix a b j

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TensorPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Skew matrix actions on the actual four tensor slots. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators

/-- The Kronecker sum of the four actual infinitesimal rotation actions. -/
def plusKernel (s : Fin 3) (p q : TensorIndex) : ℝ :=
  (if p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2
    then quaternionMatrix s p.1 q.1 else 0) +
  (if p.1 = q.1 ∧ p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2
    then quaternionMatrix s p.2.1 q.2.1 else 0) +
  (if p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ p.2.2.2 = q.2.2.2
    then rotation s p.2.2.1 q.2.2.1 else 0) +
  (if p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1
    then rotation s p.2.2.2 q.2.2.2 else 0)

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeneralMatrixCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bianchi compression for an arbitrary symmetric trace-free Weyl matrix,
with no choice of a moving diagonal frame. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open TraceHessian PositiveEinsteinFour.Geometry

noncomputable section


def costMatrix (v : Fin 3 → Vec) : RawGradient :=
  ![![-v 0 + (3 : ℝ) • v 1,
      -quaternion 2 (v 2 + (2 : ℝ) • v 1),
      -quaternion 1 (v 2 - v 1 + v 0)],
    ![-quaternion 2 (v 2 + (2 : ℝ) • v 1),
      -v 0 - (3 : ℝ) • v 1,
      -quaternion 0 (v 2 - v 1 - v 0)],
    ![-quaternion 1 (v 2 - v 1 + v 0),
      -quaternion 0 (v 2 - v 1 - v 0), (2 : ℝ) • v 0]]

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestMinus
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The minus Casimir energy and curvature bound on actual highest Hessians. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

def minusKernel (s : Fin 3) (p q : TensorIndex) : ℝ :=
  (if p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2
    then rightQuaternion s p.1 q.1 else 0) +
  (if p.1 = q.1 ∧ p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2
    then rightQuaternion s p.2.1 q.2.1 else 0)

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

/-! The original weighted-Hessian curvature form with complete Weyl matrices.
The contractions retain the full symmetric Weyl matrices. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- The symmetric elementary off-diagonal coefficient. -/
def symmetricUnit (r s : Fin 3) : Mat :=
  fun i j => (if i = r ∧ j = s then 1 else 0) + (if i = s ∧ j = r then 1 else 0)


end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The quadratic and radial scalar contractions are unchanged by the
pointwise spectral frame. These are identities on finite arrays. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def weightedCubicField (a : Fin 4 → ℝ) (Z : Angular.Gradient) : ℝ :=
  ∑ i, a i * Matrix.trace (Z i * (∑ j, Z j * Z j))

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The sharp opposite-block cost for an arbitrary symmetric coefficient
matrix.  A concrete orthogonal quaternion expansion of the two derivative
slots replaces a second choice of eigenframe. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- The coefficients in the orthonormal basis `(L_a R_b)/2` of real
four-by-four matrices, with the scalar quaternion in position zero. -/
def rightQuaternionCoefficients (M : Mat4) : Mat4 :=
  ![![(M 0 0 + M 1 1 + M 2 2 + M 3 3) / 2,
      (-M 0 1 + M 1 0 + M 2 3 - M 3 2) / 2,
      (-M 0 2 - M 1 3 + M 2 0 + M 3 1) / 2,
      (-M 0 3 + M 1 2 - M 2 1 + M 3 0) / 2],
    ![(-M 0 1 + M 1 0 - M 2 3 + M 3 2) / 2,
      (-M 0 0 - M 1 1 + M 2 2 + M 3 3) / 2,
      (M 0 3 - M 1 2 - M 2 1 + M 3 0) / 2,
      (-M 0 2 - M 1 3 - M 2 0 - M 3 1) / 2],
    ![(-M 0 2 + M 1 3 + M 2 0 - M 3 1) / 2,
      (-M 0 3 - M 1 2 - M 2 1 - M 3 0) / 2,
      (-M 0 0 + M 1 1 - M 2 2 + M 3 3) / 2,
      (M 0 1 + M 1 0 - M 2 3 - M 3 2) / 2],
    ![(-M 0 3 - M 1 2 + M 2 1 + M 3 0) / 2,
      (M 0 2 - M 1 3 + M 2 0 - M 3 1) / 2,
      (-M 0 1 - M 1 0 - M 2 3 - M 3 2) / 2,
      (-M 0 0 + M 1 1 + M 2 2 - M 3 3) / 2]]

def rightMatrixAction (r : Fin 3) (M : Mat4) : Mat4 := fun i j =>
  (∑ k, rightQuaternion r i k * M k j) + ∑ k, rightQuaternion r j k * M i k

def rightCoefficientAction (r : Fin 3) (C : Mat4) : Mat4 := fun a =>
  ![![0, 0, 2 * C a 3, -2 * C a 2],
    ![0, -2 * C a 3, 0, 2 * C a 1],
    ![0, 2 * C a 2, -2 * C a 1, 0]] r

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Covariance of the actual Bianchi projection. The two generator
transformations are derived from the same quaternion frame change and
contract against its orthogonal three-dimensional matrix. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def rawQuaternion (s : Fin 3) (Z : RawGradient) : RawGradient :=
  fun a b => quaternion s (Z a b)

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Shifted positive Weyl coefficients give an upper bound on the scalar trace-free Hessian, using its actual nine real coefficients. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular HighestHessian

noncomputable section

def coefficientQuadratic (A : Mat) (c : Fin 3 → ℝ) : ℝ :=
  ∑ r, ∑ s, A r s * c r * c s

def columnGram (A C : Mat) : ℝ := ∑ j, coefficientQuadratic A (fun i => C i j)

def rowGram (A C : Mat) : ℝ := ∑ i, coefficientQuadratic A (fun j => C i j)

end
end PositiveEinsteinFour.ScalarHessian
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Norm-only forms of the cubic and true projection estimates. These are
unchanged by reflecting the opposite block's covector coordinates. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry
open Energy QuarticEnergy Quadratic Potential

noncomputable section

def projectionBracket (v y σ ρ e radial : ℝ) : ℝ :=
  projectionCoefficient v y σ ρ * ((5 / 3) * radial) +
    defectCoefficient v y * (e - (5 / 3) * radial)

/-- The tested scalar norm equations, trace subtraction and variance term
that are added to the two actual Hessian Green integrands. -/
def scalarCouplingTerm (v b e f B C NA NB TA TB : ℝ) (p q : Vec) : ℝ :=
  (17 / 10 : ℝ) * (-(e + f) * (NA + NB) - 26 * (2 - v - b) * (e + f) +
      40 * (2 - v - b) * (B + C) - (2 - v - b) * (TA + TB)) +
    158 * (‖p - q‖ ^ 2 / (4 + v ^ 2 + b ^ 2) -
      (1 - (2 - v - b) ^ 2 / 4) * (v - b) ^ 2) +
    kappa v b * NA + kappa b v * NB +
    kappaV v b * ‖p‖ ^ 2 + (kappaB v b + kappaB b v) * inner ℝ p q +
    kappaV b v * ‖q‖ ^ 2

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Exact scalar separation into quartic, axial quadratic, and potential
terms. No geometric estimate is an assumption in these identities. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry
open Energy QuarticEnergy Quadratic Potential Boundary

noncomputable section

def scalarHessianCorrection (v b σ τ e B radial : ℝ) : ℝ :=
  (17 / 10 : ℝ) *
      ((6 * (σ * v ^ 2 + τ * b ^ 2 - v - b) - 26 * (2 - v - b)) * e +
        40 * (2 - v - b) * B) +
    kappa v b * ((e - radial) / v)

def quarticNormLoss (v b e f : ℝ) (p q : Vec) : ℝ :=
  -(17 / 10 : ℝ) * (e + f) * ((e - ‖p‖ ^ 2) / v + (f - ‖q‖ ^ 2) / b)

def radialQuadraticTerm (v b : ℝ) (p q : Vec) : ℝ :=
  158 * (‖p - q‖ ^ 2 / (4 + v ^ 2 + b ^ 2)) +
    kappaV v b * ‖p‖ ^ 2 + (kappaB v b + kappaB b v) * inner ℝ p q +
    kappaV b v * ‖q‖ ^ 2

end
end PositiveEinsteinFour.QuaternionFrame
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiTraceAverage
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp averaged ordered-product estimate at Weyl energy three. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius
noncomputable section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

instance matrixContinuousENorm_p2 : ContinuousENorm NormalMatrix :=
  @SeminormedAddGroup.toContinuousENorm NormalMatrix
    (inferInstanceAs (SeminormedAddGroup NormalMatrix))

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SineLogPolynomial
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit comparison function for the lower-volume sine remainder. -/
namespace PositiveEinsteinFour.Jacobi
noncomputable section

def sineLogWronskian (x : ℝ) : ℝ :=
  Real.exp (-sineLogPolynomial x) * (sineCotPolynomial x * Real.sin x - x * Real.cos x)

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SineLogRemainder
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logarithmic sine bound supplying the strict volume correction. -/
namespace PositiveEinsteinFour.Jacobi
open Filter Set
open scoped _root_.Topology
noncomputable section

def weightedSinc (x : ℝ) : ℝ := Real.exp (sineLogPolynomial x) * Real.sinc x

end
end PositiveEinsteinFour.Jacobi

end OAI
end


