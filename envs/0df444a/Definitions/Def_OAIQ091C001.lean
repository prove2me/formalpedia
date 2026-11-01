-- Prove2me | Definitions.Def_OAIQ091C001
-- name    : OAIQ091C001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:48:39.498795+00:00
-- url     : https://prove2.me/theorems/9e02ab0c-bdd5-4b96-bb55-a13617a8678d
-- title:
--   Definitions bundle OAIQ091C001 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 460 declarations of OpenAI's Lean: 156 definitions, 2 inductive types or structures, 5 instances and 297 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Averages.CurvatureIndex`, `OAI.PositiveEinsteinFour.Averages.fieldIntegral`, `OAI.PositiveEinsteinFour.Averages.flowGreenNormedAddCommGroup`, `OAI.PositiveEinsteinFour.Averages.flowGreenNormedSpace`, `OAI.PositiveEinsteinFour.Averages.instNormedAddCommGroupContinuousMap_solutions`, `OAI.PositiveEinsteinFour.Averages.instNormedSpaceRealContinuousMap_solutions`, `OAI.PositiveEinsteinFour.Averages.sineMeasure`, `OAI.PositiveEinsteinFour.Averages.sineWeight`, `OAI.PositiveEinsteinFour.Bianchi.generatorCoefficients`, `OAI.PositiveEinsteinFour.Boundary.correctedPotential`, `OAI.PositiveEinsteinFour.Boundary.spectralCoefficient`, `OAI.PositiveEinsteinFour.Boundary.zeroOrderIntegrand`, `OAI.PositiveEinsteinFour.CP2Vector`, `OAI.PositiveEinsteinFour.Defect.A0`, `OAI.PositiveEinsteinFour.Defect.C0`, `OAI.PositiveEinsteinFour.Defect.L0`, `OAI.PositiveEinsteinFour.Defect.discriminantNumerator`, `OAI.PositiveEinsteinFour.Energy.defectCoefficient`, `OAI.PositiveEinsteinFour.Energy.gradientSum`, `OAI.PositiveEinsteinFour.Energy.quarticEnergy`, `OAI.PositiveEinsteinFour.Energy.scalarWeight`, `OAI.PositiveEinsteinFour.FlowCalculus.VariationSpace`, `OAI.PositiveEinsteinFour.FlowCalculus.variationalField`, `OAI.PositiveEinsteinFour.Geometry.CoordinateColumn`, `OAI.PositiveEinsteinFour.Geometry.CotangentIndex`, `OAI.PositiveEinsteinFour.Geometry.CotangentMatrix`, `OAI.PositiveEinsteinFour.Geometry.CovariantCoordinates`, `OAI.PositiveEinsteinFour.Geometry.CovariantTwoFormSkew`, `OAI.PositiveEinsteinFour.Geometry.HeatMat6`, `OAI.PositiveEinsteinFour.Geometry.JacobiCoordinateVector`, `OAI.PositiveEinsteinFour.Geometry.OrientedOrthogonalFour`, `OAI.PositiveEinsteinFour.Geometry.PositiveRadius`, `OAI.PositiveEinsteinFour.Geometry.TwoFormFour`, `OAI.PositiveEinsteinFour.Geometry.TwoFormMatrix`, `OAI.PositiveEinsteinFour.Geometry.TwoTensorEuclidean`, `OAI.PositiveEinsteinFour.Geometry.bianchiCycle`, `OAI.PositiveEinsteinFour.Geometry.chartRicci`, `OAI.PositiveEinsteinFour.Geometry.complexProjectiveEvaluation`, `OAI.PositiveEinsteinFour.Geometry.complexProjectiveTopology`, `OAI.PositiveEinsteinFour.Geometry.curvatureCycle` and 118 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_H1`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_ArzelaAscoli`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_SupportedH1`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2`, `EinsteinFour_ActualJacobiODEExistence`, `EinsteinFour_ActualJacobiODEMatrix`, `EinsteinFour_ActualRicciContraction`, `EinsteinFour_AngularDerivativeMoments`, `EinsteinFour_AngularEnergy`, `EinsteinFour_AngularNormal`, `EinsteinFour_AveragedRadial`, `EinsteinFour_Averages`, `EinsteinFour_Boundary`, `EinsteinFour_CP2Overlap`, `EinsteinFour_CP2UnitGeometry`, `EinsteinFour_CompactDomination`, `EinsteinFour_ConnectionPullback`, `EinsteinFour_ContinuousFieldDerivative`, `EinsteinFour_CoordinateMetricCompatibility`, `EinsteinFour_CotangentJacobian`, `EinsteinFour_Coupling`, `EinsteinFour_CurvatureFirstBianchi`, `EinsteinFour_CurvatureGreen`, `EinsteinFour_CurvatureTensors02`, `EinsteinFour_Defect`, `EinsteinFour_DirichletMatrix`, `EinsteinFour_Energy`, `EinsteinFour_FlowDifferentiability`, `EinsteinFour_FlowFiniteRegularity`, `EinsteinFour_FlowGermUniqueness`, `EinsteinFour_FlowGreen`, `EinsteinFour_FlowJointDifferentiability`, `EinsteinFour_FlowLocalDifferentiability`, `EinsteinFour_FlowTimeReversal`, `EinsteinFour_FlowVariationalExistence`, `EinsteinFour_FlowVariationalRegularity`, `EinsteinFour_FourDeterminantDerivative`, `EinsteinFour_FourHeatGaussian`, `EinsteinFour_FourHeatGaussianDifferential`, `EinsteinFour_FourHeatGaussianEquation`, `EinsteinFour_FourHeatGaussianTimeRegularity`, `EinsteinFour_FrameCurvatureMetricSkew`, `EinsteinFour_GeodesicAverage`, `EinsteinFour_GeodesicGeometry04`, `EinsteinFour_GeodesicGeometry12`, `EinsteinFour_GeodesicGeometry13`, `EinsteinFour_GeodesicJacobiAlgebra`, `EinsteinFour_GradientCoordinateModel`, `EinsteinFour_HeatDriftTransportAlgebra`, `EinsteinFour_HeatRoughTraceAlgebra`, `EinsteinFour_HighestProjection`, `EinsteinFour_HodgeTheory08`, `EinsteinFour_JacobiAverage`, `EinsteinFour_JacobiODEPositivity`, `EinsteinFour_JacobiScheme`, `EinsteinFour_JacobiSchemeRatios`, `EinsteinFour_LocalCoordinateMeasure`, `EinsteinFour_MetricChartLipschitz`, `EinsteinFour_MetricContractionCalculus`, `EinsteinFour_MetricInverseCalculus`, `EinsteinFour_ModeAverageLimit`, `EinsteinFour_OrientationCoverCore`, `EinsteinFour_Potential`, `EinsteinFour_QuaternionGenerators`, `EinsteinFour_QuaternionReflections`, `EinsteinFour_RicciMatrixChange`, `EinsteinFour_ScalarNormalizer`, `EinsteinFour_ScalarPoissonKernelCommutator`, `EinsteinFour_ScalarPoissonKernelCutoffs`, `EinsteinFour_ScalarPoissonKernelDerivative`, `EinsteinFour_ScalarPoissonKernelSobolev`, `EinsteinFour_ScalarRegularity07`, `EinsteinFour_SineAverage`, `EinsteinFour_TensorPairing`, `EinsteinFour_WeightedConnectionCurvature`, `EinsteinFour_WeightedCurve`, `EinsteinFour_WeylDerivative`, `EinsteinFour_WeylEstimates01`, `EinsteinFour_WeylEstimates03`, `EinsteinFour_WeylGeometry`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C006`, `OAIQ091C007`, `OAIQ091C008`, `OAIQ091C009`, `OAIQ091C010`, `OAIQ091C011` and `OAIQ091C012`; the statements `OAI_PositiveEinsteinFour_Boundary_theta_swap`, `OAI_PositiveEinsteinFour_Boundary_zeroOrderIntegrand_swap`, `OAI.PositiveEinsteinFour.Boundary.zeroOrder_bound` and `OAI_PositiveEinsteinFour_QuarticClosed_quartic_energy_bound_closed`; the proofs of `OAI_PositiveEinsteinFour_Boundary_theta_swap`, `OAI_PositiveEinsteinFour_Boundary_zeroOrderIntegrand_swap` and `OAI.PositiveEinsteinFour.Boundary.zeroOrder_bound`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour

section
-- module Solutions.OAIQ091_EF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
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

local instance instMeasurableSpace_solutions : MeasurableSpace E := borel E
local instance instBorelSpace_solutions : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpace_solutions : OpensMeasurableSpace E := by infer_instance

variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

abbrev L2ℝ : Type _ := ↥(E →₂[μ] ℝ)
abbrev L2E : Type _ := ↥(E →₂[μ] E)
abbrev H1Target : Type _ := L2ℝ (μ := μ) × L2E (μ := μ)

/-- `C¹` real-valued functions on `E` with compact support, as a submodule of `E → ℝ`. -/
def C1c : Submodule ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ 1 f ∧ HasCompactSupport f}
  zero_mem' := by
    refine ⟨contDiff_const, ?_⟩
    simpa using (HasCompactSupport.zero : HasCompactSupport (fun _ : E => (0 : ℝ)))
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c, ?_⟩
    -- `HasCompactSupport` is stable under pointwise scalar multiplication.
    exact HasCompactSupport.smul_left (f := fun _ : E => c) hf.2

/-- The pointwise gradient (as an `E`-valued function), via Riesz representation. -/
noncomputable def grad (f : E → ℝ) : E → E :=
  fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)

lemma continuous_grad {f : E → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (grad (E := E) f) := by
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have : Continuous fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp hcont
  exact this

lemma hasCompactSupport_grad {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (grad (E := E) f) := by
  -- Outside the support of `f`, `fderiv` is identically `0`, hence so is `grad`.
  have hf' : HasCompactSupport (fderiv ℝ f) := hf.fderiv ℝ
  -- `grad` is composition with a linear map sending `0` to `0`.
  exact
    (HasCompactSupport.comp_left (f := fderiv ℝ f) (g := (InnerProductSpace.toDual ℝ E).symm)
      hf' (by simp))

omit [CompleteSpace E] in
lemma memLp_of_mem_C1c {f : E → ℝ} (hf : f ∈ C1c (E := E)) : MemLp f 2 μ := by
  exact (hf.1.continuous.memLp_of_hasCompactSupport (μ := μ) (p := (2 : ℝ≥0∞)) hf.2)

lemma memLp_grad_of_mem_C1c {f : E → ℝ} (hf : f ∈ C1c (E := E)) :
    MemLp (grad (E := E) f) 2 μ := by
  have hcont : Continuous (grad (E := E) f) := continuous_grad (E := E) (f := f) hf.1
  have hcs : HasCompactSupport (grad (E := E) f) := hasCompactSupport_grad (E := E) (f := f) hf.2
  exact hcont.memLp_of_hasCompactSupport (μ := μ) (p := (2 : ℝ≥0∞)) hcs

/-- The `L²` class of a `C¹` compactly supported function. -/
noncomputable def toL2 (f : ↥(C1c (E := E))) : L2ℝ (μ := μ) :=
  (memLp_of_mem_C1c (μ := μ) (E := E) f.2).toLp f.1

/-- The `L²` class of the gradient of a `C¹` compactly supported function. -/
noncomputable def toL2Grad (f : ↥(C1c (E := E))) : L2E (μ := μ) :=
  (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).toLp (grad (E := E) f.1)

omit [CompleteSpace E] in
lemma toL2_add (f g : ↥(C1c (E := E))) :
    toL2 (μ := μ) (E := E) (f + g) =
      toL2 (μ := μ) (E := E) f + toL2 (μ := μ) (E := E) g := by
  apply Lp.ext
  have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hg : (toL2 (μ := μ) (E := E) g : E → ℝ) =ᵐ[μ] g.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) g.2).coeFn_toLp
  have hfg : (toL2 (μ := μ) (E := E) (f + g) : E → ℝ) =ᵐ[μ] (f.1 + g.1) :=
    (memLp_of_mem_C1c (μ := μ) (E := E) (f + g).2).coeFn_toLp
  -- Both sides agree a.e. with `f + g`.
  refine hfg.trans ?_
  filter_upwards [Lp.coeFn_add (toL2 (μ := μ) (E := E) f) (toL2 (μ := μ) (E := E) g), hf, hg]
    with x hxadd hxf hxg
  -- Rewrite both sides in terms of pointwise evaluation.
  calc
    f.1 x + g.1 x =
        (toL2 (μ := μ) (E := E) f : E → ℝ) x +
          (toL2 (μ := μ) (E := E) g : E → ℝ) x := by
      simp [hxf, hxg]
    _ = ((toL2 (μ := μ) (E := E) f + toL2 (μ := μ) (E := E) g : L2ℝ (μ := μ)) : E → ℝ) x := by
      simpa [Pi.add_apply] using hxadd.symm

omit [CompleteSpace E] in
lemma toL2_smul (c : ℝ) (f : ↥(C1c (E := E))) :
    toL2 (μ := μ) (E := E) (c • f) = c • toL2 (μ := μ) (E := E) f := by
  apply Lp.ext
  have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hcf : (toL2 (μ := μ) (E := E) (c • f) : E → ℝ) =ᵐ[μ] (c • f.1) :=
    (memLp_of_mem_C1c (μ := μ) (E := E) (c • f).2).coeFn_toLp
  refine hcf.trans ?_
  filter_upwards [Lp.coeFn_smul c (toL2 (μ := μ) (E := E) f), hf] with x hxsmul hxf
  simp [Pi.smul_apply, hxsmul, hxf]

/-- Linear map sending `C¹_c` functions to their `L²` classes. -/
noncomputable def toL2Linear : ↥(C1c (E := E)) →ₗ[ℝ] L2ℝ (μ := μ) where
  toFun := toL2 (μ := μ) (E := E)
  map_add' := toL2_add (μ := μ) (E := E)
  map_smul' := toL2_smul (μ := μ) (E := E)

lemma toL2Grad_add (f g : ↥(C1c (E := E))) :
    toL2Grad (μ := μ) (E := E) (f + g) =
      toL2Grad (μ := μ) (E := E) f + toL2Grad (μ := μ) (E := E) g := by
  apply Lp.ext
  have hf : (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hg : (toL2Grad (μ := μ) (E := E) g : E → E) =ᵐ[μ] grad (E := E) g.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) g.2).coeFn_toLp
  have hfg :
      (toL2Grad (μ := μ) (E := E) (f + g) : E → E) =ᵐ[μ] grad (E := E) (f.1 + g.1) :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) (f + g).2).coeFn_toLp
  refine hfg.trans ?_
  filter_upwards [Lp.coeFn_add (toL2Grad (μ := μ) (E := E) f) (toL2Grad (μ := μ) (E := E) g), hf,
    hg] with x hxadd hxf hxg
  have hdf : DifferentiableAt ℝ f.1 x :=
    (f.2.1.differentiable one_ne_zero).differentiableAt
  have hdg : DifferentiableAt ℝ g.1 x :=
    (g.2.1.differentiable one_ne_zero).differentiableAt
  -- Rewrite in terms of pointwise evaluation and use linearity of `grad`.
  have hgrad :
      grad (E := E) (f.1 + g.1) x = grad (E := E) f.1 x + grad (E := E) g.1 x := by
    simp [grad, fderiv_add hdf hdg, map_add]
  calc
    grad (E := E) (f.1 + g.1) x = grad (E := E) f.1 x + grad (E := E) g.1 x := hgrad
    _ =
        (toL2Grad (μ := μ) (E := E) f : E → E) x +
          (toL2Grad (μ := μ) (E := E) g : E → E) x := by
        simp [hxf, hxg]
    _ = ((toL2Grad (μ := μ) (E := E) f +
            toL2Grad (μ := μ) (E := E) g : L2E (μ := μ)) :
            E → E) x := by
        simpa [Pi.add_apply] using hxadd.symm

lemma toL2Grad_smul (c : ℝ) (f : ↥(C1c (E := E))) :
    toL2Grad (μ := μ) (E := E) (c • f) = c • toL2Grad (μ := μ) (E := E) f := by
  apply Lp.ext
  have hf : (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hcf :
      (toL2Grad (μ := μ) (E := E) (c • f) : E → E) =ᵐ[μ] grad (E := E) (c • f.1) :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) (c • f).2).coeFn_toLp
  refine hcf.trans ?_
  filter_upwards [Lp.coeFn_smul c (toL2Grad (μ := μ) (E := E) f), hf] with x hxsmul hxf
  have hdf : DifferentiableAt ℝ f.1 x :=
    (f.2.1.differentiable one_ne_zero).differentiableAt
  have hgrad : grad (E := E) (c • f.1) x = c • grad (E := E) f.1 x := by
    simp [grad, fderiv_const_smul hdf, map_smul]
  calc
    grad (E := E) (c • f.1) x = c • grad (E := E) f.1 x := hgrad
    _ = c • (toL2Grad (μ := μ) (E := E) f : E → E) x := by
      simp [hxf]
    _ = ((c • toL2Grad (μ := μ) (E := E) f : L2E (μ := μ)) : E → E) x := by
      -- `Lp.coeFn_smul` gives the pointwise evaluation of `c • f` in `L²`.
      simpa [Pi.smul_apply] using hxsmul.symm

/-- Linear map sending `C¹_c` functions to the `L²` class of their gradient. -/
noncomputable def toL2GradLinear : ↥(C1c (E := E)) →ₗ[ℝ] L2E (μ := μ) where
  toFun := toL2Grad (μ := μ) (E := E)
  map_add' := toL2Grad_add (μ := μ) (E := E)
  map_smul' := toL2Grad_smul (μ := μ) (E := E)

/-- The graph map `f ↦ (f, ∇f)` into `L² × L²(E)`. -/
noncomputable def graph : ↥(C1c (E := E)) →ₗ[ℝ] H1Target (μ := μ) :=
  (toL2Linear (μ := μ) (E := E)).prod (toL2GradLinear (μ := μ) (E := E))

/-- The Euclidean `H¹` space (as a closed submodule of `L² × L²(E)`). -/
noncomputable def h1 : Submodule ℝ (H1Target (μ := μ)) :=
  (LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure

/-- The Euclidean `H¹` submodule is closed by construction. -/
theorem isClosed_h1 : IsClosed (h1 (μ := μ) (E := E) : Set (H1Target (μ := μ))) := by
  delta h1
  exact Submodule.isClosed_topologicalClosure (LinearMap.range (graph (μ := μ) (E := E)))

/-- The continuous embedding `H¹ → L²`. -/
noncomputable def h1ToL2 : (↥(h1 (μ := μ) (E := E))) →L[ℝ] L2ℝ (μ := μ) :=
  (ContinuousLinearMap.fst ℝ (L2ℝ (μ := μ)) (L2E (μ := μ))).comp
    (Submodule.subtypeL (h1 (μ := μ) (E := E)))

/-- The continuous gradient map `H¹ → L²(E)`. -/
noncomputable def h1ToL2Grad : (↥(h1 (μ := μ) (E := E))) →L[ℝ] L2E (μ := μ) :=
  (ContinuousLinearMap.snd ℝ (L2ℝ (μ := μ)) (L2E (μ := μ))).comp
    (Submodule.subtypeL (h1 (μ := μ) (E := E)))

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
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
# `L²` compactness criterion: smoothing setup (Euclidean)

This file provides the basic “extend by zero + smooth by convolution” infrastructure used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main results

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.extendByZeroL2`:
  extend `u : L²(volume.restrict K)` by zero to an element of `L²(volume)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothL2`:
  a smoothing operator obtained by convolution with a compactly supported continuous kernel `ψ`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma tsupport_indicator_subset_closure (s : Set E) (f : E → ℝ) :
    tsupport (s.indicator f) ⊆ closure s := by
  -- `Function.support (s.indicator f) ⊆ s`, hence the topological support is contained in
  -- `closure s`.
  simpa [tsupport] using closure_mono (Set.support_indicator_subset (s := s) (f := f))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma hasCompactSupport_indicator_of_isCompact (s : Set E) (hs : IsCompact s) (f : E → ℝ) :
    HasCompactSupport (s.indicator f) := by
  have hs_closed : IsClosed s := hs.isClosed
  -- `tsupport (s.indicator f)` is closed and contained in the compact set `s`.
  refine hs.of_isClosed_subset (isClosed_tsupport _) ?_
  have : tsupport (s.indicator f) ⊆ closure s := tsupport_indicator_subset_closure (E := E) s f
  simpa [hs_closed.closure_eq] using this

end

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- `volume` is the canonical Haar measure on finite-dimensional real vector spaces.
local instance instMeasurableSpace_solutions_1 : MeasurableSpace E := borel E
local instance instBorelSpace_solutions_1 : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpace_solutions_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable {K : Set E}

local instance instMeasurableAdd_solutions_1_re7c677_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
/-- Extend an `L²` function on `K` by zero to a pointwise function on the ambient space. -/
def extendByZeroFun (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : E → ℝ :=
  K.indicator fun x : E => u x

lemma hasCompactSupport_extendByZeroFun (hK : IsCompact K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    HasCompactSupport (extendByZeroFun (K := K) u) := by
  classical
  -- The indicator is pointwise supported in `K`.
  simpa [extendByZeroFun] using
    (hasCompactSupport_indicator_of_isCompact (E := E) (s := K) hK (f := fun x => u x))

/-- `extendByZeroFun` packaged as an element of `L²(volume)`. -/
noncomputable def extendByZeroL2 (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (E →₂[(volume : Measure E)] ℝ) := by
  classical
  have hu : MeasureTheory.MemLp (fun x : E => u x) (2 : ℝ≥0∞) (volume.restrict K) :=
    MeasureTheory.Lp.memLp u
  have hm :
      MeasureTheory.MemLp (extendByZeroFun (K := K) u) (2 : ℝ≥0∞) (volume : Measure E) := by
    simpa [extendByZeroFun] using
      (MeasureTheory.memLp_indicator_iff_restrict (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := K) (f := fun x : E => u x) hKm).2 hu
  exact hm.toLp (extendByZeroFun (K := K) u)

lemma extendByZeroL2_ae_eq (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (extendByZeroL2 (E := E) (K := K) hKm u : E → ℝ) =ᵐ[(volume : Measure E)]
      extendByZeroFun (E := E) (K := K) u := by
  classical
  simp [extendByZeroL2, MeasureTheory.MemLp.coeFn_toLp]

variable (ψ : E → ℝ)

/-- Smoothing by convolution with a fixed kernel `ψ`, applied to the zero-extension from `K`. -/
def smoothFun (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : E → ℝ :=
  (extendByZeroFun (K := K) u) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ

lemma continuous_smoothFun
    (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Continuous (smoothFun (K := K) ψ u) := by
  -- `extendByZeroFun u` is `L²`, hence locally integrable; convolution with a compactly supported
  -- continuous kernel is continuous.
  have hf_memLp :
      MeasureTheory.MemLp (extendByZeroFun (K := K) u)
        (2 : ℝ≥0∞) (volume : Measure E) := by
    have hu : MeasureTheory.MemLp (fun x : E => u x) (2 : ℝ≥0∞) (volume.restrict K) :=
      MeasureTheory.Lp.memLp u
    simpa [extendByZeroFun] using
      (MeasureTheory.memLp_indicator_iff_restrict (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := K) (f := fun x : E => u x) hKm).2 hu
  have hf_loc :
      MeasureTheory.LocallyIntegrable (extendByZeroFun (K := K) u)
        (volume : Measure E) := by
    have h12 : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
    exact hf_memLp.locallyIntegrable h12
  simpa [smoothFun] using
    (hψcs.continuous_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure E)) hf_loc hψc)

lemma hasCompactSupport_smoothFun (hK : IsCompact K) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    HasCompactSupport (smoothFun (K := K) ψ u) := by
  have hf : HasCompactSupport (extendByZeroFun (K := K) u) :=
    hasCompactSupport_extendByZeroFun (K := K) hK u
  simpa [smoothFun] using
    (hf.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure E)) hψcs)

lemma support_smoothFun_subset_add_tsupport
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Function.support (smoothFun (E := E) (K := K) ψ u) ⊆ K + tsupport ψ := by
  classical
  have hsupp :
      Function.support (smoothFun (E := E) (K := K) ψ u) ⊆
        Function.support (extendByZeroFun (E := E) (K := K) u) + Function.support ψ := by
    simpa [smoothFun] using
      (support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure E))
        (f := extendByZeroFun (E := E) (K := K) u) (g := ψ))
  have h1 : Function.support (extendByZeroFun (E := E) (K := K) u) ⊆ K := by
    simp [extendByZeroFun]
  have h2 : Function.support ψ ⊆ tsupport ψ := by
    simpa [tsupport] using (subset_closure : Function.support ψ ⊆ closure (Function.support ψ))
  exact hsupp.trans (add_subset_add h1 h2)

/-- `smoothFun` packaged as an element of `L²(volume)`. -/
noncomputable def smoothL2 (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : (E →₂[(volume : Measure E)] ℝ) :=
  let hs : HasCompactSupport (smoothFun (K := K) ψ u) :=
    hasCompactSupport_smoothFun (K := K) ψ hK hψcs u
  let hm : MeasureTheory.MemLp (smoothFun (K := K) ψ u) (2 : ℝ≥0∞) (volume : Measure E) := by
    have hc : Continuous (smoothFun (K := K) ψ u) := continuous_smoothFun (K := K) ψ hKm hψc hψcs u
    exact hc.memLp_of_hasCompactSupport (μ := (volume : Measure E)) hs
  hm.toLp (smoothFun (K := K) ψ u)

lemma smoothL2_ae_eq (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u : E → ℝ) =ᵐ[(volume : Measure E)]
      smoothFun (E := E) (K := K) ψ u := by
  classical
  simp [smoothL2, MeasureTheory.MemLp.coeFn_toLp]
end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
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
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation`

Translation utilities for the Euclidean Sobolev model spaces.

This file is intentionally “pre-Rellich”: it provides the algebraic/measure-theoretic translation
operators and their interaction with the `C¹_c` graph embedding used to define `H¹`.

## Main results

- `translateC1c`: translation as a linear endomorphism of `C¹_c`.
- `translateL2`: translation as a linear isometry of `L²` (under an invariant measure).
- `translateL2_toL2` / `translateL2_toL2Grad`: translation commutes with `toL2` / `toL2Grad`.
- `grad_translate`: the Euclidean gradient commutes with translation.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory

section Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceE_SobolevEuclideanTranslation : MeasurableSpace E := borel E
local instance instBorelSpaceE_SobolevEuclideanTranslation : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslation_re7c677_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_SobolevEuclideanTranslation : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable (μ : Measure E) [μ.IsAddRightInvariant]

/-- Translation on `L²` as a linear isometry, under an additive right-invariant measure. -/
noncomputable def translateL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E) :
    (E →₂[μ] F) →ₗᵢ[ℝ] (E →₂[μ] F) := by
  classical
  simpa using
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := F) (p := (2 : ENNReal))
      (μ := μ) (μb := μ) (f := fun x : E => x + a) (MeasureTheory.measurePreserving_add_right μ a))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma translateL2_ae_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (g : E →₂[μ] F) :
    (translateL2 (μ := μ) (F := F) a g : E → F) =ᵐ[μ] fun x => (g : E → F) (x + a) := by
  classical
  -- Reduce to `Lp.coeFn_compMeasurePreserving`.
  exact
    (MeasureTheory.Lp.coeFn_compMeasurePreserving (g := (g : MeasureTheory.Lp F (2 : ENNReal) μ))
      (hf := MeasureTheory.measurePreserving_add_right μ a))

end Measure

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation
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
# `L²` compactness criterion: approximation-by-translation bounds (Euclidean)

This file will prove the key inequality used in the Fréchet–Kolmogorov approach: smoothing by a
probability kernel controls the `L²` error by the translation modulus.

## Main results (planned)

The principal statement will control `‖smoothL2 ψ u - extendByZeroL2 u‖₂` by an average (or sup) of
`‖translateL2 t (extendByZeroL2 u) - extendByZeroL2 u‖₂` over `t` in the support of `ψ`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpace_solutions_2 : MeasurableSpace E := borel E
local instance instBorelSpace_solutions_2 : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpace_solutions_2 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAdd_solutions_2 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNeg_solutions : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable {K : Set E} (hK : IsCompact K) (hKm : MeasurableSet K)
variable (ψ : E → ℝ)

/-- The measure with density `ψ` with respect to Lebesgue measure. This will be a probability
measure once `ψ ≥ 0` and `∫ ψ = 1`. -/
noncomputable def kernelMeasure : Measure E :=
  (volume : Measure E).withDensity fun x => ENNReal.ofReal (ψ x)

lemma kernelMeasure_univ (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) :
    kernelMeasure (E := E) ψ Set.univ = 1 := by
  have hψi : MeasureTheory.Integrable ψ (volume : Measure E) :=
    Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure E)) hψc hψcs
  have hψae : (MeasureTheory.ae (volume : Measure E)).EventuallyLE 0 ψ :=
    Filter.Eventually.of_forall hψ0
  have hlin :
      (∫⁻ x, ENNReal.ofReal (ψ x) ∂(volume : Measure E)) =
        ENNReal.ofReal (∫ x, ψ x ∂(volume : Measure E)) := by
    symm
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hψi hψae
  -- `withDensity` on `univ` is the `lintegral` of the density.
  have hwd :
      kernelMeasure (E := E) ψ Set.univ =
        ∫⁻ x, ENNReal.ofReal (ψ x) ∂(volume : Measure E) := by
    simp [kernelMeasure, MeasureTheory.withDensity_apply, MeasurableSet.univ]
  -- Conclude using `∫ ψ = 1`.
  simpa [hψint] using (hwd.trans hlin)

theorem instIsProbabilityMeasure_kernelMeasure
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) :
    MeasureTheory.IsProbabilityMeasure (kernelMeasure (E := E) ψ) :=
  ⟨kernelMeasure_univ (E := E) (ψ := ψ) hψc hψcs hψ0 hψint⟩

lemma integral_kernelMeasure_eq_integral_smul (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (g : E → ℝ) :
    (∫ x, g x ∂kernelMeasure (E := E) ψ) =
      ∫ x, (ψ x) • (g x) ∂(volume : Measure E) := by
  have hmeas : Measurable fun x => ENNReal.ofReal (ψ x) :=
    (hψc.measurable.ennreal_ofReal : Measurable fun x => ENNReal.ofReal (ψ x))
  have htop :
      (MeasureTheory.ae (volume : Measure E)).Eventually
        (fun x => ENNReal.ofReal (ψ x) < ∞) :=
    Filter.Eventually.of_forall (fun _ => by simp)
  have hwd :=
    (integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure E))
      (f := fun x => ENNReal.ofReal (ψ x)) hmeas htop g)
  have hwd' :
      (∫ x, g x ∂kernelMeasure (E := E) ψ) =
        ∫ x, (ENNReal.ofReal (ψ x)).toReal • (g x) ∂(volume : Measure E) := by
    simpa [kernelMeasure] using hwd
  -- Simplify `toReal (ofReal _)` using `ψ ≥ 0`.
  refine hwd'.trans ?_
  refine integral_congr_ae ?_
  refine ae_of_all _ (fun x => ?_)
  have hx : (ENNReal.ofReal (ψ x)).toReal = ψ x :=
    ENNReal.toReal_ofReal (hψ0 x)
  -- After rewriting `toReal (ofReal _)`, both sides are definitional.
  simp [hx]

lemma integral_kernelMeasure_eq_integral_mul (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (g : E → ℝ) :
    (∫ x, g x ∂kernelMeasure (E := E) ψ) =
      ∫ x, (ψ x) * (g x) ∂(volume : Measure E) := by
  simpa [smul_eq_mul] using integral_kernelMeasure_eq_integral_smul (E := E) (ψ := ψ) hψc hψ0 g

lemma smoothFun_eq_integral_kernelMeasure (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    smoothFun (E := E) (K := K) ψ u x =
      ∫ t, extendByZeroFun (E := E) (K := K) u (x - t) ∂kernelMeasure (E := E) ψ := by
  have hconv :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (extendByZeroFun (E := E) (K := K) u) (x - t) • (ψ t) ∂(volume : Measure E) := by
    simp [smoothFun, convolution_lsmul_swap]
  have hconv' :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (ψ t) * extendByZeroFun (E := E) (K := K) u (x - t) ∂(volume : Measure E) := by
    refine hconv.trans ?_
    refine integral_congr_ae ?_
    refine ae_of_all _ (fun t => ?_)
    -- In `ℝ`, scalar multiplication is multiplication, so we can commute the factors.
    change
      extendByZeroFun (E := E) (K := K) u (x - t) • ψ t =
        ψ t * extendByZeroFun (E := E) (K := K) u (x - t)
    rw [smul_eq_mul]
    simp [mul_comm]
  -- Rewrite the convolution integral as an integral against the density measure.
  have hwd :
      (∫ t, extendByZeroFun (E := E) (K := K) u (x - t) ∂kernelMeasure (E := E) ψ) =
        ∫ t, (ψ t) * extendByZeroFun (E := E) (K := K) u (x - t) ∂(volume : Measure E) := by
    exact integral_kernelMeasure_eq_integral_mul (E := E) (ψ := ψ) hψc hψ0
      (g := fun t => extendByZeroFun (E := E) (K := K) u (x - t))
  exact hconv'.trans hwd.symm

lemma sq_integral_le_integral_sq_of_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [MeasureTheory.IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : MeasureTheory.MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, (f x) ^ 2 ∂μ := by
  have hvar := ProbabilityTheory.variance_nonneg (X := f) μ
  have hvar' :
      0 ≤ (∫ x, (f x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
    simpa [ProbabilityTheory.variance_eq_sub (μ := μ) hf] using hvar
  linarith

lemma norm_sq_eq_integral_sq (v : (E →₂[(volume : Measure E)] ℝ)) :
    ‖v‖ ^ 2 = ∫ x, (v x) ^ 2 ∂(volume : Measure E) := by
  have hn : ‖v‖ ^ 2 = RCLike.re (inner ℝ v v) :=
    norm_sq_eq_re_inner (𝕜 := ℝ) v
  -- Unfold the `L²` inner product as an integral; for `ℝ`, `re` is the identity.
  rw [hn]
  -- `L²` inner product is an integral of pointwise inner products.
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ) (μ := (volume : Measure E)) v v]
  -- For `ℝ`, `RCLike.re` is the identity and `inner` simplifies to a square.
  simp [pow_two]

lemma norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq (t : E)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖(translateL2 (μ := (volume : Measure E)) (-t))
        (extendByZeroL2 (E := E) (K := K) hKm u)
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 =
      ∫ x,
        (extendByZeroFun (E := E) (K := K) u (x - t) - extendByZeroFun (E := E) (K := K) u x) ^ 2
          ∂(volume : Measure E) := by
  classical
  let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  have hF_ae : (F : E → ℝ) =ᵐ[(volume : Measure E)] f :=
    extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
  -- Translate AE equality along `x ↦ x - t`.
  have hF_shift :
      (fun x : E => (F : E → ℝ) (x - t)) =ᵐ[(volume : Measure E)] fun x => f (x - t) := by
    have hmp :
        MeasureTheory.MeasurePreserving (fun x : E => x - t)
          (volume : Measure E) (volume : Measure E) :=
      MeasureTheory.measurePreserving_sub_right (μ := (volume : Measure E)) t
    exact (hmp.quasiMeasurePreserving.ae_eq_comp hF_ae)
  -- TranslateL2 gives `F(x - t)` a.e.
  have htrans :
      ((translateL2 (μ := (volume : Measure E)) (-t)) F : E → ℝ) =ᵐ[(volume : Measure E)]
        fun x => (F : E → ℝ) (x - t) := by
    simpa [sub_eq_add_neg] using (translateL2_ae_eq (μ := (volume : Measure E)) (-t) F)
  have htrans' :
      ((translateL2 (μ := (volume : Measure E)) (-t)) F : E → ℝ) =ᵐ[(volume : Measure E)]
        fun x => f (x - t) := by
    exact htrans.trans hF_shift
  have hdiff :
      (fun x => ((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x) =ᵐ[(volume : Measure E)]
        fun x => f (x - t) - f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub ((translateL2 (μ := (volume : Measure E)) (-t)) F) F,
      htrans', hF_ae] with x hxsub hx1 hx2
    -- `Lp.coeFn_sub` gives the pointwise relation between coercions of `Lp` subtraction.
    have hxsub' :
        ((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x =
          ((translateL2 (μ := (volume : Measure E)) (-t)) F) x - F x := by
      simpa using hxsub
    -- Rewrite to the desired expression using the two pointwise identities.
    rw [hxsub', hx1, hx2]
  have hcalc :
      ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 =
        ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E) := by
    have h1 :=
      norm_sq_eq_integral_sq (E := E) (v := ((translateL2 (μ := (volume : Measure E)) (-t)) F - F))
    have h2 :
        ∫ x, (((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x) ^ 2
            ∂(volume : Measure E) =
          ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E) := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hdiff.pow_const 2
    exact h1.trans h2
  simpa [F, f] using hcalc

lemma kernelMeasure_le_smul_volume (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ kernelMeasure (E := E) ψ ≤ c • (volume : Measure E) := by
  classical
  obtain ⟨C, hC⟩ := hψcs.exists_bound_of_continuous hψc
  refine ⟨ENNReal.ofReal C, by simp, ?_⟩
  refine (Measure.le_iff).2 ?_
  intro s hs
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (ψ 0)) (hC 0)
  have hψle : ∀ x, ENNReal.ofReal (ψ x) ≤ ENNReal.ofReal C := by
    intro x
    have hx : ψ x ≤ C := by
      have hx' : ‖ψ x‖ ≤ C := hC x
      -- `ψ ≥ 0`, so `‖ψ x‖ = ψ x`.
      simpa [Real.norm_eq_abs, abs_of_nonneg (hψ0 x)] using hx'
    exact ENNReal.ofReal_le_ofReal hx
  -- Unfold `withDensity` and bound the density by the constant `ENNReal.ofReal C`.
  simp [kernelMeasure, MeasureTheory.withDensity_apply, hs]
  have hle :
      (∫⁻ x in s, ENNReal.ofReal (ψ x) ∂(volume : Measure E)) ≤
        ∫⁻ x in s, ENNReal.ofReal C ∂(volume : Measure E) := by
    refine MeasureTheory.lintegral_mono ?_
    intro x
    exact hψle x
  refine hle.trans ?_
  simp

lemma smoothFun_sub_extendByZeroFun_sq_le_integral_sq
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    (smoothFun (E := E) (K := K) ψ u x - extendByZeroFun (E := E) (K := K) u x) ^ 2 ≤
      ∫ t,
        (extendByZeroFun (E := E) (K := K) u (x - t) - extendByZeroFun (E := E) (K := K) u x) ^ 2
          ∂kernelMeasure (E := E) ψ := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    instIsProbabilityMeasure_kernelMeasure (E := E) (ψ := ψ) hψc hψcs hψ0 hψint
  haveI : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  rcases kernelMeasure_le_smul_volume (E := E) (ψ := ψ) hψc hψcs hψ0 with ⟨c, hc_top, hμle⟩
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  have hf_vol : MeasureTheory.MemLp f (2 : ℝ≥0∞) (volume : Measure E) := by
    -- Use the `L²` packaging of `extendByZeroFun` and the AE bridge.
    let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
    have hF : MeasureTheory.MemLp (fun x : E => (F : E → ℝ) x) (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp F
    have hF_ae : (fun x : E => (F : E → ℝ) x) =ᵐ[(volume : Measure E)] f :=
      extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
    exact (MeasureTheory.memLp_congr_ae hF_ae).1 hF
  have hmp :
      MeasureTheory.MeasurePreserving (fun t : E => x - t)
        (volume : Measure E) (volume : Measure E) := by
    -- `t ↦ x - t = (-t) + x` is measure-preserving for Lebesgue (Haar) measure.
    have hneg :
        MeasureTheory.MeasurePreserving (Neg.neg : E → E)
          (volume : Measure E) (volume : Measure E) :=
      (volume : Measure E).measurePreserving_neg
    have hadd :
        MeasureTheory.MeasurePreserving (fun y : E => y + x)
          (volume : Measure E) (volume : Measure E) :=
      MeasureTheory.measurePreserving_add_right
        (μ := (volume : Measure E)) x
    have h := hadd.comp hneg
    convert h using 1
    funext t
    simp [sub_eq_add_neg, add_comm]
  have hf_shift_vol :
      MeasureTheory.MemLp (fun t : E => f (x - t))
        (2 : ℝ≥0∞) (volume : Measure E) :=
    hf_vol.comp_measurePreserving hmp
  have hf_shift :
      MeasureTheory.MemLp (fun t : E => f (x - t))
        (2 : ℝ≥0∞) μ := by
    exact MeasureTheory.MemLp.of_measure_le_smul
      (μ := (volume : Measure E)) (μ' := μ) (c := c)
      hc_top hμle hf_shift_vol
  have hf_const : MeasureTheory.MemLp (fun _ : E => f x) (2 : ℝ≥0∞) μ :=
    MeasureTheory.memLp_const (μ := μ) (c := f x)
  have hg : MeasureTheory.MemLp (fun t : E => f (x - t) - f x) (2 : ℝ≥0∞) μ :=
    hf_shift.sub hf_const
  have hsmooth :
      smoothFun (E := E) (K := K) ψ u x = ∫ t, f (x - t) ∂μ := by
    simpa [μ, f] using smoothFun_eq_integral_kernelMeasure (E := E) (K := K) (ψ := ψ) hψc hψ0 u x
  have hdiff :
      smoothFun (E := E) (K := K) ψ u x - f x = ∫ t, (f (x - t) - f x) ∂μ := by
    have hconst : (∫ _t : E, f x ∂μ) = f x := by
      simp [MeasureTheory.integral_const]
    have hint : MeasureTheory.Integrable (fun t : E => f (x - t)) μ :=
      hf_shift.integrable (by norm_num)
    have :
        (∫ t, f (x - t) ∂μ) - (∫ _t : E, f x ∂μ) =
          ∫ t, (f (x - t) - f x) ∂μ := by
      simpa using (MeasureTheory.integral_sub hint (MeasureTheory.integrable_const (f x))).symm
    simpa [hsmooth, hconst] using this
  -- Apply Jensen/variance inequality to `t ↦ f(x - t) - f(x)`.
  have hJ :=
    sq_integral_le_integral_sq_of_isProbabilityMeasure
      (μ := μ) (f := fun t : E => f (x - t) - f x) hg
  simpa [hdiff, μ, f] using hJ

lemma norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 ≤
      ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) (extendByZeroL2 (E := E) (K := K) hKm u)
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
          ∂kernelMeasure (E := E) ψ := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    instIsProbabilityMeasure_kernelMeasure (E := E) (ψ := ψ) hψc hψcs hψ0 hψint
  haveI : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  haveI : MeasureTheory.SFinite μ := by infer_instance
  let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  let S : (E →₂[(volume : Measure E)] ℝ) := smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
  have hS_ae :
      (S : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
    smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
  have hF_ae : (F : E → ℝ) =ᵐ[(volume : Measure E)] f :=
    extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
  have hSF_ae :
      (fun x : E => (S - F) x) =ᵐ[(volume : Measure E)] fun x =>
        smoothFun (E := E) (K := K) ψ u x - f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub S F, hS_ae, hF_ae] with x hxsub hxS hxF
    have hxsub' : (S - F) x = S x - F x := by
      simpa using hxsub
    rw [hxsub', hxS, hxF]
  have hnorm_sq :
      ‖S - F‖ ^ 2 =
        ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) := by
    have h1 := norm_sq_eq_integral_sq (E := E) (v := (S - F))
    have h2 :
        (∫ x, ((S - F) x) ^ 2 ∂(volume : Measure E)) =
          ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hSF_ae.pow_const 2
    exact h1.trans h2
  have hLHS_int :
      MeasureTheory.Integrable (fun x : E => (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2)
        (volume : Measure E) := by
    have hv_mem : MeasureTheory.MemLp (fun x : E => (S - F : E →₂[(volume : Measure E)] ℝ) x)
        (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp (S - F)
    have hv_int :
        MeasureTheory.Integrable
          (fun x : E => ‖(S - F : E →₂[(volume : Measure E)] ℝ) x‖ ^ (2 : ℕ))
          (volume : Measure E) :=
      MeasureTheory.MemLp.integrable_norm_pow (μ := (volume : Measure E)) (f := fun x =>
        (S - F : E →₂[(volume : Measure E)] ℝ) x) (p := 2) hv_mem (by decide)
    -- Replace `‖·‖^2` by `(_)^2` in `ℝ`, then transport along the AE equality.
    have hv_sq :
        MeasureTheory.Integrable (fun x : E => ((S - F : E →₂[(volume : Measure E)] ℝ) x) ^ 2)
          (volume : Measure E) := by
      simpa [Real.norm_eq_abs, sq_abs] using hv_int
    exact hv_sq.congr (hSF_ae.pow_const 2)
  -- Show integrability on the product measure, so we can use Fubini/Tonelli for the translation
  -- error.
  let h : E × E → ℝ := fun z => (f (z.1 - z.2) - f z.1) ^ 2
  have hf_mem : MeasureTheory.MemLp f (2 : ℝ≥0∞) (volume : Measure E) := by
    -- Again use the AE bridge from the `L²` packaging.
    have hF : MeasureTheory.MemLp (fun x : E => (F : E → ℝ) x) (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp F
    exact (MeasureTheory.memLp_congr_ae hF_ae).1 hF
  have hf_sq_int : MeasureTheory.Integrable (fun x : E => (f x) ^ 2) (volume : Measure E) := by
    have hf_int :
        MeasureTheory.Integrable (fun x : E => ‖f x‖ ^ (2 : ℕ)) (volume : Measure E) :=
      MeasureTheory.MemLp.integrable_norm_pow
        (μ := (volume : Measure E)) (f := f) (p := 2)
        hf_mem (by decide)
    simpa [Real.norm_eq_abs, sq_abs] using hf_int
  have hfst_map :
      MeasureTheory.Integrable (fun x : E => (f x) ^ 2)
        (Measure.map Prod.fst ((volume : Measure E).prod μ)) := by
    simpa [Measure.map_fst_prod] using hf_sq_int
  have hf_fst_sq_prod :
      MeasureTheory.Integrable (fun z : E × E => (f z.1) ^ 2) ((volume : Measure E).prod μ) :=
    (MeasureTheory.Integrable.comp_measurable (μ := (volume : Measure E).prod μ) (f := Prod.fst)
      (g := fun x : E => (f x) ^ 2) hfst_map measurable_fst)
  have hsub :
      MeasureTheory.MeasurePreserving
        (fun z : E × E => (z.1 - z.2, z.2))
        ((volume : Measure E).prod μ)
        ((volume : Measure E).prod μ) :=
    MeasureTheory.measurePreserving_sub_prod (μ := (volume : Measure E)) (ν := μ)
  have hf_shift_sq_prod :
      MeasureTheory.Integrable (fun z : E × E => (f (z.1 - z.2)) ^ 2)
        ((volume : Measure E).prod μ) := by
    have := (hsub.integrable_comp hf_fst_sq_prod.aestronglyMeasurable).2 hf_fst_sq_prod
    exact this
  have hdom :
      MeasureTheory.Integrable (fun z : E × E => (2 : ℝ) * ((f (z.1 - z.2)) ^ 2 + (f z.1) ^ 2))
        ((volume : Measure E).prod μ) := by
    simpa [mul_add, two_mul] using (hf_shift_sq_prod.add hf_fst_sq_prod).const_mul (2 : ℝ)
  have hf_fst_aesm :
      MeasureTheory.AEStronglyMeasurable (fun z : E × E => f z.1)
        ((volume : Measure E).prod μ) := by
    have hf_map :
        MeasureTheory.AEStronglyMeasurable f
          (Measure.map Prod.fst
            ((volume : Measure E).prod μ)) := by
      simpa [Measure.map_fst_prod] using hf_mem.1
    exact MeasureTheory.AEStronglyMeasurable.comp_measurable
      (μ := (volume : Measure E).prod μ) (f := Prod.fst)
      (g := f) hf_map measurable_fst
  have hf_shift_aesm :
      MeasureTheory.AEStronglyMeasurable
        (fun z : E × E => f (z.1 - z.2))
        ((volume : Measure E).prod μ) := by
    have := MeasureTheory.AEStronglyMeasurable.comp_measurePreserving (g := fun z : E × E => f z.1)
      hf_fst_aesm hsub
    exact this
  have h_aesm :
      MeasureTheory.AEStronglyMeasurable h ((volume : Measure E).prod μ) := by
    -- Build up AE-strong measurability from the two components.
    have hsub' :
        MeasureTheory.AEStronglyMeasurable (fun z : E × E => f (z.1 - z.2) - f z.1)
          ((volume : Measure E).prod μ) :=
      hf_shift_aesm.sub hf_fst_aesm
    exact (hsub'.pow 2)
  have hint_h : MeasureTheory.Integrable h ((volume : Measure E).prod μ) := by
    refine MeasureTheory.Integrable.mono (μ := (volume : Measure E).prod μ) hdom h_aesm ?_
    refine Filter.Eventually.of_forall ?_
    rintro ⟨x, t⟩
    have hineq :
        (f (x - t) - f x) ^ 2 ≤ (2 : ℝ) * ((f (x - t)) ^ 2 + (f x) ^ 2) := by
      -- `(a - b)^2 ≤ 2(a^2 + b^2)` as a special case of `add_sq_le`.
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (add_sq_le (a := f (x - t)) (b := -f x))
    have hnonneg : 0 ≤ (f (x - t) - f x) ^ 2 := by nlinarith
    have hsum_nonneg : 0 ≤ (f (x - t)) ^ 2 + (f x) ^ 2 := by nlinarith
    simpa [h, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_mul,
      abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num),
      abs_of_nonneg hsum_nonneg] using hineq
  have hRHS_int :
      MeasureTheory.Integrable
        (fun x : E => ∫ t, (f (x - t) - f x) ^ 2 ∂μ) (volume : Measure E) := by
    simpa [h] using hint_h.integral_prod_left
  have hpoint :
      (fun x : E => (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2)
        ≤ᶠ[MeasureTheory.ae (volume : Measure E)]
        fun x : E => ∫ t, (f (x - t) - f x) ^ 2 ∂μ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simpa [f, μ] using
      (smoothFun_sub_extendByZeroFun_sq_le_integral_sq (E := E) (K := K) (ψ := ψ)
        hψc hψcs hψ0 hψint hKm u x)
  have hinterm :
      ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) ≤
        ∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E) :=
    MeasureTheory.integral_mono_ae hLHS_int hRHS_int hpoint
  -- Swap the order of integration on the right-hand side.
  have hswap :
      (∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E)) =
        ∫ t, (∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) ∂μ := by
    simpa using (MeasureTheory.integral_integral_swap (μ := (volume : Measure E)) (ν := μ)
      (f := fun x t => (f (x - t) - f x) ^ 2) hint_h)
  -- Identify the inner `x` integral with the `L²` translation norm squared.
  have hinner :
      (fun t : E => ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) =
        fun t : E =>
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 := by
    funext t
    -- Use the previously proved integral identity.
    simpa [F, f] using
      (norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq
        (E := E) (K := K) (hKm := hKm) t u).symm
  have hRHS_rewrite :
      (∫ t, (∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) ∂μ) =
        ∫ t, ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ∂μ := by
    simp [hinner]
  -- Assemble everything.
  have hmain :
      ‖S - F‖ ^ 2 ≤
        ∫ t, ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ∂μ := by
    -- Convert `‖S-F‖²` to an `x`-integral and apply the integral inequality chain.
    have : ‖S - F‖ ^ 2 ≤ ∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E) := by
      simpa [hnorm_sq] using hinterm
    exact this.trans_eq (hswap.trans hRHS_rewrite)
  -- Restore the original statement.
  simpa [S, F, μ] using hmain


end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness
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
# `L²` compactness criterion: compact smoothing operator (Euclidean)

This file proves the compactness of the fixed-kernel smoothing operator used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main results

- `Kψ`: the compact set `K + tsupport ψ` controlling supports of smoothed functions.
- `smoothBCF`: `smoothFun` packaged as a `BoundedContinuousFunction` on `Kψ`.
- `uniformContinuous_ψ`: `UniformContinuous ψ` from `Continuous ψ` + `HasCompactSupport ψ`.

The Arzelà–Ascoli compactness statement for `smoothBCF` lives in
`RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli`.

This is tracked under Beads `lean-103.5.2.26.5.3.2.2.1`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessCompactness : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessCompactness : BorelSpace E := ⟨rfl⟩

variable {K : Set E}
variable {ψ : E → ℝ}

/-- The natural compact codomain for smoothing on `K` by a compactly supported kernel `ψ`. -/
def Kψ : Set E :=
  K + tsupport ψ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma isCompact_Kψ (hK : IsCompact K) (hψcs : HasCompactSupport ψ) :
    IsCompact (Kψ (K := K) (ψ := ψ)) :=
  IsCompact.add hK hψcs.isCompact

local instance instOpensMeasurableSpaceE_L2CompactnessCompactness_re7c677_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_L2CompactnessCompactness_re7c677_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_L2CompactnessCompactness_re7c677_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
def smoothOn (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    C(↥(Kψ (K := K) (ψ := ψ)), ℝ) where
  toFun x := smoothFun (E := E) (K := K) ψ u x
  continuous_toFun := by
    have : Continuous (smoothFun (E := E) (K := K) ψ u) :=
      continuous_smoothFun (E := E) (K := K) (ψ := ψ) (hKm := hKm) hψc hψcs u
    exact this.comp continuous_subtype_val

/-- `smoothFun` packaged as a `BoundedContinuousFunction` on the compact set `K + tsupport ψ`. -/
def smoothBCF (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ :=
  letI : CompactSpace ↥(Kψ (K := K) (ψ := ψ)) :=
    isCompact_iff_compactSpace.1 (isCompact_Kψ (K := K) (ψ := ψ) hK hψcs)
  BoundedContinuousFunction.mkOfCompact (smoothOn (E := E) (K := K) (ψ := ψ) hKm hψc hψcs u)

@[simp] lemma smoothBCF_apply (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (x : ↥(Kψ (K := K) (ψ := ψ))) :
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x =
      smoothFun (E := E) (K := K) ψ u x := by
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma uniformContinuous_ψ (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) :
    UniformContinuous ψ := by
  classical
  -- `HasCompactSupport` implies `ψ = 0` outside a compact set, hence `ψ → 0` along `cocompact`.
  refine
    Continuous.uniformContinuous_of_tendsto_cocompact (f := ψ) (x := (0 : ℝ)) hψc ?_
  -- Show `ψ → 0` along `cocompact` using the `ε`-ball characterization.
  refine (Metric.tendsto_nhds.2 ?_)
  intro ε hε
  refine Filter.mem_cocompact'.mpr ⟨tsupport ψ, hψcs, ?_⟩
  intro x hx
  -- If `ψ x` is `ε`-far from `0`, then `ψ x ≠ 0`, hence `x` belongs to the support and therefore
  -- to the topological support.
  have hx' : ¬ dist (ψ x) 0 < ε := by
    simpa [Set.mem_compl_iff, Set.mem_setOf_eq] using hx
  have hxε : ε ≤ dist (ψ x) 0 := le_of_not_gt (by simpa [gt_iff_lt] using hx')
  have hx0 : ψ x ≠ 0 := by
    intro hψ0
    have : dist (ψ x) 0 = 0 := by simp [hψ0]
    have : ε ≤ 0 := by simpa [this] using hxε
    exact not_lt_of_ge this hε
  have hx_supp : x ∈ Function.support ψ := by
    simpa [Function.support] using hx0
  have hx_tsupp : x ∈ tsupport ψ := by
    have : x ∈ closure (Function.support ψ) := subset_closure hx_supp
    simpa [tsupport] using this
  exact hx_tsupp

/-!
The remainder of the compactness proof (Arzelà–Ascoli on the family `smoothBCF '' closedBall`)
is tracked as part of `lean-103.5.2.26.5.3.2.2.1`.

We intentionally keep the helper lemmas above in this file so the final proof can stay short and
only reference re-usable bounds.
-/

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_ArzelaAscoli
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
# `L²` compactness criterion: Arzelà–Ascoli for the smoothing operator (Euclidean)

This file proves the Arzelà–Ascoli step for the compact smoothing operator used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main result

- `smoothBCF_image_closedBall_isCompact`:
  For a compact set `K` and a continuous compactly supported kernel `ψ`, the family
  `{ smoothFun ψ u | ‖u‖ ≤ R }` restricted to the compact set `K + tsupport ψ`
  has compact closure in `BoundedContinuousFunction`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.1.1`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessArzelaAscoli : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessArzelaAscoli : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessArzelaAscoli : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable {K : Set E} {ψ : E → ℝ}

local instance instMeasurableAddE_L2CompactnessArzelaAscoli_re7c677_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_L2CompactnessArzelaAscoli_re7c677_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
lemma smoothFun_eq_integral_restrict (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    smoothFun (E := E) (K := K) ψ u x =
      ∫ t, u t * ψ (x - t) ∂(volume.restrict K) := by
  classical
  -- Unfold convolution, then restrict the integral using the indicator defining `extendByZeroFun`.
  have :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (extendByZeroFun (E := E) (K := K) u t) • ψ (x - t) ∂(volume : Measure E) := by
    simp [smoothFun, MeasureTheory.convolution_lsmul]
  have h_ind :
      (fun t : E => extendByZeroFun (E := E) (K := K) u t * ψ (x - t)) =
        K.indicator (fun t : E => u t * ψ (x - t)) := by
    funext t
    by_cases ht : t ∈ K <;> simp [extendByZeroFun, ht]
  -- Restrict to `K` using the indicator.
  simp [this, h_ind, MeasureTheory.integral_indicator hKm]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma isCompact_diffSet (hK : IsCompact K) (hψcs : HasCompactSupport ψ) :
    IsCompact
      ((fun p : E × E => p.1 - p.2) '' ((Kψ (K := K) (ψ := ψ)) ×ˢ K)) := by
  have hKψ : IsCompact (Kψ (K := K) (ψ := ψ)) := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hprod : IsCompact ((Kψ (K := K) (ψ := ψ)) ×ˢ K) := hKψ.prod hK
  refine hprod.image ?_
  exact (continuous_fst.sub continuous_snd)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma exists_norm_ψ_bound_on_diffSet (hK : IsCompact K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ↥(Kψ (K := K) (ψ := ψ)), ∀ t : E, t ∈ K → ‖ψ ((x : E) - t)‖ ≤ C := by
  classical
  let diffSet : Set E :=
    (fun p : E × E => p.1 - p.2) '' ((Kψ (K := K) (ψ := ψ)) ×ˢ K)
  have hdiff : IsCompact diffSet := isCompact_diffSet (E := E) (K := K) (ψ := ψ) hK hψcs
  by_cases hne : diffSet.Nonempty
  · -- Use the extreme value theorem on the continuous function `z ↦ ‖ψ z‖`.
    have hcont : Continuous (fun z : E => ‖ψ z‖) := hψc.norm
    rcases hdiff.exists_isMaxOn hne (hcont.continuousOn) with ⟨z0, hz0, hzmax⟩
    refine ⟨‖ψ z0‖, norm_nonneg _, ?_⟩
    intro x t ht
    have hx : (x : E) ∈ Kψ (K := K) (ψ := ψ) := x.2
    have hx_t : (x : E) - t ∈ diffSet := by
      refine ⟨((x : E), t), ?_, rfl⟩
      exact ⟨hx, ht⟩
    exact (isMaxOn_iff.1 hzmax) _ hx_t
  · -- `diffSet = ∅`: take the trivial bound.
    refine ⟨0, le_rfl, ?_⟩
    intro x t ht
    exfalso
    have hx : (x : E) ∈ Kψ (K := K) (ψ := ψ) := x.2
    have : (x : E) - t ∈ diffSet := by
      refine ⟨((x : E), t), ?_, rfl⟩
      exact ⟨hx, ht⟩
    exact hne ⟨(x : E) - t, this⟩

/-- Arzelà--Ascoli: smoothing maps `L²(K)` bounded sets into a precompact set
in `BCF(K + tsupport ψ)`. -/
theorem smoothBCF_image_closedBall_isCompact (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact
        (closure
          (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' Metric.closedBall (0 : _)
            R)) := by
  classical
  -- Radius `0`: the image is a singleton, hence compact.
  by_cases hR0 : R = 0
  · subst hR0
    have hball :
        Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) 0 = {0} := by
      ext u
      simp
    -- Reduce to a singleton.
    simp [hball]
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    -- Compactness of the codomain.
    letI : CompactSpace ↥(Kψ (K := K) (ψ := ψ)) :=
      isCompact_iff_compactSpace.1 (isCompact_Kψ (K := K) (ψ := ψ) hK hψcs)
    let A :
        Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
    -- `volume.restrict K` is finite since `K` is compact.
    have hμK : (volume : Measure E) K < ∞ := hK.measure_lt_top (μ := (volume : Measure E))
    letI : Fact ((volume : Measure E) K < ∞) := ⟨hμK⟩
    haveI : IsFiniteMeasure (volume.restrict K) := by
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    let μ : Measure E := (volume : Measure E).restrict K
    let mK : ℝ :=
      (MeasureTheory.measureUnivNNReal (volume.restrict K)) ^ ((2 : ℝ≥0∞).toReal⁻¹)
    have hmK : 0 ≤ mK := by
      have : 0 ≤ (MeasureTheory.measureUnivNNReal (volume.restrict K)) := by simp
      exact Real.rpow_nonneg this _
    -- Uniform bound on `ψ` over the relevant compact difference set.
    obtain ⟨Cψ, hCψ_nonneg, hψ_bound⟩ :=
      exists_norm_ψ_bound_on_diffSet (E := E) (K := K) (ψ := ψ) hK hψc hψcs
    -- A compact ball controlling all values.
    let s : Set ℝ := Metric.closedBall (0 : ℝ) (R * (mK * Cψ))
    have hs : IsCompact s := by
      simpa [s] using isCompact_closedBall (0 : ℝ) (R * (mK * Cψ))
    -- Pointwise compact range: each function in `A` takes values in `s`.
    have in_s :
        ∀ (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) (x : ↥(Kψ (K := K) (ψ := ψ))),
          f ∈ A → f x ∈ s := by
      intro f x hfA
      rcases hfA with ⟨u, hu_ball, rfl⟩
      have hu_norm : ‖u‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
      -- Build the `L²(K)` kernel element.
      have hker :
          MemLp (fun t : E => ψ ((x : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
        refine MemLp.of_bound (μ := (volume.restrict K))
          (hf := (hψc.aestronglyMeasurable.comp_measurable
            (measurable_const.sub measurable_id))) Cψ ?_
        filter_upwards
          [MeasureTheory.ae_restrict_mem
            (μ := (volume : Measure E)) hKm] with t ht
        exact hψ_bound x t ht
      let kx : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
        hker.toLp (fun t : E => ψ ((x : E) - t))
      have hkx_norm : ‖kx‖ ≤ mK * Cψ := by
        have h_ae :
            ∀ᵐ t ∂(volume.restrict K), ‖(fun t : E => ψ ((x : E) - t)) t‖ ≤ Cψ := by
          filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm] with t ht
          exact hψ_bound x t ht
        have := (MeasureTheory.Lp.norm_le_of_ae_bound
          (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
          (f := kx) (hC := hCψ_nonneg) (by
            -- transport the bound through the `toLp` representative
            filter_upwards [h_ae,
              MeasureTheory.MemLp.coeFn_toLp
                (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
                (f := fun t : E => ψ ((x : E) - t))
                hker] with t ht hrep
            simpa [kx, hrep] using ht))
        simpa [mK] using this
      -- Express the smoothing value as an `L²` inner product, then apply Cauchy–Schwarz.
      have hsmooth :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            ∫ t, u t * kx t ∂(volume.restrict K) := by
        have h_ae :
            (fun t : E => u t * kx t) =ᵐ[volume.restrict K] fun t : E => u t * ψ ((x : E) - t) := by
          filter_upwards [MeasureTheory.MemLp.coeFn_toLp
            (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
            (f := fun t : E => ψ ((x : E) - t))
            hker] with t ht
          simp [kx, ht]
        -- rewrite `smoothFun` as an integral on `volume.restrict K`
        rw [smoothFun_eq_integral_restrict
          (E := E) (K := K) (ψ := ψ) (hKm := hKm) u (x : E)]
        exact (MeasureTheory.integral_congr_ae h_ae.symm)
      have hsmooth' :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            ∫ t, kx t * u t ∂(volume.restrict K) := by
        simp [hsmooth, mul_comm]
      have hinner :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx := by
        erw [MeasureTheory.L2.inner_def]; exact hsmooth'
      have habs :
          |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ ‖u‖ * ‖kx‖ := by
        simpa [hinner] using
          (abs_real_inner_le_norm (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx)
      have habs' : |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ R * (mK * Cψ) := by
        calc
          |smoothFun (E := E) (K := K) ψ u (x : E)|
              ≤ ‖u‖ * ‖kx‖ := habs
          _ ≤ R * (mK * Cψ) := by
            exact mul_le_mul hu_norm hkx_norm (norm_nonneg _) hR
      have : dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x) 0 ≤ R * (mK * Cψ) := by
        simpa [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x,
          dist_eq_norm, Real.norm_eq_abs] using habs'
      simpa [s, Metric.mem_closedBall, dist_eq_norm] using this
    -- Equicontinuity for `A`.
    have H' : UniformEquicontinuous ((↑) : A → ↥(Kψ (K := K) (ψ := ψ)) → ℝ) := by
      rw [Metric.uniformEquicontinuous_iff]
      intro ε hε
      -- Handle the zero-measure case separately (then `mK = 0` and everything is constant).
      by_cases hmK0 : mK = 0
      · refine ⟨1, by norm_num, ?_⟩
        intro x y _ f
        -- With `mK = 0`, the range bound forces all values to be `0`.
        have hx0 : dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x) 0 ≤
            R * (mK * Cψ) := by
          have :
              (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x ∈ s :=
            in_s (f := (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ)) x f.property
          simpa [s, Metric.mem_closedBall] using this
        have hy0 : dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y) 0 ≤
            R * (mK * Cψ) := by
          have :
              (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y ∈ s :=
            in_s (f := (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ)) y f.property
          simpa [s, Metric.mem_closedBall] using this
        have hx0' :
            dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x) 0 = 0 := by
          have : dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x) 0 ≤ 0 := by
            simpa [hmK0] using hx0
          exact le_antisymm this dist_nonneg
        have hy0' :
            dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y) 0 = 0 := by
          have : dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y) 0 ≤ 0 := by
            simpa [hmK0] using hy0
          exact le_antisymm this dist_nonneg
        have hx : (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x = 0 :=
          dist_eq_zero.1 hx0'
        have hy : (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y = 0 :=
          dist_eq_zero.1 hy0'
        simpa [hx, hy] using hε
      · have hRmK_ne : R * mK ≠ 0 := mul_ne_zero hR0 hmK0
        let ε2 : ℝ := ε / 2
        have hε2pos : 0 < ε2 := by
          simpa [ε2] using half_pos hε
        let ε' : ℝ := ε2 / (R * mK)
        have hε'pos : 0 < ε' :=
          div_pos hε2pos (mul_pos hRpos (lt_of_le_of_ne hmK (Ne.symm hmK0)))
        have hε'lt : R * mK * ε' = ε2 := by
          dsimp [ε']
          field_simp [hRmK_ne, mul_assoc, mul_left_comm, mul_comm]
        -- Use uniform continuity of `ψ` to get `δ`.
        have hUC : UniformContinuous ψ := uniformContinuous_ψ (E := E) (ψ := ψ) hψc hψcs
        rcases (Metric.uniformContinuous_iff.1 hUC) ε' hε'pos with ⟨δ, hδpos, hδ⟩
        refine ⟨δ, hδpos, ?_⟩
        intro x y hxy f
        -- Work with the `smoothBCF` representative of `f`.
        rcases f.property with ⟨u, hu_ball, hu_eq⟩
        have hu_eq' :
            (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) =
              smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u := by
          simpa using hu_eq.symm
        have hu_norm : ‖u‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
        -- Kernel elements at `x` and `y`.
        have hkerx :
            MemLp (fun t : E => ψ ((x : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
          refine MemLp.of_bound (μ := (volume.restrict K))
            (hf := (hψc.aestronglyMeasurable.comp_measurable
              (measurable_const.sub measurable_id))) Cψ ?_
          filter_upwards
            [MeasureTheory.ae_restrict_mem
              (μ := (volume : Measure E)) hKm] with t ht
          exact hψ_bound x t ht
        have hkery :
            MemLp (fun t : E => ψ ((y : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
          refine MemLp.of_bound (μ := (volume.restrict K))
            (hf := (hψc.aestronglyMeasurable.comp_measurable
              (measurable_const.sub measurable_id))) Cψ ?_
          filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm] with t ht
          exact hψ_bound y t ht
        let kx : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
          hkerx.toLp (fun t : E => ψ ((x : E) - t))
        let ky : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
          hkery.toLp (fun t : E => ψ ((y : E) - t))
        -- AE bound on `‖kx - ky‖` by `ε'`.
        have h_ae :
            ∀ᵐ t ∂(volume.restrict K), ‖(kx - ky) t‖ ≤ ε' := by
          filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm,
            MeasureTheory.MemLp.coeFn_toLp (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
              (f := fun t : E => ψ ((x : E) - t)) hkerx,
            MeasureTheory.MemLp.coeFn_toLp (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
              (f := fun t : E => ψ ((y : E) - t)) hkery,
            (MeasureTheory.Lp.coeFn_sub (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞)) kx ky)] with
            t ht hx_t hy_t hsub
          have hxy' : dist ((x : E) - t) ((y : E) - t) < δ := by
            simpa [sub_eq_add_neg, add_assoc, Subtype.dist_eq] using hxy
          have hψxy : dist (ψ ((x : E) - t)) (ψ ((y : E) - t)) < ε' :=
            hδ (a := (x : E) - t) (b := (y : E) - t) hxy'
          have : ‖ψ ((x : E) - t) - ψ ((y : E) - t)‖ ≤ ε' := by
            simpa [dist_eq_norm, sub_eq_add_neg] using le_of_lt hψxy
          have hx' : kx t = ψ ((x : E) - t) := by simpa [kx] using hx_t
          have hy' : ky t = ψ ((y : E) - t) := by simpa [ky] using hy_t
          have hnorm : ‖kx t - ky t‖ ≤ ε' := by
            simpa [hx', hy'] using this
          have hsub' : (kx - ky) t = kx t - ky t := by
            simpa [Pi.sub_apply] using hsub
          simpa [hsub'.symm] using hnorm
        have hkdiff : ‖kx - ky‖ ≤ mK * ε' := by
          have := (MeasureTheory.Lp.norm_le_of_ae_bound (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
            (f := (kx - ky : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ)) (hC := le_of_lt hε'pos) h_ae)
          simpa [mK, mul_comm, mul_left_comm, mul_assoc] using this
        -- Bound the difference of values using Cauchy–Schwarz.
        have hdist :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
              ≤ ‖u‖ * ‖kx - ky‖ := by
          -- Express each value as an inner product.
          have hx_val :
              smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x =
                inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx := by
            have hsmooth :
                smoothFun (E := E) (K := K) ψ u (x : E) =
                  ∫ t, u t * kx t ∂(volume.restrict K) := by
              have h_ae' :
                  (fun t : E => u t * kx t) =ᵐ[volume.restrict K]
                    fun t : E => u t * ψ ((x : E) - t) := by
                filter_upwards [MeasureTheory.MemLp.coeFn_toLp
                  (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
                  (f := fun t : E => ψ ((x : E) - t))
                  hkerx] with t ht
                simp [kx, ht]
              rw [smoothFun_eq_integral_restrict
                (E := E) (K := K) (ψ := ψ) (hKm := hKm)
                u (x : E)]
              exact (MeasureTheory.integral_congr_ae h_ae'.symm)
            have hsmooth' :
                smoothFun (E := E) (K := K) ψ u (x : E) =
                  ∫ t, kx t * u t ∂(volume.restrict K) := by
              simp [hsmooth, mul_comm]
            erw [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x,
              MeasureTheory.L2.inner_def]; exact hsmooth'
          have hy_val :
              smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y =
                inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) ky := by
            have hsmooth :
                smoothFun (E := E) (K := K) ψ u (y : E) =
                  ∫ t, u t * ky t ∂(volume.restrict K) := by
              have h_ae' :
                  (fun t : E => u t * ky t) =ᵐ[volume.restrict K]
                    fun t : E => u t * ψ ((y : E) - t) := by
                filter_upwards [MeasureTheory.MemLp.coeFn_toLp
                  (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
                  (f := fun t : E => ψ ((y : E) - t))
                  hkery] with t ht
                simp [ky, ht]
              rw [smoothFun_eq_integral_restrict
                (E := E) (K := K) (ψ := ψ) (hKm := hKm)
                u (y : E)]
              exact (MeasureTheory.integral_congr_ae h_ae'.symm)
            have hsmooth' :
                smoothFun (E := E) (K := K) ψ u (y : E) =
                  ∫ t, ky t * u t ∂(volume.restrict K) := by
              simp [hsmooth, mul_comm]
            erw [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y,
              MeasureTheory.L2.inner_def]; exact hsmooth'
          have :
              ‖smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x -
                  smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y‖ ≤
                ‖u‖ * ‖kx - ky‖ := by
            have :
                smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x -
                    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y =
                  inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky) := by
              simp [hx_val, hy_val, inner_sub_right]
            have this' :
                smoothFun (E := E) (K := K) ψ u (x : E) - smoothFun (E := E) (K := K) ψ u (y : E) =
                  inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky) := by
              simpa [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs] using this
            have hCS :=
              (abs_real_inner_le_norm (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky))
            simpa [this', dist_eq_norm, Real.norm_eq_abs] using hCS
          simpa [dist_eq_norm] using this
        have hle :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
              ≤ R * (mK * ε') := by
          calc
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
                ≤ ‖u‖ * ‖kx - ky‖ := hdist
            _ ≤ ‖u‖ * (mK * ε') := by
              exact mul_le_mul_of_nonneg_left hkdiff (norm_nonneg _)
            _ ≤ R * (mK * ε') := by
              have hmKε' : 0 ≤ mK * ε' := mul_nonneg hmK (le_of_lt hε'pos)
              exact mul_le_mul_of_nonneg_right hu_norm hmKε'
        have hRmkε' : R * (mK * ε') = ε2 := by
          have : R * mK * ε' = ε2 := by
            simpa [ε', mul_assoc] using hε'lt
          simpa [mul_assoc] using this
        have hle' :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y) ≤ ε2 := by
          simpa [hRmkε'] using hle
        have hε2lt : ε2 < ε := by
          simpa [ε2] using half_lt_self hε
        have :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y) < ε :=
          lt_of_le_of_lt hle' hε2lt
        simpa [hu_eq'] using this
    have H : Equicontinuous ((↑) : A → ↥(Kψ (K := K) (ψ := ψ)) → ℝ) := H'.equicontinuous
    -- Apply Arzelà–Ascoli.
    simpa [A, s] using
      (BoundedContinuousFunction.arzela_ascoli (α := ↥(Kψ (K := K) (ψ := ψ))) (β := ℝ)
        (s := s) hs A (fun f x hf => in_s f x hf) H)

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer
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
# `L²` compactness criterion: transfer from `BCF` compactness to `L²` (Euclidean)

This file transfers the Arzelà–Ascoli compactness of the `BoundedContinuousFunction` packaging of
`smoothFun` on the compact set `K + tsupport ψ` to a compactness statement in `L²(volume)`.

## Main results

- `smoothL2_image_closedBall_isCompact`:
  For a compact set `K` and a continuous compactly supported kernel `ψ`, the family
  `{ smoothL2 ψ u | ‖u‖ ≤ R }` has compact closure in `L²(volume)`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.1.2`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessTransfer : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessTransfer : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessTransfer : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
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
# `L²` compactness criterion: Fréchet–Kolmogorov (Euclidean, compact support case)

This file packages the final “precompactness via smoothing” step behind the Euclidean `L²`
compactness criterion used by the Rellich–Kondrachov stack:

- the **smoothing operator** `smoothL2 ψ` has compact image on `Metric.closedBall 0 R`;
- the **approximation inequality** bounds `‖smoothL2 ψ u - extendByZeroL2 u‖` by a translation
  error.

We state the criterion at the level needed by the project: families of `L²` functions with common
compact support (modeled as `Lp ℝ 2 (volume.restrict K)` and embedded into `L²(volume)` via
`extendByZeroL2`).

## Main results

- `norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le`:
  if the translation error averaged against `kernelMeasure ψ` is ≤ `η²`, then smoothing approximates
  `extendByZeroL2` within `η`.
- `totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small`:
  if a bounded family admits, at every scale `ε`, a kernel `ψ` for which the above translation error
  is uniformly small, then the embedded family is totally bounded in `L²(volume)`.
- `isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small`:
  the corresponding compact-closure statement.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.3`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessFrechetKolmogorov : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessFrechetKolmogorov : BorelSpace E := ⟨rfl⟩

variable {K : Set E} {ψ : E → ℝ}

local instance instOpensMeasurableSpaceE_L2CompactnessFrechetKolmogorov_re7c677_1 :
    OpensMeasurableSpace E := by infer_instance
local instance instMeasurableAddE_L2CompactnessFrechetKolmogorov_re7c677_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_L2CompactnessFrechetKolmogorov_re7c677_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
lemma norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
    (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) {η : ℝ} (hη : 0 ≤ η)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (htrans :
      ∫ t,
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (extendByZeroL2 (E := E) (K := K) hKm u)
              - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
        ∂kernelMeasure (E := E) ψ ≤ η ^ 2) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ η := by
  have hsq :
      ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 ≤ η ^ 2 := by
    refine (le_trans ?_ htrans)
    simpa using
      norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
        (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs hψ0 hψint u
  exact (sq_le_sq₀ (norm_nonneg _) hη).1 hsq

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
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
# `L²` compactness criterion: existence of small-support probability kernels (Euclidean)

This file provides a “kernel factory” for the Euclidean Fréchet–Kolmogorov / Riesz–Kolmogorov
criterion: for any radius `δ > 0`, produce a continuous compactly supported function `ψ : E → ℝ`
such that:

- `ψ ≥ 0`,
- `tsupport ψ ⊆ Metric.ball 0 δ`,
- `∫ ψ = 1` (so `kernelMeasure ψ` is a probability measure).

The construction uses mathlib’s `exists_smooth_tsupport_subset` bump-function lemma and normalizes
by its (positive) integral.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.5`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessKernels : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessKernels : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessKernels : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

/-- For any `δ > 0`, there exists a continuous compactly supported kernel `ψ` supported in
`Metric.ball 0 δ`, with `ψ ≥ 0` and `∫ ψ = 1` (w.r.t. Lebesgue measure). -/
theorem exists_kernel_tsupport_subset_ball_integral_eq_one {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∫ x, ψ x ∂(volume : Measure E) = 1) ∧ tsupport ψ ⊆ Metric.ball (0 : E) δ := by
  classical
  -- Start from a smooth bump supported in `ball 0 δ` with value `1` at `0`.
  have hs : (Metric.ball (0 : E) δ) ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hδ
  rcases exists_contDiff_tsupport_subset (n := ⊤)
    (E := E) (s := Metric.ball (0 : E) δ) (x := (0 : E)) hs with
    ⟨f, hf_tsupp, hf_cs, hf_smooth, hf_range, hf0⟩
  have hf_cont : Continuous f := hf_smooth.continuous
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    have hx : f x ∈ Set.Icc (0 : ℝ) 1 := hf_range ⟨x, rfl⟩
    exact hx.1
  have hf0_ne : f (0 : E) ≠ 0 := by
    -- `f 0 = 1`.
    simp [hf0]
  -- The integral is strictly positive (Lebesgue is an open-positive measure).
  have hIpos :
      0 < ∫ x, f x ∂(volume : Measure E) := by
    simpa using
      (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure E))
        hf_cont hf_cs hf_nonneg hf0_ne)
  set I : ℝ := ∫ x, f x ∂(volume : Measure E)
  have hI0 : I ≠ 0 := ne_of_gt hIpos
  have hIpos' : 0 < I := by simpa [I] using hIpos
  -- Normalize: `ψ = I⁻¹ • f`.
  let ψ : E → ℝ := fun x => I⁻¹ * f x
  have hψc : Continuous ψ := by
    exact continuous_const.mul hf_cont
  have hψcs : HasCompactSupport ψ := by
    exact
      (HasCompactSupport.smul_left (f := fun _x : E => I⁻¹) (f' := f) hf_cs)
  have hψ0 : ∀ x, 0 ≤ ψ x := by
    intro x
    have hInv : 0 ≤ I⁻¹ := by
      have : 0 ≤ I := le_of_lt hIpos'
      simpa using inv_nonneg.2 this
    simpa [ψ] using mul_nonneg hInv (hf_nonneg x)
  have hψint : ∫ x, ψ x ∂(volume : Measure E) = 1 := by
    have : (∫ x, ψ x ∂(volume : Measure E)) = I⁻¹ * I := by
      -- Pull out the constant scalar.
      simpa [ψ, I] using
        (MeasureTheory.integral_const_mul (μ := (volume : Measure E)) (r := I⁻¹) (f := f))
    simp [this, hI0]
  have hψ_tsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ := by
    -- Scaling does not enlarge topological support; use the bump support inclusion.
    have hsub : tsupport ψ ⊆ tsupport f := by
      simpa [ψ, smul_eq_mul] using (tsupport_smul_subset_right (f := fun _x : E => I⁻¹) (g := f))
    exact hsub.trans hf_tsupp
  exact ⟨ψ, hψc, hψcs, hψ0, hψint, hψ_tsupp⟩

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
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
# `L²` compactness criterion: bounding the translation-integral by a translation modulus

This file provides a small but crucial bridge lemma used to connect a uniform translation modulus
on `L²(volume)` with the `kernelMeasure` translation-integral bound appearing in the
approximation-identity estimate.

The core observation is that if `ψ` is supported in a neighborhood where the translation modulus is
≤ `η`, then the averaged squared translation error against the probability measure
`kernelMeasure ψ` is ≤ `η²`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.4`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessTranslationIntegral : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessTranslationIntegral : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessTranslationIntegral :
    OpensMeasurableSpace E := by infer_instance

variable {ψ : E → ℝ}

local instance instMeasurableAddE_L2CompactnessTranslationIntegral_re7c677_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_L2CompactnessTranslationIntegral_re7c677_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
lemma kernelMeasure_compl_ball_eq_zero_of_tsupport_subset {δ : ℝ}
    (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ) :
    kernelMeasure (E := E) ψ ((Metric.ball (0 : E) δ)ᶜ) = 0 := by
  classical
  have hψzero : ∀ x : E, x ∈ (Metric.ball (0 : E) δ)ᶜ → ψ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ψ := by
      intro hx_ts
      exact hx (hψsupp hx_ts)
    exact image_eq_zero_of_notMem_tsupport (f := ψ) hx'
  have hmeas : MeasurableSet ((Metric.ball (0 : E) δ)ᶜ) :=
    (measurableSet_ball : MeasurableSet (Metric.ball (0 : E) δ)).compl
  have hEq :
      Set.EqOn (fun x : E => ENNReal.ofReal (ψ x)) 0 ((Metric.ball (0 : E) δ)ᶜ) := by
    intro x hx
    simp [hψzero x hx]
  -- Expand `kernelMeasure` and note the density is identically `0` on the set.
  simp [kernelMeasure, MeasureTheory.withDensity_apply, hmeas,
    MeasureTheory.setLIntegral_eq_zero
      (μ := (volume : Measure E))
      (s := (Metric.ball (0 : E) δ)ᶜ) hmeas hEq]

theorem integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    {δ η : ℝ} (hη : 0 ≤ η) (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ)
    (F : (E →₂[(volume : Measure E)] ℝ))
    (hmod :
      ∀ t : E, t ∈ Metric.ball (0 : E) δ →
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η) :
    ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
      ∂kernelMeasure (E := E) ψ ≤ η ^ 2 := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    ⟨kernelMeasure_univ (E := E) (ψ := ψ) hψc hψcs hψ0 hψint⟩
  have hμzero : μ ((Metric.ball (0 : E) δ)ᶜ) = 0 := by
    simpa [μ] using kernelMeasure_compl_ball_eq_zero_of_tsupport_subset (E := E) (ψ := ψ) hψsupp
  have hAE_ball : (Metric.ball (0 : E) δ) ∈ MeasureTheory.ae μ :=
    (MeasureTheory.mem_ae_iff.2 hμzero)
  -- On `Metric.ball 0 δ`, the squared translation error is bounded by `η²`.
  have hAE_bound :
      ∀ᵐ t : E ∂μ,
        ‖‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2‖ ≤ η ^ 2 := by
    filter_upwards [hAE_ball] with t ht
    have hle : ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η := hmod t ht
    have hsq :
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ≤ η ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hη).2 hle
    have hnonneg : 0 ≤ ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 :=
      sq_nonneg _
    have hηnonneg : 0 ≤ η ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hηnonneg] using hsq
  have hnorm_int :
      ‖∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ‖ ≤ η ^ 2 * μ.real Set.univ := by
    simpa using
      (MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun t : E => ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2)
        (C := η ^ 2) hAE_bound)
  have hμreal : μ.real Set.univ = 1 := by
    -- `μ` is a probability measure.
    simp [MeasureTheory.measureReal_def]
  have hnonneg_int :
      0 ≤ ∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ := by
    refine MeasureTheory.integral_nonneg ?_
    intro t
    exact sq_nonneg _
  -- Use `|∫ f| = ∫ f` for a nonnegative integrand.
  have habs :
      |∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ| ≤ η ^ 2 := by
    have := hnorm_int
    -- Replace `‖·‖` by `abs` in `ℝ` and simplify `μ.real univ = 1`.
    simpa [Real.norm_eq_abs, hμreal, mul_one] using this
  simpa [abs_of_nonneg hnonneg_int, μ] using habs

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate
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
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimate`

Pointwise translation estimates for `C¹_c` functions on Euclidean spaces.

This file provides the key analytic inequality used later in the Euclidean Rellich step:
translation differences are controlled by the `L²`-gradient.

At this stage we only prove *pointwise* inequalities along the segment `t ↦ x + t • a`.
The measure-theoretic lifting to `L²` is tracked separately under `lean-103.5.2.26.5.3.2.3`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance instMeasurableSpaceE_SobolevEuclideanTranslationEstimate :
    MeasurableSpace E := borel E
local instance instBorelSpaceE_SobolevEuclideanTranslationEstimate :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslationEstimate :
    OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

/-! ## Derivative along a translated line -/

/-- The affine line `t ↦ x + t • a`. -/
def line (x a : E) (t : ℝ) : E :=
  x + t • a

lemma hasDerivAt_line (x a : E) (t : ℝ) :
    HasDerivAt (line (x := x) (a := a)) a t := by
  -- `t ↦ t • a` has derivative `a`, and adding the constant `x` preserves the derivative.
  have hsmul : HasDerivAt (fun t : ℝ => t • a) a t := by
    simpa [one_smul] using (hasDerivAt_id t).smul_const a
  exact HasDerivAt.const_add x hsmul

lemma hasDerivAt_comp_line
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    HasDerivAt (fun t => f (line (x := x) (a := a) t))
      (fderiv ℝ f (line (x := x) (a := a) t) a) t := by
  have hf' : HasFDerivAt f (fderiv ℝ f (line (x := x) (a := a) t)) (line (x := x) (a := a) t) :=
    (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  exact
    HasFDerivAt.comp_hasDerivAt_of_eq t hf' (hasDerivAt_line (x := x) (a := a) t) rfl

lemma deriv_comp_line {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    deriv (fun t => f (line (x := x) (a := a) t)) t =
      fderiv ℝ f (line (x := x) (a := a) t) a :=
  (hasDerivAt_comp_line (hf := hf) (x := x) (a := a) t).deriv

/-! ## Pointwise translation bound via the gradient -/

section

variable [CompleteSpace E]

lemma enorm_fderiv_apply_le_enorm_grad_mul (f : E → ℝ) (x a : E) :
    ‖fderiv ℝ f x a‖ₑ ≤ ‖grad (E := E) f x‖ₑ * ‖a‖ₑ := by
  -- Use the operator norm bound, then identify `‖fderiv‖` with `‖grad‖` via the Riesz isometry.
  have h₁ :
      ‖fderiv ℝ f x a‖ₑ ≤ ‖fderiv ℝ f x‖ₑ * ‖a‖ₑ :=
    (ContinuousLinearMap.le_opNorm_enorm (f := fderiv ℝ f x) a)
  have h₂ : ‖grad (E := E) f x‖ₑ = ‖fderiv ℝ f x‖ₑ := by
    -- `grad f x = (toDual).symm (fderiv f x)` and `toDual.symm` is an isometry.
    simpa [grad] using
      (LinearIsometry.enorm_map
        (f := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry)
        (fderiv ℝ f x))
  -- Replace the operator norm by the gradient norm.
  simpa [h₂, mul_assoc, mul_left_comm, mul_comm] using h₁

lemma enorm_deriv_comp_line_le (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ‖deriv (fun t => f (line (x := x) (a := a) t)) t‖ₑ ≤
      ‖a‖ₑ * ‖grad (E := E) f (line (x := x) (a := a) t)‖ₑ := by
  -- Reduce to the `fderiv` bound.
  have :=
    enorm_fderiv_apply_le_enorm_grad_mul
      (E := E) (f := f) (x := line (x := x) (a := a) t) (a := a)
  -- Rewrite `deriv` and commute the product.
  simpa [deriv_comp_line (hf := hf) (x := x) (a := a) t,
    mul_comm, mul_left_comm, mul_assoc] using this

lemma enorm_sub_le_enorm_mul_lintegral_grad (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ‖f (x + a) - f x‖ₑ ≤
      ‖a‖ₑ * ∫⁻ t in Icc (0 : ℝ) 1, ‖grad (E := E) f (x + t • a)‖ₑ := by
  -- Apply FTC along the segment `t ↦ x + t • a`, then bound the derivative pointwise.
  have hCont :
      ContDiffOn ℝ 1 (fun t : ℝ => f (x + t • a)) (Icc (0 : ℝ) 1) := by
    -- `t ↦ x + t • a` is `C^∞`; compose with `f`.
    have hInner : ContDiff ℝ ⊤ (fun t : ℝ => x + t • a) := by
      simpa [line] using
        (contDiff_const.add (contDiff_id.smul (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => a))))
    have hInner' : ContDiff ℝ 1 (fun t : ℝ => x + t • a) := hInner.of_le (by first | simp | exact_mod_cast le_top)
    exact (hf.comp hInner').contDiffOn
  have hFTC :
      ‖f (x + a) - f x‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ := by
    simpa using
      (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (f := fun t : ℝ => f (x + t • a))
        (a := (0 : ℝ)) (b := 1) hCont (by exact zero_le_one))
  refine hFTC.trans ?_
  have hDerivBound :
      (fun t : ℝ => ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ)
        ≤ᵐ[Measure.restrict volume (Icc (0 : ℝ) 1)]
          fun t : ℝ => ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    -- Pointwise bound holds everywhere.
    refine (ae_of_all _ fun t => ?_)
    -- `deriv` along `t ↦ x + t•a` is controlled by the gradient.
    simpa [line, mul_assoc, mul_left_comm, mul_comm] using
      (enorm_deriv_comp_line_le (x := x) (a := a) (f := f) hf (t := t))
  -- Pull out the constant `‖a‖ₑ`.
  have :
      (∫⁻ t in Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ) ≤
        ∫⁻ t in Icc (0 : ℝ) 1, ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    exact lintegral_mono_ae hDerivBound
  refine this.trans ?_
  -- Pull out the constant factor.
  have hMeas :
      Measurable fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ := by
    -- `grad f` is continuous when `f` is `C¹`.
    have hgradCont : Continuous (grad (E := E) f) := continuous_grad (E := E) (f := f) (by
      -- `ContDiff` gives continuity of `grad`.
      exact hf)
    -- hence `t ↦ grad f (x + t•a)` is measurable; take `enorm`.
    exact (hgradCont.comp (by
      have : Continuous (fun t : ℝ => x + t • a) := by
        fun_prop
      exact this)).measurable.enorm
  -- Now finish: `∫⁻ t in Icc, ‖a‖ * g t = ‖a‖ * ∫⁻ t in Icc, g t`.
  exact le_of_eq <| by
    simpa [mul_assoc] using
      (MeasureTheory.lintegral_const_mul (μ := volume.restrict (Icc (0 : ℝ) 1)) (r := ‖a‖ₑ)
        (f := fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ) hMeas)

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2
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
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2`

`L²` translation estimates for Euclidean `C¹_c` functions (and derived `H¹`) under invariant
measures.

This file lifts the pointwise fundamental-theorem-of-calculus bound from
`Euclidean.TranslationEstimate` to an `L²` bound using Tonelli and the measure-preserving property
of translations.

## Main results

- `enorm_translateL2_sub_toL2_le`: for `f ∈ C¹_c`, `‖τ_a f - f‖₂ ≤ ‖a‖ · ‖∇f‖₂` (as an `ℝ≥0∞`
  inequality on `L²` norms), under a right-invariant measure.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceE_SobolevEuclideanTranslationEstimateL2 :
    MeasurableSpace E := borel E
local instance instBorelSpaceE_SobolevEuclideanTranslationEstimateL2 :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslationEstimateL2 :
    OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_SobolevEuclideanTranslationEstimateL2 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

abbrev μI : Measure ℝ := (volume.restrict (Icc (0 : ℝ) 1))

lemma holderConj_two_two : (2 : ℝ).HolderConjugate (2 : ℝ) := by
  refine (Real.holderConjugate_iff).2 ?_
  constructor
  · linarith
  · norm_num

lemma lintegral_rpow_two_le_lintegral_rpow_two
    {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g (μI : Measure ℝ)) :
    (∫⁻ t, g t ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤ ∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
  -- Hölder with `g * 1` gives `∫ g ≤ (∫ g^2)^(1/2) * (∫ 1^2)^(1/2)`.
  have hHolder :
      (∫⁻ t, g t ∂(μI : Measure ℝ)) ≤
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ _t : ℝ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [Pi.mul_apply] using
      (ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := (μI : Measure ℝ)) holderConj_two_two
        hg (aemeasurable_const : AEMeasurable (fun _t : ℝ => (1 : ℝ≥0∞)) (μI : Measure ℝ)))
  have h1 : (∫⁻ _t : ℝ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) = (1 : ℝ≥0∞) := by
    -- `μI` has total mass `1`, and `1^2 = 1`.
    simp
  have h :
      (∫⁻ t, g t ∂(μI : Measure ℝ)) ≤
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [h1, mul_one] using hHolder
  -- Raise to the power `2` and simplify `((A)^(1/2))^2 = A`.
  have h' :=
    ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  -- Rewrite the RHS using `rpow_mul`.
  simpa [ENNReal.rpow_mul] using (h'.trans_eq (by
    have : (1 / (2 : ℝ)) * (2 : ℝ) = (1 : ℝ) := by norm_num
    simpa [this] using
      (ENNReal.rpow_mul
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ))
        (1 / (2 : ℝ)) (2 : ℝ)).symm))

/-- `L²` translation estimate for `C¹_c` functions under a right-invariant measure. -/
lemma enorm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ₑ ≤
      ‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ := by
  classical
  -- Reduce to an `eLpNorm` inequality on representatives.
  have hL2 :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
          toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => (f.1 (x + a) - f.1 x)) (2 : ℝ≥0∞) μ := by
    -- Both terms agree a.e. with the underlying pointwise translation.
    have h₁ :
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) := by
      have hf :
          (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
        (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
      have hf' :
          (fun x => (toL2 (μ := μ) (E := E) f : E → ℝ) (x + a)) =ᵐ[μ] fun x => f.1 (x + a) := by
        exact
          (Measure.QuasiMeasurePreserving.ae_eq_comp
            (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
      exact (translateL2_ae_eq (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f)).trans hf'
    have h₂ : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] fun x => f.1 x :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hsub :
        ((translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
              toL2 (μ := μ) (E := E) f : E →₂[μ] ℝ) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) - f.1 x := by
      filter_upwards [Lp.coeFn_sub
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f))
        (toL2 (μ := μ) (E := E) f), h₁, h₂] with x hxsub hx1 hx2
      simpa [hx1, hx2, Pi.sub_apply] using hxsub
    -- Convert the `Lp` norm to `eLpNorm` and rewrite using a.e. equality.
    let d : E →₂[μ] ℝ :=
      translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) - toL2 (μ := μ) (E := E) f
    have hd0 : (‖d‖ₑ : ℝ≥0∞) = MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have hd1 :
        MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) (by simpa [d] using hsub)
    simpa [d] using hd0.trans hd1
  have hGrad :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    have h₁ :
        (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] fun x => grad (E := E) f.1 x :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have h0 :
        (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
          MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have h1 :
        MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) h₁
    exact h0.trans h1
  -- Prove the `eLpNorm` inequality by squaring, using Tonelli and measure-preserving translation.
  have hCore :
      MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ ≤
        ‖a‖ₑ * MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    -- Expand the definition of `eLpNorm` at exponent `2`.
    have h2_ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
    have h2_netop : (2 : ℝ≥0∞) ≠ ∞ := by simp
    simp_rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      h2_ne0 h2_netop, ENNReal.toReal_ofNat] at *
    -- It suffices to compare the squared integrals.
    have hsq :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
          ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
      -- Pointwise: Cauchy–Schwarz in `t`, then Tonelli in `(x,t)`.
      have hpt :
          ∀ x : E,
            ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
              ‖a‖ₑ ^ (2 : ℝ) *
                ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
        intro x
        have h0 := enorm_sub_le_enorm_mul_lintegral_grad (E := E) (x := x) (a := a) (f := f.1)
          (hf := f.2.1)
        -- Square both sides and apply Cauchy–Schwarz in `t`.
        have h1 :
            ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
              (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
          exact ENNReal.rpow_le_rpow h0 (by norm_num)
        have hcs :
            (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤
              ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
          refine lintegral_rpow_two_le_lintegral_rpow_two (g := fun t : ℝ =>
            ‖grad (E := E) f.1 (x + t • a)‖ₑ) ?_
          -- measurability from continuity of `grad`.
          have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
          have hline : Continuous fun t : ℝ => x + t • a := by
            fun_prop
          exact (hgrad.comp hline).measurable.enorm.aemeasurable
        -- Combine and rewrite.
        calc
          ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ)
              ≤ (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := h1
          _ = ‖a‖ₑ ^ (2 : ℝ) *
              (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
                ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
              simpa using
                (ENNReal.mul_rpow_of_nonneg ‖a‖ₑ
                  (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
                    ∂(μI : Measure ℝ))
                  (show (0 : ℝ) ≤ (2 : ℝ) by norm_num))
          _ ≤ ‖a‖ₑ ^ (2 : ℝ) *
              ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
                ∂(μI : Measure ℝ) := by
              gcongr
          _ = ‖a‖ₑ ^ (2 : ℝ) *
              ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
                ∂(μI : Measure ℝ) := rfl
      -- Integrate over `x` and apply Tonelli to swap integrals.
      let F : E × ℝ → ℝ≥0∞ :=
        fun z => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ ^ (2 : ℝ)
      have hmeas :
          AEMeasurable
            F (μ.prod (μI : Measure ℝ)) := by
        have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
        have hcont : Continuous fun z : E × ℝ => z.1 + z.2 • a := by
          fun_prop
        have hbase : Measurable fun z : E × ℝ => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ := by
          exact (hgrad.comp hcont).measurable.enorm
        have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
          (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
        exact (hpow.comp hbase).aemeasurable
      have hTonelli :
          (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) =
            ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
        -- Tonelli in both orders, via the product measure.
        have hprod :
            (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
              ∫⁻ x, ∫⁻ t, F (x, t) ∂(μI : Measure ℝ) ∂μ :=
          MeasureTheory.lintegral_prod (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
        have hprod_symm :
            (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
              ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) :=
          MeasureTheory.lintegral_prod_symm (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
        calc
          (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ)
              = ∫⁻ z, F z ∂μ.prod (μI : Measure ℝ) := by
                  simpa [F] using hprod.symm
          _ = ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) := hprod_symm
          _ = ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
                  simp [F]
      -- Now use measure-preserving translation in `x` and evaluate the `t`-integral.
      have hShift :
          (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) =
            ∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ) := by
        refine MeasureTheory.lintegral_congr fun t => ?_
        -- Change of variables `x ↦ x + t•a`.
        have hmeas' : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) := by
          have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
          have hbase : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ := hgrad.measurable.enorm
          have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
            (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
          exact hpow.comp hbase
        simpa [Function.comp, add_assoc] using
          (MeasureTheory.measurePreserving_add_right μ (t • a)).lintegral_comp (μ := μ) (ν := μ)
            (f := fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ)) hmeas'
      have hEval :
          (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) =
            (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
        -- `μI` has total mass `1`.
        simp [μI, Measure.restrict_apply, Real.volume_Icc]
      -- Put everything together.
      have hInt :
          (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
            ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
        calc
          (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ)
              ≤ ∫⁻ x, ‖a‖ₑ ^ (2 : ℝ) *
                    ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ := by
                refine MeasureTheory.lintegral_mono ?_
                intro x
                exact hpt x
          _ = ‖a‖ₑ ^ (2 : ℝ) *
                (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) := by
                -- Pull out the constant using `lintegral_const_mul''`.
                have hInner :
                    AEMeasurable
                      (fun x : E =>
                        ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) μ := by
                  -- Measurability of the inner integral follows
                  -- from `hmeas` via
                  -- `AEMeasurable.lintegral_prod_right'`.
                  simpa [F] using (hmeas.lintegral_prod_right' (μ := μ) (ν := (μI : Measure ℝ)))
                simpa [mul_assoc] using
                  (MeasureTheory.lintegral_const_mul'' (μ := μ) (r := ‖a‖ₑ ^ (2 : ℝ))
                    (f := fun x : E =>
                      ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) hInner)
          _ = ‖a‖ₑ ^ (2 : ℝ) *
                (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) := by
                exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hTonelli
          _ = ‖a‖ₑ ^ (2 : ℝ) *
                (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) := by
                exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hShift
          _ = ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
                exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hEval
      exact hInt
    -- Take the `1/2` power on both sides and simplify.
    have hsq' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ) * ∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      exact ENNReal.rpow_le_rpow hsq (by norm_num)
    -- Rewrite the RHS as `‖a‖ * (...)^(1/2)`.
    have hsq'' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      simpa [ENNReal.mul_rpow_of_nonneg, show (0 : ℝ) ≤ (1 / (2 : ℝ)) by nlinarith,
        mul_assoc, mul_left_comm, mul_comm] using hsq'
    have hroot : (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = ‖a‖ₑ := by
      -- `(x^2)^(1/2) = x` in `ℝ≥0∞`, accounting for simp-normalization of `2` and `1/2`.
      have hnat : (‖a‖ₑ ^ (2 : ℕ)) = ‖a‖ₑ ^ (2 : ℝ) := by
        simp
      calc
        (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = (‖a‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
          congrArg (fun r : ℝ≥0∞ => r ^ ((2 : ℝ)⁻¹)) hnat
        _ = ‖a‖ₑ := by
          have := (ENNReal.rpow_mul ‖a‖ₑ (2 : ℝ) ((2 : ℝ)⁻¹)).symm
          have hmul : (2 : ℝ) * ((2 : ℝ)⁻¹) = (1 : ℝ) := by norm_num
          simpa [hmul, ENNReal.rpow_one] using this
    simpa [hroot, mul_assoc, mul_left_comm, mul_comm] using hsq''
  -- Finish: translate back to the original `L²` norms.
  -- (The final `simp` is safe since we have explicit `eLpNorm` equalities above.)
  simpa [hL2, hGrad] using hCore

/-- Real-norm form of `enorm_translateL2_sub_toL2_le`. -/
lemma norm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ ≤
      ‖a‖ * ‖toL2Grad (μ := μ) (E := E) f‖ := by
  have h := enorm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hA_ne_top :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ ∞ := by
    simp [enorm]
  have hGrad_ne_top :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ ∞ := by
    simp [enorm]
  have hB_ne_top : (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ ∞ := by
    refine ENNReal.mul_ne_top ?_ hGrad_ne_top
    simp [enorm]
  have h' :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ).toReal ≤
        (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ).toReal := by
    exact (ENNReal.toReal_le_toReal hA_ne_top hB_ne_top).2 h
  simpa [ENNReal.toReal_mul, toReal_enorm'] using h'

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
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
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1`

Extend Euclidean `L²` translation estimates from `C¹_c` to the closure-based Euclidean `H¹` space.

## Main results

- `norm_translateL2_sub_h1ToL2_le`: for `u ∈ H¹`, `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂`, where `∇u` is the
  `L²(E)` component in our `H¹ ⊆ L² × L²(E)` model.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceE_SobolevEuclideanTranslationEstimateH1 :
    MeasurableSpace E := borel E

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`

Euclidean Rellich–Kondrachov compactness for fixed compact support (Lebesgue `volume`).

This file discharges the “Euclidean heart” needed by the manifold Rellich glue:
for a fixed compact set `K ⊆ E`, the inclusion `H¹ → L²` is compact when restricted to the closed
subspace of `H¹` whose `L²` component is supported in `K` (a.e.).

The proof uses:

1. the Euclidean `H¹` translation estimate
   `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂` (`TranslationEstimateH1`);
2. the Fréchet–Kolmogorov / smoothing-based `L²` compactness criterion
   (`L2CompactnessCriterion`).

## Main definitions / results

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On`:
  the closed subspace of `H¹(volume)` whose `L²` component is supported in `K` (a.e.).
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2`:
  the restricted inclusion map `h1On K →L[ℝ] L²(volume)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2`:
  compactness of the inclusion.

Tracking: Beads `lean-103.5.2.26.5.3.2.1`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

local instance instMeasurableSpaceE_SobolevEuclideanRellich : MeasurableSpace E := borel E
local instance instBorelSpaceE_SobolevEuclideanRellich : BorelSpace E := ⟨rfl⟩
local instance instFactOneLeTwo_SobolevEuclideanRellich : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ### Supported `H¹` subspace -/

/-! ### Euclidean Rellich on fixed compact support -/

/-!
### Codomain restriction and a compact map into `L²(volume.restrict K)`

The definition of `h1On` forces the image of `h1OnToL2` to lie in the (closed) range of the
extension-by-zero map from `volume.restrict K`. We record a codomain-restricted version and a
convenient compact map to the restricted `L²` space.
-/

end Volume

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_SupportedH1
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
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.SupportedH1`

Supported Euclidean `H¹` subspaces for a general measure.

This file defines the `H¹` subspace of functions whose `L²` component is (a.e.) supported in a
measurable set `K`, modeled as membership in the closed range of the extension-by-zero map
`Lp (μ.restrict K) →ₗᵢ Lp μ`.

These definitions match the volume-specialized `h1On` construction used by
`RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`, but are stated for an
arbitrary measure `μ`. Compactness results are proven elsewhere.

## Main definitions

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnMeasure`
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2Measure`
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [CompleteSpace E]

local instance instMeasurableSpaceE_SobolevEuclideanSupportedH1 : MeasurableSpace E := borel E
local instance instFactOneLeTwo_SobolevEuclideanSupportedH1 : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ## Range characterization for extension-by-zero -/

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ActualJacobiODEExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global solutions of a bounded continuous linear equation, constructed
from Picard–Lindelöf on overlapping intervals. The uniform local time depends
on the operator bound, while the Picard ball may depend on the initial value. -/

namespace PositiveEinsteinFour.Jacobi

open Set Metric
open scoped _root_.Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def LinearCurveOn (A : ℝ → E →L[ℝ] E) (γ : ℝ → E) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, HasDerivAt γ (A t (γ t)) t

theorem linear_uniform_local_solution (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K)
    (ε : ℝ) (hε : 0 < ε) (hsmall : 2 * (K : ℝ) * ε ≤ 1)
    (s : ℝ) (x : E) :
    ∃ γ : ℝ → E, γ s = x ∧ LinearCurveOn A γ (Ioo (s - ε) (s + ε)) := by
  let a : ℝ≥0 := ‖x‖₊ + 1
  let L : ℝ≥0 := 2 * K * a
  let s₀ : Icc (s - ε) (s + ε) := ⟨s, by constructor <;> linarith⟩
  have hlip (t : ℝ) : LipschitzWith K (A t) :=
    (A t).lipschitz.weaken (by exact_mod_cast hK t)
  have hpl : IsPicardLindelof (fun t y => A t y) s₀ x a 0 L K := by
    constructor
    · exact fun t _ => (hlip t).lipschitzOnWith
    · exact fun y _ => (hA.clm_apply continuous_const).continuousOn
    · intro t _ y hy
      have hyx : ‖y - x‖ ≤ (a : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hy
      have hx : ‖x‖ ≤ (a : ℝ) := by dsimp [a]; simp
      have hy' : ‖y‖ ≤ 2 * (a : ℝ) := by
        have h := norm_le_norm_sub_add y x
        linarith
      calc
        ‖A t y‖ ≤ (K : ℝ) * ‖y‖ := (A t).le_of_opNorm_le (hK t) y
        _ ≤ (K : ℝ) * (2 * (a : ℝ)) :=
          mul_le_mul_of_nonneg_left hy' K.coe_nonneg
        _ = (L : ℝ) := by simp only [L, NNReal.coe_mul, NNReal.coe_ofNat]; ring
    · have hleft : s + ε - (s₀ : ℝ) = ε := by dsimp [s₀]; ring
      have hright : (s₀ : ℝ) - (s - ε) = ε := by dsimp [s₀]; ring
      rw [hleft, hright, max_self]
      change (2 * (K : ℝ) * (a : ℝ)) * ε ≤ (a : ℝ) - 0
      nlinarith [mul_le_mul_of_nonneg_right hsmall a.coe_nonneg]
  obtain ⟨γ, hγ0, hγ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨γ, hγ0, fun t ht => ?_⟩
  exact (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

omit [CompleteSpace E] in
theorem LinearCurveOn.mono {A : ℝ → E →L[ℝ] E} {γ : ℝ → E}
    {I J : Set ℝ} (hγ : LinearCurveOn A γ I) (hJI : J ⊆ I) :
    LinearCurveOn A γ J := fun t ht => hγ t (hJI ht)

omit [CompleteSpace E] in
theorem linear_curve_eqOn_interval (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K)
    {γ η : ℝ → E} {a b t : ℝ}
    (hγ : LinearCurveOn A γ (Ioo a b)) (hη : LinearCurveOn A η (Ioo a b))
    (ht : t ∈ Ioo a b) (heq : γ t = η t) : EqOn γ η (Ioo a b) := by
  apply ODE_solution_unique_of_mem_Ioo (s := fun _ => univ)
    (K := K) (v := fun r y => A r y) _ ht _ _ heq
  · intro r _
    exact ((A r).lipschitz.weaken (by exact_mod_cast hK r)).lipschitzOnWith
  · exact fun r hr => ⟨hγ r hr, mem_univ _⟩
  · exact fun r hr => ⟨hη r hr, mem_univ _⟩

omit [CompleteSpace E] in
theorem linear_curve_piecewise (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K)
    {γ η : ℝ → E} {a b c d t : ℝ}
    (hγ : LinearCurveOn A γ (Ioo a b)) (hη : LinearCurveOn A η (Ioo c d))
    (ht : t ∈ Ioo a b ∩ Ioo c d) (heq : γ t = η t) :
    LinearCurveOn A ((Ioo a b).piecewise γ η) (Ioo a b ∪ Ioo c d) := by
  classical
  have hover : EqOn γ η (Ioo (max a c) (min b d)) :=
    linear_curve_eqOn_interval A K hK
      (hγ.mono (Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)))
      (hη.mono (Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)))
      ⟨max_lt ht.1.1 ht.2.1, lt_min ht.1.2 ht.2.2⟩ heq
  have hother : EqOn ((Ioo a b).piecewise γ η) η (Ioo c d) := by
    intro r hr
    by_cases hab : r ∈ Ioo a b
    · rw [piecewise_eq_of_mem _ _ _ hab]
      exact hover ⟨max_lt hab.1 hr.1, lt_min hab.2 hr.2⟩
    · exact piecewise_eq_of_notMem _ _ _ hab
  intro r hr
  by_cases hab : r ∈ Ioo a b
  · have hnear : (Ioo a b).piecewise γ η =ᶠ[𝓝 r] γ := by
      filter_upwards [isOpen_Ioo.mem_nhds hab] with u hu
      exact piecewise_eq_of_mem _ _ _ hu
    have hd := (hγ r hab).congr_of_eventuallyEq hnear
    simpa only [hnear.self_of_nhds] using hd
  · have hcd : r ∈ Ioo c d := hr.resolve_left hab
    have hnear : (Ioo a b).piecewise γ η =ᶠ[𝓝 r] η := by
      filter_upwards [isOpen_Ioo.mem_nhds hcd] with u hu
      exact hother hu
    have hd := (hη r hcd).congr_of_eventuallyEq hnear
    simpa only [hnear.self_of_nhds] using hd

omit [CompleteSpace E] in
theorem extend_linear_curve_interval (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) {ε a : ℝ}
    (hε : 0 < ε) (ha : ε / 2 ≤ a)
    (hlocal : ∀ s x, ∃ γ : ℝ → E, γ s = x ∧
      LinearCurveOn A γ (Ioo (s - ε) (s + ε)))
    {γ : ℝ → E} (hγ : LinearCurveOn A γ (Ioo (-a) a)) :
    ∃ δ : ℝ → E, δ 0 = γ 0 ∧
      LinearCurveOn A δ (Ioo (-(a + ε / 2)) (a + ε / 2)) := by
  classical
  let c := a - ε / 4
  have hc : 0 < c := by dsimp [c]; linarith
  have hca : c < a := by dsimp [c]; linarith
  obtain ⟨L, hL0, hL⟩ := hlocal (-c) (γ (-c))
  obtain ⟨R, hR0, hR⟩ := hlocal c (γ c)
  have htL : -c ∈ Ioo (-a) a ∩ Ioo (-c - ε) (-c + ε) := by
    constructor <;> constructor <;> linarith
  let ψ : ℝ → E := (Ioo (-a) a).piecewise γ L
  have hψ : LinearCurveOn A ψ (Ioo (-(a + ε / 2)) a) := by
    apply (linear_curve_piecewise A K hK hγ hL htL hL0.symm).mono
    intro t ht
    by_cases hta : -a < t
    · exact Or.inl ⟨hta, ht.2⟩
    · right
      constructor <;> dsimp [c] at * <;> linarith [ht.1, ht.2]
  have hψc : ψ c = γ c := piecewise_eq_of_mem _ _ _ ⟨by linarith, hca⟩
  have htR : c ∈ Ioo (-(a + ε / 2)) a ∩ Ioo (c - ε) (c + ε) := by
    constructor <;> constructor <;> linarith
  let δ : ℝ → E := (Ioo (-(a + ε / 2)) a).piecewise ψ R
  refine ⟨δ, ?_, ?_⟩
  · have ha0 : 0 < a := lt_of_lt_of_le (half_pos hε) ha
    simp only [δ, ψ, piecewise,
      ite_eq_left (show (0 : ℝ) ∈ Ioo (-(a + ε / 2)) a from ⟨by linarith, ha0⟩),
      ite_eq_left (show (0 : ℝ) ∈ Ioo (-a) a from ⟨by linarith, ha0⟩)]
  · apply (linear_curve_piecewise A K hK hψ hR htR (hψc.trans hR0.symm)).mono
    intro t ht
    by_cases hta : t < a
    · exact Or.inl ⟨ht.1, hta⟩
    · right
      constructor <;> dsimp [c] at * <;> linarith [ht.1, ht.2]

/-- A continuous globally bounded operator coefficient admits a genuine
global linear solution through every initial value. -/
theorem exists_global_linear_solution (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x : E) :
    ∃ Γ : ℝ → E, Γ 0 = x ∧ ∀ t, HasDerivAt Γ (A t (Γ t)) t := by
  classical
  let ε : ℝ := 1 / (2 * ((K : ℝ) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : 2 * (K : ℝ) * ε ≤ 1 := by
    dsimp [ε]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_one (by positivity)).mpr
    linarith [K.coe_nonneg]
  have hlocal := linear_uniform_local_solution A hA K hK ε hε hsmall
  let r (n : ℕ) : ℝ := ((n : ℝ) + 1) * ε / 2
  have hr (n : ℕ) : ε / 2 ≤ r n := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hmul : 0 ≤ (n : ℝ) * ε := mul_nonneg hn hε.le
    dsimp [r]
    nlinarith
  have hstep (n : ℕ) : r (n + 1) = r n + ε / 2 := by
    simp only [r, Nat.cast_add, Nat.cast_one]
    ring
  have hfam (n : ℕ) : ∃ γ : ℝ → E, γ 0 = x ∧ LinearCurveOn A γ (Ioo (-(r n)) (r n)) := by
    induction n with
    | zero =>
      obtain ⟨γ, h0, hγ⟩ := hlocal 0 x
      refine ⟨γ, h0, hγ.mono ?_⟩
      apply Ioo_subset_Ioo <;> simp only [r, Nat.cast_zero, zero_add, one_mul] <;> linarith
    | succ n ih =>
      obtain ⟨γ, h0, hγ⟩ := ih
      obtain ⟨δ, hδ0, hδ⟩ := extend_linear_curve_interval A K hK hε (hr n) hlocal hγ
      exact ⟨δ, hδ0.trans h0, by simpa only [hstep n] using hδ⟩
  have hinterval (a : ℝ) : ∃ γ : ℝ → E, γ 0 = x ∧ LinearCurveOn A γ (Ioo (-a) a) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (a / (ε / 2))
    have han : a < (n : ℝ) * (ε / 2) := (div_lt_iff₀ (half_pos hε)).mp hn
    have har : a < r n := by dsimp [r]; nlinarith
    obtain ⟨γ, h0, hγ⟩ := hfam n
    exact ⟨γ, h0, hγ.mono (Ioo_subset_Ioo (by linarith) har.le)⟩
  choose γ h0 hγ using hinterval
  have compatible {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      EqOn (γ a) (γ b) (Ioo (-a) a) := by
    apply linear_curve_eqOn_interval A K hK (hγ a)
      ((hγ b).mono (Ioo_subset_Ioo (by linarith) hab))
      (t := 0) ⟨by linarith, ha⟩
    exact (h0 a).trans (h0 b).symm
  let Γ : ℝ → E := fun t => γ (|t| + 1) t
  have hagrees (a : ℝ) (ha : 0 < a) : EqOn Γ (γ a) (Ioo (-a) a) := by
    intro t ht
    have hr' : 0 < |t| + 1 := by positivity
    have htr : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := abs_lt.mp (lt_add_one _)
    rcases le_total a (|t| + 1) with hle | hle
    · exact (compatible ha hle ht).symm
    · exact compatible hr' hle htr
  refine ⟨Γ, h0 (|0| + 1), fun t => ?_⟩
  let a := |t| + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have ht : t ∈ Ioo (-a) a := abs_lt.mp (lt_add_one _)
  have hnear : Γ =ᶠ[𝓝 t] γ a := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hagrees a ha hs
  have hd := (hγ a t ht).congr_of_eventuallyEq hnear
  simpa only [hnear.self_of_nhds] using hd

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DirichletMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite block matrices for the Jacobi determinant approximation. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix OrderDual

noncomputable section

abbrev NormalMatrix := Matrix (Fin 3) (Fin 3) ℝ

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiScheme
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete noncommuting kick-drift scheme and its Jacobi recurrence. -/

namespace PositiveEinsteinFour.Jacobi

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R]

def jacobiScheme (A : ℕ → R) (h : ℝ) : ℕ → R × R
  | 0 => (0, 1)
  | n + 1 =>
      let z := jacobiScheme A h n
      let w := z.2 - h • (A n * z.1)
      (z.1 + h • w, w)

def discretePosition (A : ℕ → R) (h : ℝ) (n : ℕ) : R := (jacobiScheme A h n).1

def discreteVelocity (A : ℕ → R) (h : ℝ) (n : ℕ) : R := (jacobiScheme A h n).2

@[simp] theorem discretePosition_zero (A : ℕ → R) (h : ℝ) :
    discretePosition A h 0 = 0 := rfl

@[simp] theorem discreteVelocity_zero (A : ℕ → R) (h : ℝ) :
    discreteVelocity A h 0 = 1 := rfl

@[simp] theorem discretePosition_one (A : ℕ → R) (h : ℝ) :
    discretePosition A h 1 = h • (1 : R) := by
  simp [discretePosition, jacobiScheme]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarNormalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive scalar normalizer used in finite radial compression. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix
open scoped MatrixOrder

noncomputable section

def scalarNormalizer {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  CFC.sqrt L⁻¹

theorem scalarNormalizer_posSemidef {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) :
    (scalarNormalizer L).PosSemidef := (CFC.sqrt_nonneg L⁻¹).posSemidef

theorem scalarNormalizer_square {N : ℕ} {L : Matrix (Fin N) (Fin N) ℝ} (hL : L.PosDef) :
    scalarNormalizer L * scalarNormalizer L = L⁻¹ :=
  CFC.sqrt_mul_sqrt_self L⁻¹ hL.inv.posSemidef.nonneg

theorem scalarNormalizer_normalizes {N : ℕ} {L : Matrix (Fin N) (Fin N) ℝ} (hL : L.PosDef) :
    scalarNormalizer L * L * scalarNormalizer L = 1 := by
  have hsq := scalarNormalizer_square hL
  have ht : scalarNormalizer L * (scalarNormalizer L * L) = 1 := by
    rw [← Matrix.mul_assoc, hsq,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hL.isUnit)]
  exact mul_eq_one_comm.mp ht

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiSchemeRatios
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact normalized coefficient in a discrete Jacobi pivot. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def relativeDiscretePosition (R : ℕ → NormalMatrix) (h : ℝ) (i : ℕ) : NormalMatrix :=
  if i = 0 then 1 else ((i : ℝ) * h)⁻¹ • discretePosition R h i

@[simp] theorem relativeDiscretePosition_zero (R : ℕ → NormalMatrix) (h : ℝ) :
    relativeDiscretePosition R h 0 = 1 := by simp [relativeDiscretePosition]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiODEPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preconjugate positivity from the Jacobi ODE. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Precisely the local ODE and regularity bounds used by the discretization.
All constants can be chosen on a compact interval of a smooth Jacobi curve. -/
structure RegularJacobi (t : ℝ) where
  R : ℝ → NormalMatrix
  J : ℝ → NormalMatrix
  V : ℝ → NormalMatrix
  K : ℝ
  Lx : ℝ
  Lv : ℝ
  F : ℝ
  K_nonneg : 0 ≤ K
  Lx_nonneg : 0 ≤ Lx
  Lv_nonneg : 0 ≤ Lv
  F_nonneg : 0 ≤ F
  initial_position : J 0 = 0
  initial_velocity : V 0 = 1
  symmetric : ∀ s, (R s)ᵀ = R s
  curvature_bound : ∀ s ∈ Set.Icc 0 t, ‖R s‖ ≤ K
  position_derivative : ∀ s ∈ Set.Icc 0 t, HasDerivAt J (V s) s
  velocity_derivative : ∀ s ∈ Set.Icc 0 t, HasDerivAt V (-(R s * J s)) s
  velocity_lipschitz : ∀ s ∈ Set.Icc 0 t, ∀ r ∈ Set.Icc 0 t,
    ‖V s - V r‖ ≤ Lx * |s - r|
  acceleration_lipschitz : ∀ s ∈ Set.Icc 0 t, ∀ r ∈ Set.Icc 0 t,
    ‖-(R s * J s) - -(R r * J r)‖ ≤ Lv * |s - r|
  force_bound : ∀ s ∈ Set.Icc 0 t, ‖R s * J s‖ ≤ F

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ActualJacobiODEMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix Jacobi equation and its compact-interval regularity bounds.
The coefficient is allowed to vary with time and need not commute with its
values at other times. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix Set
open scoped _root_.Topology NNReal Matrix.Norms.L2Operator

noncomputable section

abbrev JacobiState := NormalMatrix × NormalMatrix

def jacobiStateOperator (R : NormalMatrix) : JacobiState →L[ℝ] JacobiState :=
  (ContinuousLinearMap.snd ℝ NormalMatrix NormalMatrix).prod
    (-((ContinuousLinearMap.mul ℝ NormalMatrix R).comp
      (ContinuousLinearMap.fst ℝ NormalMatrix NormalMatrix)))

theorem jacobiStateOperator_apply (R : NormalMatrix) (p : JacobiState) :
    jacobiStateOperator R p = (p.2, -(R * p.1)) := rfl

theorem continuous_jacobiStateOperator : Continuous jacobiStateOperator := by
  have h : Continuous (fun R : NormalMatrix =>
      -((ContinuousLinearMap.mul ℝ NormalMatrix R).comp
        (ContinuousLinearMap.fst ℝ NormalMatrix NormalMatrix))) := by fun_prop
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
    (continuous_const.prodMk h)

theorem norm_jacobiStateOperator_le (R : NormalMatrix) :
    ‖jacobiStateOperator R‖ ≤ 1 + ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  rw [jacobiStateOperator_apply, Prod.norm_def, Prod.norm_def, norm_neg]
  apply max_le
  · calc
      ‖p.2‖ ≤ max ‖p.1‖ ‖p.2‖ := le_max_right _ _
      _ ≤ (1 + ‖R‖) * max ‖p.1‖ ‖p.2‖ := by
        nlinarith [norm_nonneg R, le_max_left ‖p.1‖ ‖p.2‖, norm_nonneg p.1]
  · calc
      ‖R * p.1‖ ≤ ‖R‖ * ‖p.1‖ := norm_mul_le _ _
      _ ≤ ‖R‖ * max ‖p.1‖ ‖p.2‖ :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
      _ ≤ (1 + ‖R‖) * max ‖p.1‖ ‖p.2‖ := by
        nlinarith [le_max_left ‖p.1‖ ‖p.2‖, norm_nonneg p.1]

structure MatrixJacobiSolution (R : ℝ → NormalMatrix) where
  J : ℝ → NormalMatrix
  V : ℝ → NormalMatrix
  initial_position : J 0 = 0
  initial_velocity : V 0 = 1
  position_derivative : ∀ s, HasDerivAt J (V s) s
  velocity_derivative : ∀ s, HasDerivAt V (-(R s * J s)) s

theorem exists_matrixJacobiSolution (R : ℝ → NormalMatrix) (hR : Continuous R)
    (K : ℝ≥0) (hK : ∀ s, ‖R s‖ ≤ K) :
    Nonempty (MatrixJacobiSolution R) := by
  have hA : Continuous (fun s => jacobiStateOperator (R s)) :=
    continuous_jacobiStateOperator.comp hR
  have hB (s : ℝ) : ‖jacobiStateOperator (R s)‖ ≤ ((1 + K : ℝ≥0) : ℝ) := by
    apply (norm_jacobiStateOperator_le _).trans
    simpa only [NNReal.coe_add, NNReal.coe_one, add_comm] using add_le_add_left (hK s) 1
  obtain ⟨Γ, hΓ0, hΓ⟩ := exists_global_linear_solution _ hA (1 + K) hB
    ((0 : NormalMatrix), (1 : NormalMatrix))
  refine ⟨{
    J := fun s => (Γ s).1
    V := fun s => (Γ s).2
    initial_position := congrArg Prod.fst hΓ0
    initial_velocity := congrArg Prod.snd hΓ0
    position_derivative := fun s => (hΓ s).fst
    velocity_derivative := fun s => (hΓ s).snd }⟩

namespace MatrixJacobiSolution

variable {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)

theorem continuous_J : Continuous d.J :=
  continuous_iff_continuousAt.mpr (fun s => (d.position_derivative s).continuousAt)

theorem continuous_V : Continuous d.V :=
  continuous_iff_continuousAt.mpr (fun s => (d.velocity_derivative s).continuousAt)

/-- Every compact interval has the bounds needed by the discrete Jacobi
comparison. No uniformity in the interval is assumed. -/
theorem exists_regular (R' : ℝ → NormalMatrix) (hR : Continuous R)
    (hR' : Continuous R') (hdR : ∀ s, HasDerivAt R (R' s) s)
    (hsym : ∀ s, (R s)ᵀ = R s) (t : ℝ) :
    ∃ q : RegularJacobi t, q.R = R ∧ q.J = d.J ∧ q.V = d.V := by
  let A : ℝ → NormalMatrix := fun s => -(R s * d.J s)
  let A' : ℝ → NormalMatrix := fun s => -(R' s * d.J s + R s * d.V s)
  have hA : Continuous A := (hR.mul d.continuous_J).neg
  have hA' : Continuous A' :=
    ((hR'.mul d.continuous_J).add (hR.mul d.continuous_V)).neg
  have hdA (s : ℝ) : HasDerivAt A (A' s) s :=
    ((hdR s).mul (d.position_derivative s)).neg
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hR.continuousOn
  obtain ⟨F, hF⟩ := isCompact_Icc.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hA'.continuousOn
  let K₀ := max 0 K
  let F₀ := max 0 F
  let L₀ := max 0 L
  have hbA (s : ℝ) (hs : s ∈ Icc 0 t) : ‖A s‖ ≤ F₀ :=
    (hF s hs).trans (le_max_right _ _)
  have hbA' (s : ℝ) (hs : s ∈ Icc 0 t) : ‖A' s‖ ≤ L₀ :=
    (hL s hs).trans (le_max_right _ _)
  refine ⟨{
    R := R
    J := d.J
    V := d.V
    K := K₀
    Lx := F₀
    Lv := L₀
    F := F₀
    K_nonneg := le_max_left _ _
    Lx_nonneg := le_max_left _ _
    Lv_nonneg := le_max_left _ _
    F_nonneg := le_max_left _ _
    initial_position := d.initial_position
    initial_velocity := d.initial_velocity
    symmetric := hsym
    curvature_bound := fun s hs => (hK s hs).trans (le_max_right _ _)
    position_derivative := fun s _ => d.position_derivative s
    velocity_derivative := fun s _ => d.velocity_derivative s
    velocity_lipschitz := ?_
    acceleration_lipschitz := ?_
    force_bound := ?_ }, rfl, rfl, rfl⟩
  · intro s hs r hr
    simpa only [Real.norm_eq_abs] using
      (convex_Icc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun u _ => (d.velocity_derivative u).hasDerivWithinAt) hbA hr hs
  · intro s hs r hr
    simpa only [A, Real.norm_eq_abs] using
      (convex_Icc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun u _ => (hdA u).hasDerivWithinAt) hbA' hr hs
  · intro s hs
    simpa only [A, norm_neg] using hbA s hs

end MatrixJacobiSolution

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylGeometry
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete orthonormal frames and curvature blocks of the metric in the
classification statement, defined from its chart curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartRicci (g : SmoothMetric M) (c : M) : Mat4 :=
  ricciInChart g c (chartAt FourSpace c c)

namespace OrthonormalFrame

variable {g : SmoothMetric M} {c : M} (e : OrthonormalFrame g c)

theorem det_ne_zero : e.matrix.det ≠ 0 := by
  have h := congrArg Matrix.det e.orthonormal
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  intro hz
  simp [hz] at h

theorem map_apply (u : FourSpace) (i : Fin 4) :
    e.map u i = ∑ j, e.matrix i j * u j := rfl

theorem map_injective : Function.Injective e.map := by
  intro u v h
  apply (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).injective
  apply Matrix.mulVec_injective_of_det_ne_zero e.det_ne_zero
  exact congrArg WithLp.ofLp h

end OrthonormalFrame

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ActualRicciContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction of the actual chart curvature in an orthonormal frame.
This is a finite change-of-basis calculation, used to discharge the Ricci
positivity needed by constant Einstein normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem sum_six_rotate {α : Type*} [Fintype α]
    (f : α → α → α → α → α → α → ℝ) :
    (∑ i, ∑ a, ∑ b, ∑ p, ∑ q, ∑ r, f i a b p q r) =
      ∑ a, ∑ p, ∑ q, ∑ r, ∑ i, ∑ b, f i a b p q r := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ i, ∑ p, ∑ b, ∑ q, ∑ r, f i a b p q r := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ b, ∑ q, ∑ r, f i a b p q r := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      calc
        _ = ∑ i, ∑ q, ∑ b, ∑ r, f i a b p q r := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = ∑ q, ∑ i, ∑ b, ∑ r, f i a b p q r := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro q _
          calc
            _ = ∑ i, ∑ r, ∑ b, f i a b p q r := by
              apply Finset.sum_congr rfl
              intro i _
              exact Finset.sum_comm
            _ = _ := Finset.sum_comm

theorem tensor_trace_basis_change (G E : Mat4)
    (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : ∀ a p, (∑ i, ∑ b, G a b * E p i * E b i) = if a = p then 1 else 0)
    (j k : Fin 4) :
    (∑ i, ∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
      G a b * C a p q r * E p i * E q j * E r k * E b i) =
      ∑ q, ∑ r, E q j * (∑ a, C a a q r) * E r k := by
  rw [sum_six_rotate]
  have hh (a p q r : Fin 4) :
      (∑ i, ∑ b, G a b * C a p q r * E p i * E q j * E r k * E b i) =
        C a p q r * E q j * E r k * (∑ i, ∑ b, G a b * E p i * E b i) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [hh, h]
  simp only [mul_ite, mul_one, mul_zero]
  have hs (a q r : Fin 4) :
      (∑ p, if a = p then C a p q r * E q j * E r k else 0) =
        C a a q r * E q j * E r k := by simp
  have ht (a : Fin 4) :
      (∑ p, ∑ q, ∑ r, if a = p then C a p q r * E q j * E r k else 0) =
        ∑ q, ∑ r, C a a q r * E q j * E r k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_comm]
    simp only [hs]
  simp only [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring


end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise and averaged normal Jacobi curvature form. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

theorem norm_add_half (T U : Fin 3 → Fin 3 → ℝ) :
    (∑ i, ∑ j, ((1 / 2 : ℝ) * (T i j + U i j)) ^ 2) =
      ((∑ i, ∑ j, T i j ^ 2) + (∑ i, ∑ j, U i j ^ 2) +
        2 * (∑ i, ∑ j, T i j * U i j)) / 4 := by
  have hp (i j : Fin 3) : ((1 / 2 : ℝ) * (T i j + U i j)) ^ 2 =
      (T i j ^ 2 + U i j ^ 2 + 2 * (T i j * U i j)) / 4 := by ring
  simp_rw [hp, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem pairing_delta_sum (T U : Fin 3 → Fin 3 → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, T i j * U k l *
      (if i = j then (if k = l then (1 / 3 : ℝ) else 0) else 0)) =
        ((∑ i, T i i) * (∑ k, U k k)) / 3 := by
  simp [mul_ite, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularDerivativeMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite Weyl blocks have zero mixed directional energy. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

/-- Symmetrize a finite contraction against a symmetric matrix. -/
theorem symmetric_contraction (T X : Fin 3 → Fin 3 → ℝ)
    (hT : ∀ i j, T i j = T j i) :
    2 * (∑ i, ∑ j, T i j * X i j) =
      ∑ i, ∑ j, T i j * (X i j + X j i) := by
  have hs : (∑ i, ∑ j, T i j * X j i) = ∑ i, ∑ j, T i j * X i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hT j i]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hs]
  ring

theorem sum4_swap (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := by rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrate the exact angular identity and the classical Weyl equation.
The integrated Weitzenboeck equations are explicit premises; the derivative
energy inequality required by Jacobi comparison is derived from them.
The published input is Gursky--LeBrun (1999), equation (12), p.8 of the
arXiv version math/9807055: integrate that identity with scalar curvature
12 and determinant `2 * sigma * v^3` to obtain the normalization below. -/

namespace PositiveEinsteinFour.Angular

open MeasureTheory Filter Matrix

noncomputable section

variable {B : Type*} [MeasurableSpace B] {μ : Measure B}

theorem cubic_energy_le {v σ : ℝ} (hv : 0 ≤ v) (hv2 : v ≤ 2) (hσ : σ ≤ 1) :
    σ * v ^ 3 - v ^ 2 ≤ v ^ 2 := by
  have hs := mul_le_mul_of_nonneg_right hσ (pow_nonneg hv 3)
  have ht := mul_le_mul_of_nonneg_right hv2 (sq_nonneg v)
  nlinarith

theorem integrated_gradient_energy_le {v σ E : B → ℝ}
    (hv : ∀ᵐ c ∂μ, 0 ≤ v c ∧ v c ≤ 2 ∧ σ c ≤ 1)
    (hvi : Integrable (fun c => v c ^ 2) μ)
    (hci : Integrable (fun c => σ c * v c ^ 3 - v c ^ 2) μ)
    (hweitzenbock : (∫ c, E c ∂μ) =
      36 * (∫ c, σ c * v c ^ 3 - v c ^ 2 ∂μ)) :
    (∫ c, E c ∂μ) ≤ 36 * (∫ c, v c ^ 2 ∂μ) := by
  rw [hweitzenbock]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply integral_mono_ae hci hvi
  filter_upwards [hv] with c hc
  exact cubic_energy_le hc.1 hc.2.1 hc.2.2

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Averages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Hilbert-space variance estimate for geodesic averages. Applying this
to the Jacobi curvature matrix in the Hilbert space of square-integrable
fields separates the averaging argument from the geometric flow identities. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory Filter

noncomputable section

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → E}

omit [CompleteSpace E] in
theorem integrable_sq_distance (hf : Integrable f μ)
    (hf2 : Integrable (fun t => ‖f t‖ ^ 2) μ) (a : E) :
    Integrable (fun t => ‖a - f t‖ ^ 2) μ := by
  have h := ((integrable_const (‖a‖ ^ 2)).sub ((hf.const_inner a).const_mul 2)).add hf2
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  exact norm_sub_sq_real a (f t)

theorem integral_sq_distance (hf : Integrable f μ)
    (hf2 : Integrable (fun t => ‖f t‖ ^ 2) μ) (a : E) :
    (∫ t, ‖a - f t‖ ^ 2 ∂μ) =
      ‖a‖ ^ 2 - 2 * inner ℝ a (∫ t, f t ∂μ) + ∫ t, ‖f t‖ ^ 2 ∂μ := by
  simp_rw [norm_sub_sq_real]
  have hadd := integral_add ((integrable_const (‖a‖ ^ 2)).sub
    ((hf.const_inner a).const_mul 2)) hf2
  have hsub := integral_sub (integrable_const (‖a‖ ^ 2))
    ((hf.const_inner a).const_mul 2)
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul, integral_inner hf a]
  simp only [integral_const, probReal_univ, one_smul]

theorem integrable_mean_sq_distance (hf : Integrable f μ)
    (hf2 : Integrable (fun t => ‖f t‖ ^ 2) μ) :
    Integrable (fun s => ∫ t, ‖f s - f t‖ ^ 2 ∂μ) μ := by
  have h := (hf2.sub ((hf.inner_const (∫ t, f t ∂μ)).const_mul 2)).add
    (integrable_const (∫ t, ‖f t‖ ^ 2 ∂μ))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext s
  exact integral_sq_distance hf hf2 (f s)

/-- The double-variance identity, with only the integrability needed by the
application. The two integrals need not be interchanged. -/
theorem double_variance_identity (hf : Integrable f μ)
    (hf2 : Integrable (fun t => ‖f t‖ ^ 2) μ) :
    (∫ s, ∫ t, ‖f s - f t‖ ^ 2 ∂μ ∂μ) =
      2 * ((∫ t, ‖f t‖ ^ 2 ∂μ) - ‖∫ t, f t ∂μ‖ ^ 2) := by
  simp_rw [integral_sq_distance hf hf2]
  have hadd := integral_add (hf2.sub ((hf.inner_const (∫ t, f t ∂μ)).const_mul 2))
    (integrable_const (∫ t, ‖f t‖ ^ 2 ∂μ))
  have hsub := integral_sub hf2 ((hf.inner_const (∫ t, f t ∂μ)).const_mul 2)
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul]
  have hinner : (∫ s, inner ℝ (f s) (∫ t, f t ∂μ) ∂μ) = ‖∫ t, f t ∂μ‖ ^ 2 := by
    calc
      _ = ∫ s, inner ℝ (∫ t, f t ∂μ) (f s) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun s => real_inner_comm _ _
      _ = inner ℝ (∫ t, f t ∂μ) (∫ t, f t ∂μ) := integral_inner hf _
      _ = _ := real_inner_self_eq_norm_sq _
  rw [hinner]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- A stationary Hilbert-valued curve with a mean-square increment bound
retains this much squared norm after averaging. In the geodesic application,
`L` is the averaged squared norm of the directional derivative. -/
theorem stationary_average_lower {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {A : ℝ → E} {q L : ℝ}
    (hA : Integrable A ν) (hA2 : Integrable (fun t => ‖A t‖ ^ 2) ν)
    (ht : Integrable (fun t : ℝ => t) ν)
    (ht2 : Integrable (fun t : ℝ => t ^ 2) ν)
    (hstationary : ∀ᵐ t ∂ν, ‖A t‖ ^ 2 = q)
    (hincrement : ∀ s t, ‖A s - A t‖ ^ 2 ≤ L * (s - t) ^ 2) :
    q - L * ((∫ t, t ^ 2 ∂ν) - (∫ t, t ∂ν) ^ 2) ≤ ‖∫ t, A t ∂ν‖ ^ 2 := by
  have ht2' : Integrable (fun t : ℝ => ‖t‖ ^ 2) ν := by simpa using ht2
  have hpoint (s : ℝ) : (∫ t, ‖A s - A t‖ ^ 2 ∂ν) ≤
      L * ∫ t, ‖s - t‖ ^ 2 ∂ν := by
    calc
      _ ≤ ∫ t, L * ‖s - t‖ ^ 2 ∂ν := by
        apply integral_mono (integrable_sq_distance hA hA2 (A s))
          ((integrable_sq_distance ht ht2' s).const_mul L)
        intro t
        simpa using hincrement s t
      _ = _ := integral_const_mul _ _
  have hbound := integral_mono (integrable_mean_sq_distance hA hA2)
    ((integrable_mean_sq_distance ht ht2').const_mul L) hpoint
  rw [double_variance_identity hA hA2, integral_const_mul,
    double_variance_identity ht ht2'] at hbound
  have hq : (∫ t, ‖A t‖ ^ 2 ∂ν) = q := by
    rw [integral_congr_ae hstationary]
    simp
  rw [hq] at hbound
  simp only [Real.norm_eq_abs, sq_abs] at hbound
  linarith

omit [CompleteSpace E] in
/-- An invariant averaged derivative bound controls increments of the
Hilbert-valued curvature curve. This is also valid for an `L²` Hilbert space. -/
theorem increment_bound_of_derivative {A d : ℝ → E} {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ t, HasDerivAt A (d t) t) (hbound : ∀ t, ‖d t‖ ^ 2 ≤ L) (s t : ℝ) :
    ‖A s - A t‖ ^ 2 ≤ L * (s - t) ^ 2 := by
  have hnorm (z : ℝ) : ‖d z‖ ≤ Real.sqrt L := by
    nlinarith [hbound z, Real.sqrt_nonneg L, Real.sq_sqrt hL, norm_nonneg (d z)]
  have hforward (a b : ℝ) (hab : a ≤ b) :
      ‖A b - A a‖ ≤ Real.sqrt L * (b - a) := by
    exact norm_image_sub_le_of_norm_deriv_le_segment'
      (fun z _ => (hd z).hasDerivWithinAt) (fun z _ => hnorm z) b ⟨hab, le_rfl⟩
  have hdist : ‖A s - A t‖ ≤ Real.sqrt L * |s - t| := by
    rcases le_total t s with hts | hst
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hts)] using hforward t s hts
    · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
      exact hforward s t hst
  have hsq := mul_le_mul hdist hdist (norm_nonneg _) (by positivity)
  simpa only [← pow_two, mul_pow, Real.sq_sqrt hL, sq_abs] using hsq

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SineAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact sine-squared probability weight in the first Dirichlet mode,
its first two moments, and the resulting geodesic averaging coefficient. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

def sineWeight (u : ℝ) : ℝ := 1 - Real.cos (2 * Real.pi * u)

theorem sineWeight_eq (u : ℝ) : sineWeight u = 2 * Real.sin (Real.pi * u) ^ 2 := by
  unfold sineWeight
  rw [mul_assoc, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * u)]

theorem sineWeight_nonneg (u : ℝ) : 0 ≤ sineWeight u := by
  rw [sineWeight_eq]
  positivity

theorem continuous_sineWeight : Continuous sineWeight := by
  unfold sineWeight
  fun_prop

theorem integral_sineWeight : (∫ u in (0 : ℝ)..1, sineWeight u) = 1 := by
  have hd (u : ℝ) : HasDerivAt
      (fun z => z - Real.sin (2 * Real.pi * z) / (2 * Real.pi)) (sineWeight u) u := by
    convert (hasDerivAt_id u).sub
      ((((hasDerivAt_id u).const_mul (2 * Real.pi)).sin).div_const (2 * Real.pi)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (simp only [sineWeight, id_eq]; field_simp [Real.pi_ne_zero])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (continuous_sineWeight.intervalIntegrable 0 1)]
  simp [Real.sin_two_pi]

theorem integral_sineWeight_first : (∫ u in (0 : ℝ)..1, sineWeight u * u) = 1 / 2 := by
  have hd (u : ℝ) : HasDerivAt
      (fun z => z ^ 2 / 2 - z * Real.sin (2 * Real.pi * z) / (2 * Real.pi) -
        Real.cos (2 * Real.pi * z) / (2 * Real.pi) ^ 2) (sineWeight u * u) u := by
    have hs := ((hasDerivAt_id u).const_mul (2 * Real.pi)).sin
    have hc := ((hasDerivAt_id u).const_mul (2 * Real.pi)).cos
    convert ((((hasDerivAt_id u).pow 2).div_const 2).sub
      (((hasDerivAt_id u).mul hs).div_const (2 * Real.pi))).sub
      (hc.div_const ((2 * Real.pi) ^ 2)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (simp only [sineWeight, id_eq]; field_simp [Real.pi_ne_zero]; ring)
  have hi : IntervalIntegrable (fun u => sineWeight u * u) volume 0 1 :=
    (continuous_sineWeight.mul continuous_id).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi]
  simp [Real.sin_two_pi, Real.cos_two_pi]

theorem integral_sineWeight_second : (∫ u in (0 : ℝ)..1, sineWeight u * u ^ 2) =
    1 / 3 - 1 / (2 * Real.pi ^ 2) := by
  have hd (u : ℝ) : HasDerivAt
      (fun z => z ^ 3 / 3 - z ^ 2 * Real.sin (2 * Real.pi * z) / (2 * Real.pi) -
        2 * z * Real.cos (2 * Real.pi * z) / (2 * Real.pi) ^ 2 +
        2 * Real.sin (2 * Real.pi * z) / (2 * Real.pi) ^ 3)
      (sineWeight u * u ^ 2) u := by
    have hs := ((hasDerivAt_id u).const_mul (2 * Real.pi)).sin
    have hc := ((hasDerivAt_id u).const_mul (2 * Real.pi)).cos
    convert (((((hasDerivAt_id u).pow 3).div_const 3).sub
      ((((hasDerivAt_id u).pow 2).mul hs).div_const (2 * Real.pi))).sub
      ((((hasDerivAt_id u).const_mul 2).mul hc).div_const ((2 * Real.pi) ^ 2))).add
      ((hs.const_mul 2).div_const ((2 * Real.pi) ^ 3)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (simp only [sineWeight, Pi.pow_apply, id_eq]; field_simp [Real.pi_ne_zero]; ring)
  have hi : IntervalIntegrable (fun u => sineWeight u * u ^ 2) volume 0 1 :=
    (continuous_sineWeight.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi]
  norm_num [Real.sin_two_pi, Real.cos_two_pi]
  field_simp [Real.pi_ne_zero]

/-- The actual probability measure on the unit time interval, not a moment
axiomatization of that measure. -/
def sineMeasure : Measure ℝ :=
  (volume.restrict (Set.Ioc 0 1)).withDensity (fun u => ENNReal.ofReal (sineWeight u))

theorem integral_sineMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : (∫ u, f u ∂sineMeasure) = ∫ u in (0 : ℝ)..1, sineWeight u • f u := by
  unfold sineMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    continuous_sineWeight.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (sineWeight_nonneg _)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

instance instIsProbabilityMeasureRealSineMeasure : IsProbabilityMeasure sineMeasure := by
  apply isProbabilityMeasure_iff_real.mpr
  have h := integral_sineMeasure (fun _ => (1 : ℝ))
  simpa only [integral_const, smul_eq_mul, mul_one, integral_sineWeight] using h

theorem integrable_sineMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Continuous f) : Integrable f sineMeasure := by
  unfold sineMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    continuous_sineWeight.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (sineWeight_nonneg _)]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    ((continuous_sineWeight.smul hf).intervalIntegrable 0 1)

theorem sineMeasure_first : (∫ u, u ∂sineMeasure) = 1 / 2 := by
  simpa only [integral_sineMeasure, smul_eq_mul] using integral_sineWeight_first

theorem sineMeasure_second : (∫ u, u ^ 2 ∂sineMeasure) =
    1 / 3 - 1 / (2 * Real.pi ^ 2) := by
  simpa only [integral_sineMeasure, smul_eq_mul] using integral_sineWeight_second

theorem sineMeasure_variance : (∫ u, u ^ 2 ∂sineMeasure) - (∫ u, u ∂sineMeasure) ^ 2 =
    1 / 12 - 1 / (2 * Real.pi ^ 2) := by
  rw [sineMeasure_first, sineMeasure_second]
  ring

theorem sine_average_coefficient (u : ℝ) :
    (3 / 2) * (Real.pi * u) ^ 2 * (1 / 12 - 1 / (2 * Real.pi ^ 2)) ≤ u ^ 2 / 2 := by
  have hpi : Real.pi ^ 2 < 10 := by
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have heq : (3 / 2) * (Real.pi * u) ^ 2 * (1 / 12 - 1 / (2 * Real.pi ^ 2)) =
      u ^ 2 * ((Real.pi ^ 2 - 6) / 8) := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [heq]
  nlinarith [mul_nonneg (sq_nonneg u) (show 0 ≤ 10 - Real.pi ^ 2 by linarith)]

/-- The averaged squared norm retained by the first sine mode. For the
curvature application the increment hypothesis comes from the invariant
geodesic-flow measure and the integrated Weyl differential identity. -/
theorem sine_average_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {A : ℝ → E} {q u : ℝ} (hq : 0 ≤ q)
    (hA : Integrable A sineMeasure)
    (hA2 : Integrable (fun t => ‖A t‖ ^ 2) sineMeasure)
    (hstationary : ∀ᵐ t ∂sineMeasure, ‖A t‖ ^ 2 = q)
    (hincrement : ∀ s t, ‖A s - A t‖ ^ 2 ≤
      ((3 / 2) * q * (Real.pi * u) ^ 2) * (s - t) ^ 2) :
    q * (1 - u ^ 2 / 2) ≤ ‖∫ t, A t ∂sineMeasure‖ ^ 2 := by
  have h := stationary_average_lower hA hA2 (integrable_sineMeasure continuous_id)
    (integrable_sineMeasure (continuous_id.pow 2)) hstationary hincrement
  rw [sineMeasure_variance] at h
  have hc := mul_le_mul_of_nonneg_left (sine_average_coefficient u) hq
  nlinarith only [h, hc]

/-- The differentiable-curve version supplies both integrability and the
increment estimate. Its derivative hypothesis has exactly the geodesic
curvature normalization after time is rescaled to the unit interval. -/
theorem sine_average_lower_of_derivative {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {A d : ℝ → E} {q u : ℝ} (hq : 0 ≤ q)
    (hd : ∀ t, HasDerivAt A (d t) t)
    (hstationary : ∀ᵐ t ∂sineMeasure, ‖A t‖ ^ 2 = q)
    (hbound : ∀ t, ‖d t‖ ^ 2 ≤ (3 / 2) * q * (Real.pi * u) ^ 2) :
    q * (1 - u ^ 2 / 2) ≤ ‖∫ t, A t ∂sineMeasure‖ ^ 2 := by
  have hA : Continuous A := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  apply sine_average_lower hq (integrable_sineMeasure hA)
    (integrable_sineMeasure (hA.norm.pow 2)) hstationary
  exact increment_bound_of_derivative (by positivity) hd hbound

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-mode averaging estimate in the actual space of square-integrable
fields. Stationarity is an integral over the space of initial geodesics; no
pointwise constancy along a geodesic is assumed. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

omit [CompleteSpace E] in
/-- The Hilbert norm used for geodesic averaging is exactly the mean square
of the continuous field, with respect to the chosen finite measure. -/
theorem continuous_toL2_norm_sq (f : C(Ω, E)) :
    ‖ContinuousMap.toLp 2 μ ℝ f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    (∫ x, inner ℝ ((ContinuousMap.toLp 2 μ ℝ f) x)
      ((ContinuousMap.toLp 2 μ ℝ f) x) ∂μ) = ∫ x, inner ℝ (f x) (f x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f] with x hx
        rw [hx]
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

/-- Averaging a field first in time and then in space gives the same squared
norm as the Bochner average in the actual `L²` space. -/
theorem continuous_toL2_average_norm_sq {F : ℝ → C(Ω, E)}
    (hF : Integrable F sineMeasure) :
    ‖∫ u, ContinuousMap.toLp 2 μ ℝ (F u) ∂sineMeasure‖ ^ 2 =
      ∫ x, ‖∫ u, F u x ∂sineMeasure‖ ^ 2 ∂μ := by
  rw [(ContinuousMap.toLp 2 μ ℝ).integral_comp_comm hF,
    continuous_toL2_norm_sq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [ContinuousMap.integral_apply hF x]

/-- The geodesic first-mode bound, obtained from stationarity of mean-square
curvature and its mean-square derivative bound. The hypotheses are ordinary
field identities and derivatives; the conclusion is the iterated integral
needed in the radial determinant comparison. -/
theorem geodesic_mean_square_lower {F G : ℝ → C(Ω, E)} {q t : ℝ}
    (hq : 0 ≤ q)
    (hderiv : ∀ r, HasDerivAt F (G r) r)
    (hstationary : ∀ r, (∫ x, ‖F r x‖ ^ 2 ∂μ) = q)
    (henergy : ∀ r, (∫ x, ‖G r x‖ ^ 2 ∂μ) ≤ (3 / 2) * q) :
    q * (1 - (t / Real.pi) ^ 2 / 2) ≤
      ∫ x, ‖∫ u, F (t * u) x ∂sineMeasure‖ ^ 2 ∂μ := by
  let T : C(Ω, E) →L[ℝ] Lp E 2 μ := ContinuousMap.toLp 2 μ ℝ
  have hd (u : ℝ) : HasDerivAt (fun u => T (F (t * u))) (t • T (G (t * u))) u := by
    exact ((T.hasFDerivAt.comp_hasDerivAt (t * u) (hderiv (t * u))).scomp u
      (by simpa using (hasDerivAt_id u).const_mul t))
  have hs : ∀ᵐ u ∂sineMeasure, ‖T (F (t * u))‖ ^ 2 = q :=
    Filter.Eventually.of_forall fun u => (continuous_toL2_norm_sq _).trans (hstationary _)
  have hb (u : ℝ) : ‖t • T (G (t * u))‖ ^ 2 ≤
      (3 / 2) * q * (Real.pi * (t / Real.pi)) ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, continuous_toL2_norm_sq]
    have he := mul_le_mul_of_nonneg_left (henergy (t * u)) (sq_nonneg t)
    field_simp [Real.pi_ne_zero]
    nlinarith only [he]
  have h := sine_average_lower_of_derivative hq hd hs hb
  have hc : Continuous (fun u => F (t * u)) :=
    (continuous_iff_continuousAt.mpr fun r => (hderiv r).continuousAt).comp
      (continuous_const.mul continuous_id)
  rwa [continuous_toL2_average_norm_sq (integrable_sineMeasure hc)] at h

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiAverage
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace and curvature bounds for the concrete sine-weighted average. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

local instance instNormedAddCommGroupNormalMatrix_re7c677_1 : NormedAddCommGroup NormalMatrix := Matrix.frobeniusNormedAddCommGroup
def entryCLM (i j : Fin 3) : NormalMatrix →L[ℝ] ℝ :=
  (show NormalMatrix →ₗ[ℝ] ℝ from
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

@[simp] theorem entryCLM_apply (i j : Fin 3) (A : NormalMatrix) :
    entryCLM i j A = A i j := rfl

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ModeAverageLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence of the normalized scalar-mode curvature average. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem sineWeight_lipschitz (s r : ℝ) :
    ‖Averages.sineWeight s - Averages.sineWeight r‖ ≤ 2 * Real.pi * |s - r| := by
  have hid : Averages.sineWeight s - Averages.sineWeight r =
      Real.cos (2 * Real.pi * r) - Real.cos (2 * Real.pi * s) := by
    unfold Averages.sineWeight
    ring
  rw [hid, Real.norm_eq_abs]
  calc
    _ ≤ |2 * Real.pi * r - 2 * Real.pi * s| := Real.abs_cos_sub_cos_le _ _
    _ = 2 * Real.pi * |s - r| := by
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_sub_comm]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AveragedRadial
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

local instance instNormedAddCommGroupNormalMatrix_2_re7c677_1 : NormedAddCommGroup NormalMatrix := Matrix.frobeniusNormedAddCommGroup
local instance instNormedSpaceRealNormalMatrix_1_re7c677_1 : NormedSpace ℝ NormalMatrix := Matrix.frobeniusNormedSpace
/-- The radial Jacobian, set to zero once a conjugate point has occurred. -/
def RegularJacobi.truncatedDensity {t : ℝ} (d : RegularJacobi t) : ℝ := by
  classical
  exact if ∀ s, 0 < s → s ≤ t → IsUnit (d.J s) then (d.J t).det else 0

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Coupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebra and integration in the one-block vanishing argument

The scalar one-block vanishing argument in Section 8 of
*Positively curved Einstein four-manifolds* (23 September 2026). -/

namespace PositiveEinsteinFour

open MeasureTheory Filter

noncomputable section

/-- The coefficient `c` in the paper's equation (15). -/
def couplingCoefficient (v b : ℝ) : ℝ := 2 / 5 - 3 / 10 * v * b

end

end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The potential polynomial certificate

The five quotient polynomials and their quarter-interval Bernstein certificates
are those of Section 7, Lemma "The polynomial F" of the manuscript.
The polynomial identities and inequalities hold over the real numbers.
-/

namespace PositiveEinsteinFour.Potential

noncomputable section

/-- The multiplier in equation (15), with its exact rational coefficients. -/
def kappa (v b : ℝ) : ℝ :=
  let a := v - 1
  let s := b - 1;
  -(158 / 6) * (a - s) - (43 / 4) * a ^ 2 + (61 / 18) * a * s -
    (45 / 4) * s ^ 2 - (63 / 4) * s ^ 3 + (21 / 4) * a * s ^ 2 +
    (183 / 4) * a ^ 2 * s + (208 / 4) * a ^ 3 + (61 / 4) * s ^ 4 +
    (46 / 4) * a * s ^ 3 + (101 / 4) * a ^ 2 * s ^ 2 +
    (79 / 4) * a ^ 3 * s - (41 / 4) * a ^ 4

def theta (v b : ℝ) : ℝ :=
  let n := (2 - v - b) / 2
  let t := (v - b) / 2
  (n ^ 2 * (1 - n) * (105 + 5 * n) +
    t ^ 2 * (4 + 360 * n - 586 * n ^ 2) - 4 * t ^ 4) / 4

def zeroOrder (v b : ℝ) : ℝ :=
  let δ := 2 - v - b
  158 * (1 - δ ^ 2 / 4) * (v - b) ^ 2 +
    51 * δ * (v ^ 2 * (v - 1) ^ 2 + b ^ 2 * (b - 1) ^ 2) +
    6 * ((v - 1) * v * kappa v b + (b - 1) * b * kappa b v)

/-- The actual polynomial `F = c E₀ - Θ²` from equation (23). -/
def potential (v b : ℝ) : ℝ :=
  (2 / 5 - 3 * v * b / 10) * zeroOrder v b - theta v b ^ 2

end

end PositiveEinsteinFour.Potential

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact triangle certificates and the full zeroth-order coupling bound. -/

namespace PositiveEinsteinFour.Boundary

open Potential

noncomputable section

def spectralCoefficient (v b : ℝ) : ℝ :=
  17 * (2 - v - b) * v - kappa v b

def correctedPotential (v b : ℝ) : ℝ :=
  potential v b + 12 * couplingCoefficient v b * (2 - v - b) ^ 2 * spectralCoefficient b v

/-- The derivative-free part of the manuscript's combined integrand. -/
def zeroOrderIntegrand (v b σ τ : ℝ) : ℝ :=
  -zeroOrder v b - 6 * v ^ 2 * (1 - σ) * spectralCoefficient v b -
    6 * b ^ 2 * (1 - τ) * spectralCoefficient b v

end

end PositiveEinsteinFour.Boundary

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CP2Overlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit representatives and transition probabilities for the actual
Fubini--Study distance on CP2. -/

namespace PositiveEinsteinFour

open EinsteinFour

noncomputable section

abbrev CP2Vector := EuclideanSpace ℂ (Fin 3)

def cp2UnitRep (p : ComplexProjective2) : CP2Vector :=
  ((‖p.rep‖⁻¹ : ℝ) : ℂ) • p.rep

theorem cp2UnitRep_norm (p : ComplexProjective2) : ‖cp2UnitRep p‖ = 1 := by
  have hn : ‖p.rep‖ ≠ 0 := norm_ne_zero_iff.mpr p.rep_nonzero
  simp [cp2UnitRep, norm_smul, Complex.norm_real, hn]

theorem cp2UnitRep_ne_zero (p : ComplexProjective2) : cp2UnitRep p ≠ 0 := by
  intro h
  have hn := cp2UnitRep_norm p
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem cp2UnitRep_mk (p : ComplexProjective2) :
    Projectivization.mk ℂ (cp2UnitRep p) (cp2UnitRep_ne_zero p) = p := by
  conv_rhs => rw [← p.mk_rep]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨_, rfl⟩

def cp2Overlap (p q : ComplexProjective2) : ℝ :=
  ‖inner ℂ (cp2UnitRep p) (cp2UnitRep q)‖

@[simp] theorem cp2Overlap_self (p : ComplexProjective2) : cp2Overlap p p = 1 := by
  change ‖inner ℂ (cp2UnitRep p) (cp2UnitRep p)‖ = 1
  rw [inner_self_eq_norm_sq_to_K, cp2UnitRep_norm]
  norm_num

end
end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CP2UnitGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unit representatives needed for the projective fixed-point argument. -/

namespace PositiveEinsteinFour

open EinsteinFour

noncomputable section

theorem cp2Overlap_eq_one_iff (p q : ComplexProjective2) :
    cp2Overlap p q = 1 ↔ p = q := by
  constructor
  · intro h
    have hCS : ‖inner ℂ (cp2UnitRep p) (cp2UnitRep q)‖ =
        ‖cp2UnitRep p‖ * ‖cp2UnitRep q‖ := by
      simpa only [cp2Overlap, cp2UnitRep_norm, one_mul] using h
    obtain ⟨a, _, ha⟩ :=
      (norm_inner_eq_norm_iff (cp2UnitRep_ne_zero p) (cp2UnitRep_ne_zero q)).mp hCS
    rw [← cp2UnitRep_mk p, ← cp2UnitRep_mk q]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨a⁻¹, by rw [ha, smul_smul]; simp_all⟩
  · rintro rfl
    exact cp2Overlap_self p

end
end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CompactDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness passes to a linear map whose norm is controlled by a compact
map. This is used for the finite coordinate reconstruction of two-forms. -/

namespace PositiveEinsteinFour.Geometry

open Set Metric

noncomputable section

theorem compact_of_norm_domination
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : E →L[ℝ] F) (Q : E →L[ℝ] G) (hQ : IsCompactOperator Q)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖T x‖ ≤ C * ‖Q x‖) :
    IsCompactOperator T := by
  let R := Set.range (Q : E → G)
  let pick : R → E := fun y => Classical.choose y.property
  have hpick (y : R) : Q (pick y) = y.val := Classical.choose_spec y.property
  let f : R → F := fun y => T (pick y)
  have hf (x : E) : f ⟨Q x, ⟨x, rfl⟩⟩ = T x := by
    have h := hb (pick ⟨Q x, ⟨x, rfl⟩⟩ - x)
    simp only [map_sub, hpick, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have hLip : LipschitzWith ⟨C, hC⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (T (pick x)) (T (pick y)) ≤ C * dist x.val y.val
    simp only [dist_eq_norm]
    simpa only [map_sub, hpick] using hb (pick x - pick y)
  let B := closedBall (0 : E) 1
  have ht : TotallyBounded (Q '' B) :=
    (hQ.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  have hs : TotallyBounded ((Subtype.val : R → G) ⁻¹' (Q '' B)) :=
    totallyBounded_preimage isUniformEmbedding_subtype_val.isUniformInducing ht
  have heq : f '' ((Subtype.val : R → G) ⁻¹' (Q '' B)) = T '' B := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, hxy⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      have hy : y = ⟨Q x, ⟨x, rfl⟩⟩ := Subtype.ext hxy.symm
      rw [hy, hf]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨Q x, ⟨x, rfl⟩⟩, ⟨x, hx, rfl⟩, hf x⟩
  have htb : TotallyBounded (T '' B) := heq ▸ hs.image hLip.uniformContinuous
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall
    T.toLinearMap (show (0 : ℝ) < 1 by norm_num)).mpr
      (isCompact_iff_totallyBounded_isComplete.mpr
        ⟨htb.closure, isClosed_closure.isComplete⟩)

theorem compact_finite_pi
    {E F J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype J]
    (Q : J → E →L[ℝ] F) (hQ : ∀ j, IsCompactOperator (Q j)) :
    IsCompactOperator (ContinuousLinearMap.pi Q) := by
  choose K hK hb using fun j => (hQ j).image_closedBall_subset_compact 1
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (ContinuousLinearMap.pi Q).toLinearMap (show (0 : ℝ) < 1 by norm_num)).mpr
  refine ⟨Set.pi Set.univ K, isCompact_univ_pi hK, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ j _
  exact hb j ⟨x, hx, rfl⟩

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CoordinateMetricCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric-compatibility identity for the actual Christoffel formula.
This algebraic step needs only invertibility of the chart metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem matrix_lower_inverse (G : Mat4) (hG : IsUnit G.det)
    (v : Fin 4 → ℝ) (k : Fin 4) :
    (∑ p, G k p * ((1 / 2 : ℝ) * ∑ l, G⁻¹ p l * v l)) = (1 / 2 : ℝ) * v k := by
  change (G *ᵥ ((1 / 2 : ℝ) • (G⁻¹ *ᵥ v))) k = _
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG,
    Matrix.one_mulVec]
  rfl

/-- Differentiating metric compatibility in two coordinate directions leaves
exactly the skew-adjointness equation for their curvature commutator. -/
theorem curvature_matrix_skew_of_metric_differentials (G A B C D : Mat4)
    (hmixed :
      Cᵀ * G + Bᵀ * (Aᵀ * G + G * A) + (Aᵀ * G + G * A) * B + G * C =
      Dᵀ * G + Aᵀ * (Bᵀ * G + G * B) + (Bᵀ * G + G * B) * A + G * D) :
    (C - D + A * B - B * A)ᵀ * G + G * (C - D + A * B - B * A) = 0 := by
  calc
    _ = (Cᵀ * G + Bᵀ * (Aᵀ * G + G * A) + (Aᵀ * G + G * A) * B + G * C) -
        (Dᵀ * G + Aᵀ * (Bᵀ * G + G * B) + (Bᵀ * G + G * B) * A + G * D) := by
      simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul]
      noncomm_ring
    _ = 0 := sub_eq_zero.mpr hmixed

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureFirstBianchi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first Bianchi identity follows directly from the symmetric
Levi-Civita Christoffel symbols and is preserved by frame contraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem sum_three_cycle (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ p, ∑ q, ∑ r, f p q r) = ∑ p, ∑ q, ∑ r, f q r p := by
  calc
    _ = ∑ p, ∑ r, ∑ q, f p q r := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem contracted_bianchi (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ p q r, R p q r + R q r p + R r p q = 0)
    (E : Matrix (Fin 4) (Fin 4) ℝ) (i j k : Fin 4) :
    (∑ p, ∑ q, ∑ r, R p q r * E p i * E q j * E r k) +
      (∑ p, ∑ q, ∑ r, R p q r * E p j * E q k * E r i) +
      (∑ p, ∑ q, ∑ r, R p q r * E p k * E q i * E r j) = 0 := by
  have h2 : (∑ p, ∑ q, ∑ r, R p q r * E p j * E q k * E r i) =
      ∑ p, ∑ q, ∑ r, R q r p * E p i * E q j * E r k := by
    rw [sum_three_cycle]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    ring
  have h3 : (∑ p, ∑ q, ∑ r, R p q r * E p k * E q i * E r j) =
      ∑ p, ∑ q, ∑ r, R r p q * E p i * E q j * E r k := by
    rw [sum_three_cycle, sum_three_cycle]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro p _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro q _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro r _
  linear_combination (E p i * E q j * E r k) * hR p q r

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ConnectionPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric compatibility under the coordinate change formula for a
connection. The matrices here are four-dimensional chart matrices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem pullback_metric_compatibility (H J K P U : Mat4)
    (h : J * K = P + U * J) :
    Kᵀ * (Jᵀ * H * J) + (Jᵀ * H * J) * K =
      Pᵀ * H * J + Jᵀ * (Uᵀ * H + H * U) * J + Jᵀ * H * P := by
  have ht : Kᵀ * Jᵀ = Pᵀ + Jᵀ * Uᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_add] using congrArg Matrix.transpose h
  calc
    _ = (Kᵀ * Jᵀ) * H * J + Jᵀ * H * (J * K) := by noncomm_ring
    _ = (Pᵀ + Jᵀ * Uᵀ) * H * J + Jᵀ * H * (P + U * J) := by rw [ht, h]
    _ = _ := by noncomm_ring

def pulledConnection (J P U : Mat4) : Mat4 := J⁻¹ * (P + U * J)

theorem pulledConnection_equation (J P U : Mat4) (hJ : IsUnit J.det) :
    J * pulledConnection J P U = P + U * J := by
  unfold pulledConnection
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hJ, one_mul]

theorem pulledConnection_metric_compatibility (H J P U : Mat4)
    (hJ : IsUnit J.det) :
    (pulledConnection J P U)ᵀ * (Jᵀ * H * J) +
      (Jᵀ * H * J) * pulledConnection J P U =
      Pᵀ * H * J + Jᵀ * (Uᵀ * H + H * U) * J + Jᵀ * H * P :=
  pullback_metric_compatibility H J _ P U (pulledConnection_equation J P U hJ)

def weightedConnection (J : Mat4) (C : Fin 4 → Mat4) (i : Fin 4) : Mat4 :=
  ∑ a, J a i • C a

theorem weightedConnection_torsion (J : Mat4) (C : Fin 4 → Mat4)
    (hC : ∀ a b r, C a r b = C b r a) (i j r : Fin 4) :
    (weightedConnection J C i * J) r j = (weightedConnection J C j * J) r i := by
  have he (s t : Fin 4) : (weightedConnection J C s * J) r t =
      ∑ a, ∑ b, J a s * C a r b * J b t := by
    simp only [weightedConnection, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [he, he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hC b a r]
  ring

theorem pulledConnection_torsion (J : Mat4) (P C : Fin 4 → Mat4)
    (hP : ∀ i j r, P i r j = P j r i)
    (hC : ∀ a b r, C a r b = C b r a) (i j k : Fin 4) :
    pulledConnection J (P i) (weightedConnection J C i) k j =
      pulledConnection J (P j) (weightedConnection J C j) k i := by
  change (∑ r, J⁻¹ k r * (P i r j + (weightedConnection J C i * J) r j)) =
    ∑ r, J⁻¹ k r * (P j r i + (weightedConnection J C j * J) r i)
  apply Finset.sum_congr rfl
  intro r _
  rw [hP i j r, weightedConnection_torsion J C hC i j r]

/-- The mixed Jacobian derivative cancels from the curvature transformation.
The two last premises are exactly the differentiated connection laws. -/
theorem curvature_intertwining_of_connection
    (J C₁ C₂ U₁ U₂ P₁ P₂ D₁₂ D₂₁ V₁₂ V₂₁ E : Mat4)
    (h₁ : J * C₁ = P₁ + U₁ * J) (h₂ : J * C₂ = P₂ + U₂ * J)
    (h₁₂ : P₁ * C₂ + J * D₁₂ = E + V₁₂ * J + U₂ * P₁)
    (h₂₁ : P₂ * C₁ + J * D₂₁ = E + V₂₁ * J + U₁ * P₂) :
    J * (D₁₂ - D₂₁ + C₁ * C₂ - C₂ * C₁) =
      (V₁₂ - V₂₁ + U₁ * U₂ - U₂ * U₁) * J := by
  have hd : J * D₁₂ - J * D₂₁ =
      (V₁₂ - V₂₁) * J + U₂ * P₁ - U₁ * P₂ - P₁ * C₂ + P₂ * C₁ := by
    calc
      _ = (P₁ * C₂ + J * D₁₂) - (P₂ * C₁ + J * D₂₁) -
          P₁ * C₂ + P₂ * C₁ := by noncomm_ring
      _ = _ := by rw [h₁₂, h₂₁]; noncomm_ring
  calc
    _ = (J * D₁₂ - J * D₂₁) + (J * C₁) * C₂ - (J * C₂) * C₁ := by
      noncomm_ring
    _ = ((V₁₂ - V₂₁) * J + U₂ * P₁ - U₁ * P₂ - P₁ * C₂ + P₂ * C₁) +
        (P₁ + U₁ * J) * C₂ - (P₂ + U₂ * J) * C₁ := by rw [hd, h₁, h₂]
    _ = (V₁₂ - V₂₁) * J + U₂ * P₁ - U₁ * P₂ - P₁ * C₂ + P₂ * C₁ +
        P₁ * C₂ + U₁ * (J * C₂) - P₂ * C₁ - U₂ * (J * C₁) := by noncomm_ring
    _ = _ := by rw [h₁, h₂]; noncomm_ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ContinuousFieldDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing from derivatives along each initial frame to a derivative in
the space of continuous fields. The fundamental theorem of calculus avoids
any separate uniform remainder assumption. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance instNormedAddCommGroupContinuousMap_solutions : NormedAddCommGroup C(Ω, E) := ContinuousMap.instNormedAddCommGroup
local instance instNormedSpaceRealContinuousMap_solutions : NormedSpace ℝ C(Ω, E) := ContinuousMap.normedSpace

/-- A continuous family of pointwise derivatives is the derivative in the
supremum norm on continuous fields. -/
theorem continuousField_hasDerivAt {F G : ℝ → C(Ω, E)}
    (hG : Continuous G)
    (hpoint : ∀ t x, HasDerivAt (fun s => F s x) (G t x) t) (t : ℝ) :
    HasDerivAt F (G t) t := by
  let K : ℝ → C(Ω, E) := fun s => F 0 + ∫ u in (0 : ℝ)..s, G u
  have hK (s : ℝ) : HasDerivAt K (G s) s :=
    (hG.integral_hasStrictDerivAt 0 s).hasDerivAt.const_add (F 0)
  have hFK : F = K := by
    funext s
    apply ContinuousMap.ext
    intro x
    have hd (u : ℝ) : HasDerivAt (fun u => F u x - K u x) 0 u := by
      let ev : C(Ω, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ x
      have he : HasDerivAt (fun u => K u x) (G u x) u :=
        ev.hasFDerivAt.comp_hasDerivAt u (hK u)
      convert (hpoint u x).sub he using 1
      all_goals try with_reducible_and_instances rfl
      simp
    have hc := is_const_of_deriv_eq_zero
      (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) s 0
    have hz : F 0 x - K 0 x = 0 := by simp [K]
    exact sub_eq_zero.mp (hc.trans hz)
  rw [hFK]
  exact hK t

/-- Joint continuity in time and the compact parameter gives exactly the
continuity required by `continuousField_hasDerivAt`. -/
theorem continuousField_hasDerivAt_of_joint {F G : ℝ → C(Ω, E)}
    (hG : Continuous (fun p : ℝ × Ω => G p.1 p.2))
    (hpoint : ∀ t x, HasDerivAt (fun s => F s x) (G t x) t) (t : ℝ) :
    HasDerivAt F (G t) t :=
  continuousField_hasDerivAt
    (ContinuousMap.continuous_of_continuous_uncurry G hG) hpoint t

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourDeterminantDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Determinant differentiation in the four-dimensional coordinates used
for the metric volume density. The proof uses the alternating determinant
and its row-replacement formula, without a matrix inverse. -/

namespace PositiveEinsteinFour.Geometry

open Matrix
open scoped BigOperators

noncomputable section

def determinantForm :
    (Fin 4 → ℝ) [⋀^Fin 4]→L[ℝ] ℝ :=
  { (Matrix.detRowAlternating : (Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ) with
    cont := continuous_id.matrix_det }

def determinantDifferential (G : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] ℝ :=
  determinantForm.toContinuousMultilinearMap.linearDeriv G

theorem determinantDifferential_apply (G H : Matrix (Fin 4) (Fin 4) ℝ) :
    determinantDifferential G H = ∑ i, (G.updateRow i (H i)).det := by
  calc
    _ = ∑ i, determinantForm (Function.update G i (H i)) :=
      ContinuousMultilinearMap.linearDeriv_apply
        determinantForm.toContinuousMultilinearMap G H
    _ = _ := by
      simp only [Matrix.updateRow]
      rfl

theorem hasDerivAt_det_of_components
    (G : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ)
    (h : ∀ i j, HasDerivAt (fun s => G s i j) (H i j) t) :
    HasDerivAt (fun s => (G s).det) (determinantDifferential (G t) H) t := by
  have hG : HasDerivAt G H t :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (h i))
  exact (determinantForm.hasFDerivAt (G t)).comp_hasDerivAt t hG

theorem determinantDifferential_left (G C : Matrix (Fin 4) (Fin 4) ℝ) :
    determinantDifferential G (C * G) = C.trace * G.det := by
  rw [determinantDifferential_apply]
  have hrow (i : Fin 4) : (C * G) i = ∑ r, C i r • G r := by
    ext j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
  exact (Finset.sum_mul _ _ _).symm

theorem determinantDifferential_transpose (G H : Matrix (Fin 4) (Fin 4) ℝ) :
    determinantDifferential Gᵀ Hᵀ = determinantDifferential G H := by
  have h (i j : Fin 4) :
      HasDerivAt (fun s : ℝ => (G + s • H) i j) (H i j) 0 := by
    change HasDerivAt (fun s : ℝ => G i j + s * H i j) (H i j) 0
    exact (hasDerivAt_mul_const (H i j)).const_add (G i j)
  have h₁ := hasDerivAt_det_of_components (fun s => G + s • H) H 0 h
  have h₂ := hasDerivAt_det_of_components (fun s => (G + s • H)ᵀ) Hᵀ 0
    (fun i j => h j i)
  simp only [zero_smul, add_zero, Matrix.det_transpose] at h₁ h₂
  exact h₂.unique h₁

theorem determinantDifferential_right (G C : Matrix (Fin 4) (Fin 4) ℝ) :
    determinantDifferential G (G * C) = C.trace * G.det := by
  rw [← determinantDifferential_transpose, Matrix.transpose_mul,
    determinantDifferential_left, Matrix.trace_transpose, Matrix.det_transpose]

/-- The determinant of a metric Gram matrix has twice the connection trace
as its logarithmic derivative. -/
theorem determinantDifferential_congruence (G C : Matrix (Fin 4) (Fin 4) ℝ) :
    determinantDifferential G (Cᵀ * G + G * C) = 2 * C.trace * G.det := by
  rw [map_add, determinantDifferential_left, determinantDifferential_right,
    Matrix.trace_transpose]
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CotangentJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The eight-coordinate Jacobian calculation for the cotangent flow.
The variational equation is kept explicit here; it will be supplied by
the derivative of the actual flow with respect to its initial value. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

abbrev CotangentIndex := Fin 4 ⊕ Fin 4
abbrev CotangentMatrix := Matrix CotangentIndex CotangentIndex ℝ

def indexDeterminantForm {n : Type*} [Fintype n] [DecidableEq n] :
    (n → ℝ) [⋀^n]→L[ℝ] ℝ :=
  { (Matrix.detRowAlternating :
      (n → ℝ) [⋀^n]→ₗ[ℝ] ℝ) with
    cont := continuous_id.matrix_det }

def indexDeterminantDifferential {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  indexDeterminantForm.toContinuousMultilinearMap.linearDeriv J

theorem indexDeterminantDifferential_left {n : Type*} [Fintype n] [DecidableEq n]
    (J A : Matrix n n ℝ) :
    indexDeterminantDifferential J (A * J) = A.trace * J.det := by
  have hform : indexDeterminantDifferential J (A * J) =
      ∑ i, (J.updateRow i ((A * J) i)).det := by
    calc
      _ = ∑ i, indexDeterminantForm (Function.update J i ((A * J) i)) :=
        ContinuousMultilinearMap.linearDeriv_apply
          indexDeterminantForm.toContinuousMultilinearMap J (A * J)
      _ = _ := by
        simp only [Matrix.updateRow]
        rfl
  rw [hform]
  have hrow (i : n) : (A * J) i = ∑ r, A i r • J r := by
    ext j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
  exact (Finset.sum_mul _ _ _).symm

theorem hasDerivAt_indexDeterminant {n : Type*} [Fintype n] [DecidableEq n]
    (J : ℝ → Matrix n n ℝ) (A : Matrix n n ℝ) (t : ℝ)
    (hJ : ∀ i j, HasDerivAt (fun s => J s i j) ((A * J t) i j) t) :
    HasDerivAt (fun s => (J s).det) (A.trace * (J t).det) t := by
  have hd : HasDerivAt J (A * J t) t :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (hJ i))
  have h := (indexDeterminantForm.hasFDerivAt (J t)).comp_hasDerivAt t hd
  change HasDerivAt (fun s => (J s).det)
    (indexDeterminantDifferential (J t) (A * J t)) t at h
  rwa [indexDeterminantDifferential_left] at h

/-- Liouville's determinant identity in exactly the eight coordinates
needed for the cotangent bundle. No inverse of the Jacobian is needed. -/
theorem hasDerivAt_cotangentDeterminant (J : ℝ → CotangentMatrix)
    (A : CotangentMatrix) (t : ℝ)
    (hJ : ∀ i j, HasDerivAt (fun s => J s i j) ((A * J t) i j) t) :
    HasDerivAt (fun s => (J s).det) (A.trace * (J t).det) t :=
  hasDerivAt_indexDeterminant J A t hJ

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlowGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts from invariance of the frame-flow measure. The
only derivative hypotheses concern individual continuous fields along
the flow; the weighted identity is derived using the product rule. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

local instance flowGreenNormedAddCommGroup : NormedAddCommGroup C(Ω, ℝ) :=
  ContinuousMap.instNormedAddCommGroup
local instance flowGreenNormedSpace : NormedSpace ℝ C(Ω, ℝ) :=
  ContinuousMap.normedSpace

def fieldIntegral : C(Ω, ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM (μ := μ)).comp (ContinuousMap.toLp 1 μ ℝ)

theorem fieldIntegral_apply (f : C(Ω, ℝ)) :
    fieldIntegral μ f = ∫ x, f x ∂μ := by
  change L1.integralCLM (ContinuousMap.toLp 1 μ ℝ f) = _
  rw [← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) μ f)

/-- The integral of a continuous infinitesimal generator is zero. This
is obtained by differentiating the invariant integral, not assumed as
a separate integration-by-parts law. -/
theorem integral_flow_derivative_zero
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hμ : ∀ t, MeasurePreserving (φ t) μ μ)
    (f d : C(Ω, ℝ))
    (hd : ∀ t x, HasDerivAt (fun s => f (φ s x)) (d (φ t x)) t) :
    (∫ x, d x ∂μ) = 0 := by
  let F : ℝ → C(Ω, ℝ) := fun t =>
    ⟨fun x => f (φ t x), f.continuous.comp
      (hφ.comp (continuous_const.prodMk continuous_id))⟩
  let G : ℝ → C(Ω, ℝ) := fun t =>
    ⟨fun x => d (φ t x), d.continuous.comp
      (hφ.comp (continuous_const.prodMk continuous_id))⟩
  have hcurve : HasDerivAt F (G 0) 0 :=
    continuousField_hasDerivAt_of_joint (d.continuous.comp hφ) hd 0
  have hi := (fieldIntegral μ).hasFDerivAt.comp_hasDerivAt 0 hcurve
  change HasDerivAt (fun t => fieldIntegral μ (F t)) (fieldIntegral μ (G 0)) 0 at hi
  have hs (t : ℝ) : fieldIntegral μ (F t) = ∫ x, f x ∂μ := by
    rw [fieldIntegral_apply]
    exact (hμ t).integral_comp' f
  have hz : fieldIntegral μ (G 0) = ∫ x, d x ∂μ := by
    rw [fieldIntegral_apply]
    exact (hμ 0).integral_comp' d
  have hi' : HasDerivAt (fun _ : ℝ => ∫ x, f x ∂μ) (∫ x, d x ∂μ) 0 := by
    simpa only [hs, hz] using hi
  exact hi'.unique (hasDerivAt_const 0 (∫ x, f x ∂μ))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Weighted Green identity for any two tensor-coordinate fields along a
measure-preserving parallel-frame flow. -/
theorem weighted_flow_green
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hμ : ∀ t, MeasurePreserving (φ t) μ μ)
    (m dm : C(Ω, ℝ)) (f df g dg : C(Ω, E))
    (hm : ∀ t x, HasDerivAt (fun s => m (φ s x)) (dm (φ t x)) t)
    (hf : ∀ t x, HasDerivAt (fun s => f (φ s x)) (df (φ t x)) t)
    (hg : ∀ t x, HasDerivAt (fun s => g (φ s x)) (dg (φ t x)) t) :
    (∫ x, m x * inner ℝ (df x) (g x) +
      dm x * inner ℝ (f x) (g x) ∂μ) =
      -(∫ x, m x * inner ℝ (f x) (dg x) ∂μ) := by
  let P : C(Ω, ℝ) := ⟨fun x => m x * inner ℝ (f x) (g x), by fun_prop⟩
  let D : C(Ω, ℝ) := ⟨fun x =>
    m x * inner ℝ (df x) (g x) + dm x * inner ℝ (f x) (g x) +
      m x * inner ℝ (f x) (dg x), by fun_prop⟩
  have hD (t : ℝ) (x : Ω) :
      HasDerivAt (fun s => P (φ s x)) (D (φ t x)) t := by
    convert (hm t x).mul ((hf t x).inner ℝ (hg t x)) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [P, D]
    ring
  have hz := integral_flow_derivative_zero μ φ hφ hμ P D hD
  have hfirst : Integrable
      (fun x => m x * inner ℝ (df x) (g x) + dm x * inner ℝ (f x) (g x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlast : Integrable (fun x => m x * inner ℝ (f x) (dg x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ x, (m x * inner ℝ (df x) (g x) + dm x * inner ℝ (f x) (g x)) +
    m x * inner ℝ (f x) (dg x) ∂μ) = 0 at hz
  rw [integral_add hfirst hlast] at hz
  linarith

/-- Sum the four parallel-frame directions. This is the weighted rough
Laplacian identity used for the covariant Weyl gradient. -/
theorem weighted_four_direction_green
    (φ : Fin 4 → ℝ → Ω ≃ᵐ Ω)
    (hφ : ∀ i, Continuous (fun p : ℝ × Ω => φ i p.1 p.2))
    (hμ : ∀ i t, MeasurePreserving (φ i t) μ μ)
    (m : C(Ω, ℝ)) (dm : Fin 4 → C(Ω, ℝ))
    (f : C(Ω, E)) (df ddf : Fin 4 → C(Ω, E))
    (hm : ∀ i t x, HasDerivAt (fun s => m (φ i s x)) (dm i (φ i t x)) t)
    (hf : ∀ i t x, HasDerivAt (fun s => f (φ i s x)) (df i (φ i t x)) t)
    (hdf : ∀ i t x, HasDerivAt (fun s => df i (φ i s x)) (ddf i (φ i t x)) t) :
    (∫ x, m x * (∑ i, ‖df i x‖ ^ 2) +
      ∑ i, dm i x * inner ℝ (f x) (df i x) ∂μ) =
      -(∫ x, m x * inner ℝ (f x) (∑ i, ddf i x) ∂μ) := by
  have hleft (i : Fin 4) : Integrable
      (fun x => m x * inner ℝ (df i x) (df i x) +
        dm i x * inner ℝ (f x) (df i x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hright (i : Fin 4) : Integrable
      (fun x => m x * inner ℝ (f x) (ddf i x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum :
      (∫ x, ∑ i, (m x * inner ℝ (df i x) (df i x) +
        dm i x * inner ℝ (f x) (df i x)) ∂μ) =
      -(∫ x, ∑ i, m x * inner ℝ (f x) (ddf i x) ∂μ) := by
    rw [integral_finsetSum _ (fun i _ => hleft i),
      integral_finsetSum _ (fun i _ => hright i)]
    simp_rw [weighted_flow_green μ _ (hφ _) (hμ _) m (dm _) f (df _) (df _) (ddf _)
      (hm _) (hf _) (hdf _)]
    simp only [Finset.sum_neg_distrib]
  simpa only [real_inner_self_eq_norm_sq, Finset.sum_add_distrib,
    Finset.mul_sum, inner_sum] using hsum

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureGreen
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

abbrev CurvatureIndex := (Fin 4 × Fin 4) × (Fin 4 × Fin 4)

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Defect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar certificates controlling the energy defects in equation (19). -/

namespace PositiveEinsteinFour.Defect

noncomputable section

def A0 (v : ℝ) : ℝ := (27 / 320) * v * (15 / 2 + 2 * v / 3)
def L0 (v : ℝ) : ℝ := (9 / 20) * v * (7 / 4 - 3 * v / 4)
def C0 (v : ℝ) : ℝ := (7 / 5) * (17 / 10) - A0 v - L0 v
def discriminantNumerator (v : ℝ) : ℝ :=
  4 * C0 v * (((17 / 10) - A0 v) * (2 - v) + (2 / 5) * (17 / 10) * v) -
    (2 - v) * (2 * A0 v + L0 v) ^ 2

end

end PositiveEinsteinFour.Defect

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removal of the energy defects

The right side of equation (19) is kept as an actual function of its two
energies. Its derivative estimate uses the scalar discriminant; continuity supplies
the zero-energy endpoints.
-/

namespace PositiveEinsteinFour.Energy

open Defect

noncomputable section

def scalarWeight (v b : ℝ) : ℝ := 1 - 3 * (v - b) / 8

def gradientSum (e0 f0 : ℝ) : ℝ :=
  Real.sqrt (3 / 5) * (Real.sqrt e0 + Real.sqrt f0)

/-- The actual right side of equation (19), with the two fixed radial energies
`e0`, `f0` and variable total energies `e`, `f`. -/
def quarticEnergy (v b e0 f0 g gb H Hb e f : ℝ) : ℝ :=
  (1 / 2) * Real.sqrt (3 / 5) * gradientSum e0 f0 *
      (scalarWeight v b * (e * Real.sqrt e) + scalarWeight b v * (f * Real.sqrt f)) +
    (9 / 64) * (gradientSum e0 f0) ^ 2 *
      (g * e0 + gb * f0 + H * (e - e0) + Hb * (f - f0)) -
    (17 / 10) * (e + f) * ((e - (3 / 5) * e0) / v + (f - (3 / 5) * f0) / b)

/-- The defect coefficient `H_d` in equation (19). -/
def defectCoefficient (v y : ℝ) : ℝ := (7 / 12) * (4 + y) + (5 / 4) * v + 4

end
end PositiveEinsteinFour.Energy

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeightedConnectionCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The curvature of the pulled-back connection one-form. The symmetric
second derivative of the coordinate change cancels in the alternating sum. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def weightedConnectionDerivative (J : Mat4) (P C : Fin 4 → Mat4)
    (D : Fin 4 → Fin 4 → Mat4) (i j : Fin 4) : Mat4 :=
  ∑ a, (P i a j • C a + J a j • ∑ b, J b i • D b a)

theorem weightedConnection_mul (J : Mat4) (C : Fin 4 → Mat4) (i j : Fin 4) :
    weightedConnection J C i * weightedConnection J C j =
      ∑ a, ∑ b, (J a i * J b j) • (C a * C b) := by
  simp only [weightedConnection, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm]

theorem weightedConnection_curvature (J : Mat4) (P C : Fin 4 → Mat4)
    (D : Fin 4 → Fin 4 → Mat4) (hP : ∀ i j a, P i a j = P j a i)
    (i j : Fin 4) :
    weightedConnectionDerivative J P C D i j - weightedConnectionDerivative J P C D j i +
      weightedConnection J C i * weightedConnection J C j -
        weightedConnection J C j * weightedConnection J C i =
      ∑ a, ∑ b, (J a i * J b j) • (D a b - D b a + C a * C b - C b * C a) := by
  have hp : (∑ a, P i a j • C a) = ∑ a, P j a i • C a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hP i j a]
  have hd : (∑ a, J a j • ∑ b, J b i • D b a) =
      ∑ a, ∑ b, (J a i * J b j) • D a b := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_comm]
  have hm : weightedConnection J C j * weightedConnection J C i =
      ∑ a, ∑ b, (J a i * J b j) • (C b * C a) := by
    rw [weightedConnection_mul, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_comm]
  simp only [weightedConnectionDerivative, Finset.sum_add_distrib]
  rw [hp, hd, weightedConnection_mul, hm]
  simp only [Finset.smul_sum, smul_smul, smul_sub, smul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCoordinateModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed twelve real coordinates for the inner generators in the cost calculation. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
set_option maxHeartbeats 1000000

def generatorCoefficients (s : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![![3, 2, -2], ![2/3, 5/3, -2/3], ![-10/3, -10/3, -5/3]],
    ![![3, -2, 2], ![-2/3, 5/3, -2/3], ![10/3, -10/3, -5/3]],
    ![![1, 0, 0], ![0, 11/3, 4/3], ![0, 20/3, -5/3]]] s

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TensorPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Skew matrix actions on the actual four tensor slots. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators

abbrev TensorIndex := Fin 4 × Fin 4 × Fin 3 × Fin 3

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate covariant derivatives of the actual curvature tensor. The
scalar-curvature contribution is subtracted in the Ricci=3g normalization.
The definitions retain all tensor slots until after differentiation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev CovariantCoordinates (n : ℕ) := (Fin n → Fin 4) → ℝ

/-- Pull back every covariant slot by a single actual orthonormal frame. -/
def frameTensor {n : ℕ} (A : Mat4) (T : CovariantCoordinates n) :
    CovariantCoordinates n := fun a =>
  ∑ b : Fin n → Fin 4, (∏ i, A (b i) (a i)) * T b

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameCurvatureMetricSkew
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of coordinate curvature skew-adjointness through the actual
orthonormal frame. No change-of-frame assumption is used. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem sum_four_first_last (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]

theorem sum_five_first_last (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact sum_four_first_last (fun a c d e => f a b c d e)

theorem skew_matrix_contraction (L E : Mat4)
    (hL : ∀ r b, L r b = -L b r) (k l : Fin 4) :
    (∑ r, ∑ b, L r b * E r k * E b l) =
      -(∑ r, ∑ b, L r b * E r l * E b k) := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ r, ∑ b, -(L r b * E r l * E b k) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro b _
      rw [hL b r]
      ring
    _ = _ := by simp only [Finset.sum_neg_distrib]

theorem tensor_last_skew_transport (G E : Mat4)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ p q r b, (∑ a, G a b * R a p q r) = -(∑ a, G a r * R a p q b))
    (i j k l : Fin 4) :
    (∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
      G a b * R a p q r * E p i * E q j * E r k * E b l) =
      -(∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
      G a b * R a p q r * E p i * E q j * E r l * E b k) := by
  have heq (k l : Fin 4) :
      (∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
        G a b * R a p q r * E p i * E q j * E r k * E b l) =
      ∑ p, ∑ q, (E p i * E q j) *
        ∑ r, ∑ b, (∑ a, G a b * R a p q r) * E r k * E b l := by
    rw [sum_five_first_last, sum_four_first_last]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heq, heq]
  have hs (p q : Fin 4) := skew_matrix_contraction
    (fun r b => ∑ a, G a b * R a p q r) E (hR p q) k l
  simp_rw [hs, mul_neg]
  simp only [Finset.sum_neg_distrib]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricInverseCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse metric is parallel. Its coordinate derivative is derived
from the inverse identity and the proved metric compatibility equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

theorem inverse_metric_derivative_algebra (G H C D : Mat4)
    (hGH : G * H = 1) (hHG : H * G = 1)
    (hD : D * G + H * (Cᵀ * G + G * C) = 0) :
    D = -(C * H) - H * Cᵀ := by
  have h := congrArg (fun A : Mat4 => A * H) hD
  have hexpand : (D * G + H * (Cᵀ * G + G * C)) * H = D + H * Cᵀ + C * H := by
    calc
      _ = D * (G * H) + (H * Cᵀ) * (G * H) + (H * G) * (C * H) := by
        noncomm_ring
      _ = _ := by rw [hGH, hHG]; simp
  rw [hexpand, zero_mul] at h
  have hd : D = -(H * Cᵀ + C * H) :=
    eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using h)
  rw [hd]
  abel

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricContractionCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiate contraction by the actual inverse metric. This is the
local identity needed to commute covariant differentiation with trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem metric_trace_derivative_algebra (H C T D : Mat4) :
    (((-(C * H) - H * Cᵀ) * T + H * D).trace) =
      (H * (D - Cᵀ * T - T * C)).trace := by
  have hm : (-(C * H) - H * Cᵀ) * T + H * D =
      H * (D - Cᵀ * T - T * C) + (H * T * C - C * H * T) := by
    noncomm_ring
  have hcycle : (C * H * T).trace = (H * T * C).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm C (H * T)
  rw [hm, Matrix.trace_add, Matrix.trace_sub, hcycle,
    sub_self, add_zero]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuaternionReflections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pure quaternion lifts of the reflections needed to choose a local
spectral frame. Only their concrete action on the two quaternion triples
is used; no global eigenframe or representation theorem is assumed. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def imaginaryCombination (Q : Fin 3 → Mat4) (u : Fin 3 → ℝ) : Mat4 :=
  ∑ r, u r • Q r

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuaternionGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rotation of the matrix indices is recovered from the actual
quaternion commutator.  Thus a four-dimensional quaternion lift also
intertwines the three-dimensional infinitesimal rotation generators. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem imaginaryCombination_apply (Q : Fin 3 → Mat4) (u : Fin 3 → ℝ)
    (i j : Fin 4) : imaginaryCombination Q u i j = ∑ r, u r * Q r i j := by
  change (∑ r, u r • Q r) i j = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RicciMatrixChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tracing curvature after an arbitrary invertible change of coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

/-- Contract the output and first curvature-input indices. -/
def ricciMatrix (R : Fin 4 → Fin 4 → Mat4) : Mat4 :=
  fun j k => ∑ i, R i j i k

theorem conjugate_row_contraction (J A : Mat4) (hJ : IsUnit J.det)
    (a k : Fin 4) :
    (∑ i, J a i * (J⁻¹ * A * J) i k) = (A * J) a k := by
  change (J * (J⁻¹ * A * J)) a k = _
  have he : J * (J⁻¹ * A * J) = A * J := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hJ,
      one_mul]
  exact congrArg (fun B : Mat4 => B a k) he

/-- Curvature conjugation in the vector slot and the two covector slots
induces precisely the ordinary covariant matrix law for Ricci. -/
theorem ricciMatrix_pullback (J : Mat4) (R S : Fin 4 → Fin 4 → Mat4)
    (hJ : IsUnit J.det)
    (hS : ∀ i j, S i j = J⁻¹ *
      (∑ a, ∑ b, (J a i * J b j) • R a b) * J) :
    ricciMatrix S = Jᵀ * (ricciMatrix R * J) := by
  have hexp (i j : Fin 4) : S i j =
      ∑ a, ∑ b, (J a i * J b j) • (J⁻¹ * R a b * J) := by
    rw [hS]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  ext j k
  change (∑ i, S i j i k) = (Jᵀ * (ricciMatrix R * J)) j k
  simp only [hexp, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    _ = ∑ a, ∑ b, J b j *
        (∑ i, J a i * (J⁻¹ * R a b * J) i k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ a, ∑ b, J b j * (R a b * J) a k := by
      simp only [conjugate_row_contraction J _ hJ]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, ricciMatrix,
        Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal projection is constructed from the actual tensor subspace. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

abbrev HessianSpace := EuclideanSpace ℝ TensorIndex

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Contracting the differential Bianchi identity, with the same index
convention as the actual frame Ricci tensor. -/

namespace PositiveEinsteinFour.Geometry

open Matrix
open scoped BigOperators

noncomputable section

def bianchiCycle : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 0, 3, 4]
  invFun := ![2, 0, 1, 3, 4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Bianchi triple becomes the positive triple after
reflecting only the derivative index. This gives the same invariant Kato
bound for the actual opposite Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def orientationSign (i : Fin 4) : ℝ := if i = 0 then -1 else 1

end
end PositiveEinsteinFour.Geometry
end


section

/-! The quaternionic contraction of a closed, alternating three-tensor.
This is the finite differential-Bianchi calculation used by Weyl blocks. -/

namespace PositiveEinsteinFour.Geometry

open Matrix
open scoped BigOperators

noncomputable section


theorem sum_six_last_pair
    (f : Fin 3 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ s, ∑ j, ∑ a, ∑ b, ∑ c, ∑ d, f s j a b c d) =
      ∑ c, ∑ d, ∑ s, ∑ j, ∑ a, ∑ b, f s j a b c d := by
  let e : ((Fin 4 × Fin 4) × ((Fin 3 × Fin 4) × (Fin 4 × Fin 4))) ≃
      ((Fin 3 × Fin 4) × ((Fin 4 × Fin 4) × (Fin 4 × Fin 4))) := {
    toFun := fun p => (p.2.1, (p.2.2, p.1))
    invFun := fun p => (p.2.2, (p.1, p.2.1))
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  simpa only [e, Equiv.coe_fn_mk, Fintype.sum_prod_type] using (e.sum_comp
    (fun p => f p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)).symm

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Finite frame transport for the differentiated Ricci contraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

def tensorConsEquiv (n : ℕ) :
    (Fin 4 × (Fin n → Fin 4)) ≃ (Fin (n + 1) → Fin 4) where
  toFun p := Fin.cons p.1 p.2
  invFun a := (a 0, fun i => a i.succ)
  left_inv p := by cases p; rfl
  right_inv a := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem sum_tensor_cons {n : ℕ} (f : (Fin (n + 1) → Fin 4) → ℝ) :
    (∑ w, f w) = ∑ b, ∑ v : Fin n → Fin 4, f (Fin.cons b v) := by
  have h := (tensorConsEquiv n).sum_comp f
  have hp : (∑ p : Fin 4 × (Fin n → Fin 4), f (tensorConsEquiv n p)) =
      ∑ b, ∑ v : Fin n → Fin 4, f (Fin.cons b v) := by
    rw [Fintype.sum_prod_type]
    rfl
  exact h.symm.trans hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariant differentiation preserves the algebraic slot symmetries.
The statements here apply to the actual coordinate curvature and its
actual orthonormal-frame pullback. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem sum_tensor_permute {n : ℕ}
    (f : (Fin n → Fin 4) → ℝ) (σ : Equiv.Perm (Fin n)) :
    (∑ b, f b) = ∑ b, f (b ∘ σ) := by
  let e : (Fin n → Fin 4) ≃ (Fin n → Fin 4) :=
    Equiv.arrowCongr σ.symm (Equiv.refl (Fin 4))
  exact (e.sum_comp f).symm

end
end PositiveEinsteinFour.Geometry
end


section

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def pairSwap : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl


def derivativePairSwap : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 4, 1, 2]
  invFun := ![0, 3, 4, 1, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariant differentiation and framing preserve the algebraic first
Bianchi identity as well as the pair and alternating symmetries. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def curvatureCycle : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 0, 3]
  invFun := ![2, 0, 1, 3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def frameCurvatureCycle : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 1, 4]
  invFun := ![0, 3, 1, 2, 4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Algebraic curvature symmetries persist through a second covariant
derivative; all derivative slots remain separate from curvature slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def hessianPairSwap : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 4, 1, 2]
  invFun := ![0, 3, 4, 1, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contraction of the actual covariant slot action with two-form matrices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem sumFive_swap0
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a b c d x) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f x b c d a := by
  let e : (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) := {
    toFun := fun ⟨a, b, c, d, x⟩ => (x, b, c, d, a)
    invFun := fun ⟨a, b, c, d, x⟩ => (x, b, c, d, a)
    left_inv := by rintro ⟨a, b, c, d, x⟩; rfl
    right_inv := by rintro ⟨a, b, c, d, x⟩; rfl }
  simpa only [e, Equiv.coe_fn_mk, Fintype.sum_prod_type] using
    (e.sum_comp (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).symm

theorem sumFive_swap1
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a b c d x) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a x c d b := by
  let e : (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) := {
    toFun := fun ⟨a, b, c, d, x⟩ => (a, x, c, d, b)
    invFun := fun ⟨a, b, c, d, x⟩ => (a, x, c, d, b)
    left_inv := by rintro ⟨a, b, c, d, x⟩; rfl
    right_inv := by rintro ⟨a, b, c, d, x⟩; rfl }
  simpa only [e, Equiv.coe_fn_mk, Fintype.sum_prod_type] using
    (e.sum_comp (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).symm

theorem sumFive_swap2
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a b c d x) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a b x d c := by
  let e : (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) := {
    toFun := fun ⟨a, b, c, d, x⟩ => (a, b, x, d, c)
    invFun := fun ⟨a, b, c, d, x⟩ => (a, b, x, d, c)
    left_inv := by rintro ⟨a, b, c, d, x⟩; rfl
    right_inv := by rintro ⟨a, b, c, d, x⟩; rfl }
  simpa only [e, Equiv.coe_fn_mk, Fintype.sum_prod_type] using
    (e.sum_comp (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).symm

theorem sumFive_swap3
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a b c d x) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, f a b c x d := by
  let e : (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) := {
    toFun := fun ⟨a, b, c, d, x⟩ => (a, b, c, x, d)
    invFun := fun ⟨a, b, c, d, x⟩ => (a, b, c, x, d)
    left_inv := by rintro ⟨a, b, c, d, x⟩; rfl
    right_inv := by rintro ⟨a, b, c, d, x⟩; rfl }
  simpa only [e, Equiv.coe_fn_mk, Fintype.sum_prod_type] using
    (e.sum_comp (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Einstein curvature Hessian has zero Ricci contraction.
The first Ricci contraction vanishes on an open chart before differentiating. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

theorem sum_five (f : Fin 5 → ℝ) :
    (∑ i, f i) = f 0 + (f 1 + f 2 + f 3 + f 4) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_four]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Algebraic first Bianchi survives a second covariant derivative.
Only an identity on the open chart is differentiated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

def secondCurvatureCycle : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 1, 4]
  invFun := ![0, 3, 1, 2, 4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rank-four curvature commutator on the positive Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem sumThree_cycle (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem sumFour_pairSwap (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h := (Equiv.prodComm (Fin 4 × Fin 4) (Fin 4 × Fin 4)).sum_comp
    (fun p => f p.2.1 p.2.2 p.1.1 p.1.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

theorem sumFour_BCAD (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ c, ∑ a, ∑ d, f a b c d := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

theorem sumFour_BDAC (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ d, ∑ a, ∑ c, f a b c d := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [sumThree_cycle]

/-- The constant-curvature tensor in an orthonormal frame. -/
def unitFrameTensor : CovariantCoordinates 4 := fun a =>
  (if a 1 = a 2 then (1 : ℝ) else 0) * (if a 0 = a 3 then 1 else 0) -
    (if a 0 = a 2 then 1 else 0) * (if a 1 = a 3 then 1 else 0)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem sumFive_moveLast (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, f a b c d e := by
  calc
    _ = ∑ a, ∑ b, ∑ e, ∑ c, ∑ d, f a b c d e := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [sumThree_cycle]
    _ = ∑ a, ∑ e, ∑ b, ∑ c, ∑ d, f a b c d e := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem sumFour_moveLast (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  calc
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [sumThree_cycle]
    _ = _ := by rw [Finset.sum_comm]

theorem sumFive_moveFirst (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
  exact (sumFive_moveLast (fun b c d e a => f a b c d e)).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiating the actual cyclic second Bianchi identity preserves
its derivative and curvature slots, before passage to an orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

def differentiatedBianchiCycle : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 0, 3, 4]
  invFun := ![2, 0, 1, 3, 4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Euclidean tensor pairing is unchanged by an orthogonal frame change. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

/-- Pairing of all components of a covariant tensor in an orthonormal frame. -/
def frameTensorPairing {n : ℕ} (T U : CovariantCoordinates n) : ℝ := ∑ a, T a * U a

def frameTensorSquareNorm {n : ℕ} (T : CovariantCoordinates n) : ℝ := frameTensorPairing T T

def pairingConsEquiv (n : ℕ) :
    (Fin 4 × (Fin n → Fin 4)) ≃ (Fin (n + 1) → Fin 4) where
  toFun p := Fin.cons p.1 p.2
  invFun a := (a 0, fun i => a i.succ)
  left_inv p := by cases p; rfl
  right_inv a := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem sum_tensor_indices_cons {n : ℕ} (f : (Fin (n + 1) → Fin 4) → ℝ) :
    (∑ a, f a) = ∑ d, ∑ a : Fin n → Fin 4, f (Fin.cons d a) := by
  have h := (pairingConsEquiv n).sum_comp f
  have hp : (∑ p : Fin 4 × (Fin n → Fin 4), f (pairingConsEquiv n p)) =
      ∑ d, ∑ a : Fin n → Fin 4, f (Fin.cons d a) := by
    rw [Fintype.sum_prod_type]
    rfl
  exact h.symm.trans hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six-dimensional two-form fiber and its actual Hodge involution.
The coordinate order is 01, 02, 03, 12, 13, 23. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

abbrev TwoFormFour := EuclideanSpace ℝ (Fin 6)

def twoFormHodgeLinear : TwoFormFour ≃ₗ[ℝ] TwoFormFour where
  toFun a := WithLp.toLp 2 ![a 5, -a 4, a 3, a 2, -a 1, a 0]
  invFun a := WithLp.toLp 2 ![a 5, -a 4, a 3, a 2, -a 1, a 0]
  left_inv a := by ext i; fin_cases i <;> simp
  right_inv a := by ext i; fin_cases i <;> simp
  map_add' a b := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' r a := by ext i; fin_cases i <;> simp

theorem twoFormHodge_norm (a : TwoFormFour) : ‖twoFormHodgeLinear a‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  simp [twoFormHodgeLinear, Fin.sum_univ_succ, Real.norm_eq_abs]
  ring

def twoFormHodge : TwoFormFour ≃ₗᵢ[ℝ] TwoFormFour where
  toLinearEquiv := twoFormHodgeLinear
  norm_map' := twoFormHodge_norm

@[simp] theorem twoFormHodge_involutive (a : TwoFormFour) :
    twoFormHodge (twoFormHodge a) = a := twoFormHodgeLinear.left_inv a

end
end PositiveEinsteinFour.Geometry
end


section

/-! The infinitesimal orthonormal-frame action on two-forms preserves the
Hodge splitting and the fiber inner product. This is the local algebra
needed for the induced Levi-Civita connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormSkewAction (b a : TwoFormFour) : TwoFormFour :=
  WithLp.toLp 2 ![
    -b 1 * a 3 + a 1 * b 3 - b 2 * a 4 + a 2 * b 4,
    b 0 * a 3 - a 0 * b 3 - b 2 * a 5 + a 2 * b 5,
    b 0 * a 4 - a 0 * b 4 + b 1 * a 5 - a 1 * b 5,
    -b 0 * a 1 + a 0 * b 1 - b 4 * a 5 + a 4 * b 5,
    -b 0 * a 2 + a 0 * b 2 + b 3 * a 5 - a 3 * b 5,
    -b 1 * a 2 + a 1 * b 2 - b 3 * a 4 + a 3 * b 4]

def twoFormSkewActionLinear (b : TwoFormFour) : TwoFormFour →ₗ[ℝ] TwoFormFour where
  toFun := twoFormSkewAction b
  map_add' a c := by
    ext i
    fin_cases i <;> simp [twoFormSkewAction] <;> ring
  map_smul' r a := by
    ext i
    fin_cases i <;> simp [twoFormSkewAction] <;> ring

theorem twoFormSkewAction_skewAdjoint (b a c : TwoFormFour) :
    inner ℝ (twoFormSkewAction b a) c = -inner ℝ a (twoFormSkewAction b c) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, twoFormSkewAction,
    Fin.sum_univ_succ]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A four-column Gram--Schmidt normalizer with entrywise smooth dependence
on the positive metric matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

abbrev CoordinateColumn := Fin 4 → ℝ

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlowDifferentiability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First variation of a real autonomous ODE. These elementary Taylor,
Grönwall and endpoint lemmas are shared by horizontal-frame and cotangent
Hamiltonian flows. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set Asymptotics
open scoped ContDiff _root_.Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem taylor_remainder_le (f : E → E) {S : Set E} (hS : Convex ℝ S)
    (hf : ∀ q ∈ S, DifferentiableAt ℝ f q)
    (L : ℝ≥0) (hL : LipschitzOnWith L (fderiv ℝ (f)) S)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖f y - f x -
      (fderiv ℝ (f) x) (y - x)‖ ≤
        (L : ℝ) * ‖y - x‖ ^ 2 := by
  let D := fderiv ℝ f x
  let r : E → E := fun z => f z - D z
  have hsegment : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hd (z : E) (hz : z ∈ segment ℝ x y) :
      HasFDerivWithinAt r (fderiv ℝ f z - D) (segment ℝ x y) z :=
    ((hf z (hsegment hz)).hasFDerivAt.sub D.hasFDerivAt).hasFDerivWithinAt
  have hbound (z : E) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ f z - D‖ ≤ (L : ℝ) * ‖y - x‖ := by
    calc
      _ ≤ (L : ℝ) * ‖z - x‖ := hL.norm_sub_le (hsegment hz) hx
      _ ≤ (L : ℝ) * ‖y - x‖ :=
        mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) L.coe_nonneg
  have hb := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le hd hbound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have heq : r y - r x = f y - f x - D (y - x) := by
    dsimp [r]
    rw [map_sub]
    abel
  rw [heq] at hb
  simpa only [pow_two, mul_assoc] using hb


theorem variation_remainder_derivative (f : E → E) (x y : ℝ → E)
    (V : ℝ → E →L[ℝ] E)
    (h : E) (t : ℝ)
    (hx : HasDerivAt x (f (x t)) t)
    (hy : HasDerivAt y (f (y t)) t)
    (hV : HasDerivAt V
      ((fderiv ℝ (f) (x t)).comp (V t)) t) :
    HasDerivAt (fun s => y s - x s - V s h)
      ((fderiv ℝ (f) (x t)) (y t - x t - V t h) +
        (f (y t) - f (x t) -
          (fderiv ℝ (f) (x t)) (y t - x t))) t := by
  have hv := hV.clm_apply (hasDerivAt_const t h)
  simp only [map_zero, add_zero] at hv
  convert (hy.sub hx).sub hv using 1
  all_goals try with_reducible_and_instances rfl
  simp only [ContinuousLinearMap.comp_apply, map_sub]
  abel

theorem variation_quadratic_error (f : E → E) (x y : ℝ → E)
    (V : ℝ → E →L[ℝ] E)
    (h : E) (K L T : ℝ) (hL : 0 ≤ L)
    (hx : ∀ t ∈ Icc 0 T, HasDerivAt x (f (x t)) t)
    (hy : ∀ t ∈ Icc 0 T, HasDerivAt y (f (y t)) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V
      ((fderiv ℝ (f) (x t)).comp (V t)) t)
    (hinit : y 0 = x 0 + h) (hVinit : V 0 = ContinuousLinearMap.id ℝ E)
    (hD : ∀ t ∈ Icc 0 T, ‖fderiv ℝ (f) (x t)‖ ≤ K)
    (htraj : ∀ t ∈ Icc 0 T, ‖y t - x t‖ ≤ Real.exp (K * T) * ‖h‖)
    (hTaylor : ∀ t ∈ Icc 0 T,
      ‖f (y t) - f (x t) -
        (fderiv ℝ (f) (x t)) (y t - x t)‖ ≤
          L * ‖y t - x t‖ ^ 2) :
    ∀ t ∈ Icc 0 T, ‖y t - x t - V t h‖ ≤
      gronwallBound 0 K (L * (Real.exp (K * T)) ^ 2 * ‖h‖ ^ 2) t := by
  let r : ℝ → E := fun t => y t - x t - V t h
  let D : ℝ → E →L[ℝ] E :=
    fun t => fderiv ℝ (f) (x t)
  let err : ℝ → E := fun t =>
    f (y t) - f (x t) -
      D t (y t - x t)
  have hr (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt r (D t (r t) + err t) t :=
    variation_remainder_derivative f x y V h t (hx t ht) (hy t ht) (hV t ht)
  have hrc : ContinuousOn r (Icc 0 T) := fun t ht => (hr t ht).continuousAt.continuousWithinAt
  have hr0 : r 0 = 0 := by simp only [r, hinit, hVinit, ContinuousLinearMap.id_apply]; abel
  have hb (t : ℝ) (ht : t ∈ Ico 0 T) :
      ‖D t (r t) + err t‖ ≤ K * ‖r t‖ + L * (Real.exp (K * T)) ^ 2 * ‖h‖ ^ 2 := by
    have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
    have hsq : ‖y t - x t‖ ^ 2 ≤ (Real.exp (K * T) * ‖h‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (htraj t ht') 2
    calc
      _ ≤ ‖D t (r t)‖ + ‖err t‖ := norm_add_le _ _
      _ ≤ K * ‖r t‖ + L * ‖y t - x t‖ ^ 2 := by
        exact add_le_add ((D t).le_of_opNorm_le (hD t ht') _) (hTaylor t ht')
      _ ≤ K * ‖r t‖ + L * (Real.exp (K * T) * ‖h‖) ^ 2 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hsq hL) _
      _ = _ := by ring
  intro t ht
  have hbound := norm_le_gronwallBound_of_norm_deriv_right_le hrc
    (fun s hs => (hr s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by rw [hr0, norm_zero]) hb t ht
  simpa only [sub_zero] using hbound

omit [NormedSpace ℝ E] in
/-- The Grönwall remainder is uniformly quadratic in the initial increment. -/
theorem gronwall_quadratic (K A T : ℝ) (h : E) :
    gronwallBound 0 K (A * ‖h‖ ^ 2) T = gronwallBound 0 K A T * ‖h‖ ^ 2 := by
  by_cases hK : K = 0
  · subst K
    simp only [gronwallBound_K0]
    ring
  · simp only [gronwallBound_of_K_ne_0 hK]
    ring

/-- A quadratic remainder for a local endpoint map proves the claimed
Fréchet derivative; no differentiability premise on that map is needed. -/
theorem hasFDerivAt_of_quadratic_error
    (F : E → E) (p : E)
    (V : E →L[ℝ] E) (C : ℝ)
    (hb : ∀ᶠ q in 𝓝 p, ‖F q - F p - V (q - p)‖ ≤ C * ‖q - p‖ ^ 2) :
    HasFDerivAt F V p := by
  have hbig : (fun q => F q - F p - V (q - p)) =O[𝓝 p]
      (fun q => ‖q - p‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hb] with q hq
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖q - p‖)] using hq
  rw [hasFDerivAt_iff_isLittleO]
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub p (by norm_num : 1 < 2))

/-- The endpoint map of a local family of genuine solutions has the
variational derivative. All quantitative hypotheses concern the local
vector field and its containing convex neighborhood. -/
theorem hasFDerivAt_flow_endpoint (f : E → E) (α : E × ℝ → E)
    (p : E) (S B : Set E) (hS : S ∈ 𝓝 p)
    (hB : Convex ℝ B) (hf : ∀ z ∈ B, DifferentiableAt ℝ f z)
    (K L : ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (hK : LipschitzOnWith K (f) B)
    (hL : LipschitzOnWith L (fderiv ℝ (f)) B)
    (hD : ∀ z ∈ B, ‖fderiv ℝ (f) z‖ ≤ K)
    (hα0 : ∀ q ∈ S, α (q, 0) = q)
    (hα : ∀ q ∈ S, ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => α (q, s)) (f (α (q, t))) t)
    (hαB : ∀ q ∈ S, ∀ t ∈ Icc 0 T, α (q, t) ∈ B)
    (V : ℝ → E →L[ℝ] E)
    (hV0 : V 0 = ContinuousLinearMap.id ℝ E)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V
      ((fderiv ℝ (f) (α (p, t))).comp (V t)) t) :
    HasFDerivAt (fun q => α (q, T)) (V T) p := by
  have hp : p ∈ S := mem_of_mem_nhds hS
  let A : ℝ := (L : ℝ) * (Real.exp ((K : ℝ) * T)) ^ 2
  apply hasFDerivAt_of_quadratic_error _ p (V T) (gronwallBound 0 K A T)
  filter_upwards [hS] with q hq
  have htraj (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖α (q, t) - α (p, t)‖ ≤ Real.exp ((K : ℝ) * T) * ‖q - p‖ := by
    have hb := dist_le_of_trajectories_ODE_of_mem
      (v := fun _ => f) (s := fun _ => B)
      (fun _ _ => hK)
      (fun s hs => (hα q hq s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hα q hq s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (fun s hs => hαB q hq s (Ico_subset_Icc_self hs))
      (fun s hs => (hα p hp s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hα p hp s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (fun s hs => hαB p hp s (Ico_subset_Icc_self hs))
      (le_refl (dist (α (q, 0)) (α (p, 0)))) t ht
    simp only [hα0 q hq, hα0 p hp, dist_eq_norm, sub_zero] at hb
    calc
      _ ≤ ‖q - p‖ * Real.exp ((K : ℝ) * t) := hb
      _ ≤ ‖q - p‖ * Real.exp ((K : ℝ) * T) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have herr := variation_quadratic_error f
    (fun s => α (p, s)) (fun s => α (q, s)) V (q - p) K L T L.coe_nonneg
    (hα p hp) (hα q hq) hV
    (by rw [hα0 q hq, hα0 p hp]; abel) hV0
    (fun s hs => hD _ (hαB p hp s hs)) htraj
    (fun s hs => taylor_remainder_le f hB hf L hL
      (hαB p hp s hs) (hαB q hq s hs)) T ⟨hT, le_rfl⟩
  rw [show (L : ℝ) * (Real.exp ((K : ℝ) * T)) ^ 2 * ‖q - p‖ ^ 2 =
    A * ‖q - p‖ ^ 2 from rfl, gronwall_quadratic] at herr
  exact herr

end
end PositiveEinsteinFour.FlowCalculus

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlowTimeReversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-variation criterion also applies at negative times, by
reversing the actual autonomous equation. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set
open scoped _root_.Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFDerivAt_flow_endpoint_nonpos (f : E → E) (α : E × ℝ → E)
    (p : E) (S B : Set E) (hS : S ∈ 𝓝 p)
    (hB : Convex ℝ B) (hf : ∀ z ∈ B, DifferentiableAt ℝ f z)
    (K L : ℝ≥0) (T : ℝ) (hT : T ≤ 0)
    (hK : LipschitzOnWith K f B)
    (hL : LipschitzOnWith L (fderiv ℝ f) B)
    (hD : ∀ z ∈ B, ‖fderiv ℝ f z‖ ≤ K)
    (hα0 : ∀ q ∈ S, α (q, 0) = q)
    (hα : ∀ q ∈ S, ∀ t ∈ Icc T 0,
      HasDerivAt (fun s => α (q, s)) (f (α (q, t))) t)
    (hαB : ∀ q ∈ S, ∀ t ∈ Icc T 0, α (q, t) ∈ B)
    (V : ℝ → E →L[ℝ] E)
    (hV0 : V 0 = ContinuousLinearMap.id ℝ E)
    (hV : ∀ t ∈ Icc T 0, HasDerivAt V
      ((fderiv ℝ f (α (p, t))).comp (V t)) t) :
    HasFDerivAt (fun q => α (q, T)) (V T) p := by
  have ht {t : ℝ} (ht : t ∈ Icc 0 (-T)) : -t ∈ Icc T 0 := by
    constructor <;> linarith [ht.1, ht.2]
  have hd (q : E) : fderiv ℝ (fun z => -f z) q = -fderiv ℝ f q := fderiv_fun_neg
  have hKn : LipschitzOnWith K (fun z => -f z) B := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_neg_neg] using hK.dist_le_mul x hx y hy
  have hLn : LipschitzOnWith L (fderiv ℝ (fun z => -f z)) B := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [hd, dist_neg_neg] using hL.dist_le_mul x hx y hy
  have hαr (q : E) (hq : q ∈ S) (t : ℝ) (ht' : t ∈ Icc 0 (-T)) :
      HasDerivAt (fun s => α (q, -s)) (-f (α (q, -t))) t := by
    simpa only [Function.comp_def, neg_one_smul] using
      (hα q hq (-t) (ht ht')).scomp t (hasDerivAt_id t).neg
  have hVr (t : ℝ) (ht' : t ∈ Icc 0 (-T)) :
      HasDerivAt (fun s => V (-s))
        ((fderiv ℝ (fun z => -f z) (α (p, -t))).comp (V (-t))) t := by
    simpa only [Function.comp_def, hd, ContinuousLinearMap.neg_comp, neg_one_smul] using
      (hV (-t) (ht ht')).scomp t (hasDerivAt_id t).neg
  have hr := hasFDerivAt_flow_endpoint (fun z => -f z)
    (fun qt => α (qt.1, -qt.2)) p S B hS hB
    (fun z hz => (hf z hz).neg) K L (-T) (neg_nonneg.mpr hT)
    hKn hLn
    (fun z hz => by simpa only [hd, norm_neg] using hD z hz)
    (by simpa only [neg_zero] using hα0) hαr
    (fun q hq t ht' => hαB q hq (-t) (ht ht'))
    (fun s => V (-s)) (by simpa only [neg_zero] using hV0) hVr
  simpa only [neg_neg] using hr

end
end PositiveEinsteinFour.FlowCalculus

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlowVariationalExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Jointly continuous local solutions of the actual augmented variational
ODE. Only a C² vector field and ordinary Picard existence are used. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set Metric
open scoped ContDiff _root_.Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev VariationSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E × (E →L[ℝ] E)

def variationalField (f : E → E) (q : VariationSpace E) : VariationSpace E :=
  (f q.1, (fderiv ℝ f q.1).comp q.2)

omit [CompleteSpace E] in
theorem variationalField_contDiffAt (f : E → E) (q : VariationSpace E)
    (hf : ContDiffAt ℝ 2 f q.1) : ContDiffAt ℝ 1 (variationalField f) q := by
  have hD : ContDiffAt ℝ 1 (fderiv ℝ f) q.1 := hf.fderiv_right (by norm_num)
  exact ((hf.of_le (by norm_num)).comp q contDiffAt_fst).prodMk
    ((hD.comp q contDiffAt_fst).clm_comp contDiffAt_snd)

/-- A common local interval and continuous parameter dependence for the
base trajectory and its first variational linear map. -/
theorem exists_continuous_local_variational_flow (f : E → E) (p : E)
    (hf : ContDiffAt ℝ 2 f p) (U : Set E) (hU : U ∈ 𝓝 p) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ β : E × ℝ → VariationSpace E,
      ContinuousOn β (closedBall p r ×ˢ Ioo (-ε) ε) ∧
      ∀ q ∈ closedBall p r,
        β (q, 0) = (q, ContinuousLinearMap.id ℝ E) ∧
        ∀ t ∈ Ioo (-ε) ε, (β (q, t)).1 ∈ U ∧
          HasDerivAt (fun s => β (q, s)) (variationalField f (β (q, t))) t := by
  let p₀ : VariationSpace E := (p, ContinuousLinearMap.id ℝ E)
  obtain ⟨ε₀, hε₀, a, r₀, L, K, hr₀, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one (variationalField_contDiffAt f p₀ hf)
  obtain ⟨α, hα, hαc⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  let β : E × ℝ → VariationSpace E := fun qt =>
    α ((qt.1, ContinuousLinearMap.id ℝ E), qt.2)
  have hinit (q : E) (hq : q ∈ closedBall p (r₀ : ℝ)) :
      (q, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ (r₀ : ℝ) := by
    simpa only [mem_closedBall, p₀, Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hq
  have hβc : ContinuousOn β (closedBall p (r₀ : ℝ) ×ˢ Icc (0 - ε₀) (0 + ε₀)) := by
    exact hαc.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd).continuousOn
      (fun qt hqt => ⟨hinit qt.1 hqt.1, hqt.2⟩)
  have hβ0 : β (p, 0) = p₀ := (hα p₀ (mem_closedBall_self (by positivity))).1
  have hr₀' : 0 < (r₀ : ℝ) := hr₀
  have hn : closedBall p (r₀ : ℝ) ×ˢ Icc (0 - ε₀) (0 + ε₀) ∈ 𝓝 (p, (0 : ℝ)) :=
    by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (closedBall_mem_nhds p hr₀')
        (Icc_mem_nhds (by linarith) (by linarith))
  have hnear : ∀ᶠ qt in 𝓝 (p, (0 : ℝ)), (β qt).1 ∈ U :=
    (hβc.continuousAt hn).fst.preimage_mem_nhds (by simpa only [hβ0, p₀] using hU)
  obtain ⟨δ, hδ, hδnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let r : ℝ := min (r₀ : ℝ) (δ / 2)
  let ε : ℝ := min ε₀ (δ / 2)
  have hr : 0 < r := lt_min hr₀' (half_pos hδ)
  have hε : 0 < ε := lt_min hε₀ (half_pos hδ)
  have hsub {q : E} (hq : q ∈ closedBall p r) : q ∈ closedBall p (r₀ : ℝ) :=
    closedBall_subset_closedBall (min_le_left _ _) hq
  have htime {t : ℝ} (ht : t ∈ Ioo (-ε) ε) : t ∈ Ioo (0 - ε₀) (0 + ε₀) := by
    have hle : ε ≤ ε₀ := min_le_left _ _
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨r, hr, ε, hε, β, hβc.mono ?_, fun q hq => ⟨(hα _ (hinit q (hsub hq))).1, ?_⟩⟩
  · rintro ⟨q, t⟩ ⟨hq, ht⟩
    exact ⟨hsub hq, Ioo_subset_Icc_self (htime ht)⟩
  · intro t ht
    constructor
    · apply hδnear
      rw [Prod.dist_eq, max_lt_iff]
      constructor
      · have hqr : dist q p ≤ r := hq
        have hrd : r ≤ δ / 2 := min_le_right _ _
        linarith
      · rw [Real.dist_eq, sub_zero, abs_lt]
        have hεd : ε ≤ δ / 2 := min_le_right _ _
        constructor <;> linarith [ht.1, ht.2]
    · exact ((hα _ (hinit q (hsub hq))).2 t (Ioo_subset_Icc_self (htime ht))).hasDerivAt
        (Icc_mem_nhds (htime ht).1 (htime ht).2)

end
end PositiveEinsteinFour.FlowCalculus

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlowLocalDifferentiability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual differentiability in initial data for a local autonomous flow.
The derivative is obtained from the constructed variational ODE, using the
quadratic remainder estimate; it is not an assumed property of the flow. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set Metric
open scoped ContDiff _root_.Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_differentiable_local_flow (f : E → E) (p : E)
    (hf : ContDiffAt ℝ 2 f p) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∃ α : E × ℝ → E, ∃ V : E × ℝ → E →L[ℝ] E,
        ContinuousOn α (ball p r ×ˢ Ioo (-ε) ε) ∧
        ContinuousOn V (ball p r ×ˢ Ioo (-ε) ε) ∧
        ∀ q ∈ ball p r,
          α (q, 0) = q ∧ V (q, 0) = ContinuousLinearMap.id ℝ E ∧
          (∀ t ∈ Ioo (-ε) ε,
            HasDerivAt (fun s => α (q, s)) (f (α (q, t))) t ∧
            HasDerivAt (fun s => V (q, s))
              ((fderiv ℝ f (α (q, t))).comp (V (q, t))) t) ∧
          ∀ t ∈ Ioo (-ε) ε, HasFDerivAt (fun x => α (x, t)) (V (q, t)) q := by
  have hf1 : ContDiffAt ℝ 1 f p := hf.of_le (by norm_num)
  have hDf : ContDiffAt ℝ 1 (fderiv ℝ f) p := hf.fderiv_right (by norm_num)
  obtain ⟨K, U, hU, hK⟩ := hf1.exists_lipschitzOnWith
  obtain ⟨L, W, hW, hL⟩ := hDf.exists_lipschitzOnWith
  have hdiff : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ f z :=
    (hf1.eventually (by norm_num)).mono fun z hz => hz.differentiableAt (by norm_num)
  obtain ⟨a, ha, hasub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (Filter.inter_mem hU hW) hdiff)
  let B := ball p a
  have hBdiff (z : E) (hz : z ∈ B) : DifferentiableAt ℝ f z := (hasub hz).2
  have hBK : LipschitzOnWith K f B := hK.mono (fun z hz => (hasub hz).1.1)
  have hBL : LipschitzOnWith L (fderiv ℝ f) B := hL.mono (fun z hz => (hasub hz).1.2)
  obtain ⟨r, hr, ε, hε, β, hβc, hβ⟩ :=
    exists_continuous_local_variational_flow f p hf B (ball_mem_nhds p ha)
  let α : E × ℝ → E := fun z => (β z).1
  let V : E × ℝ → E →L[ℝ] E := fun z => (β z).2
  have hα0 (q : E) (hq : q ∈ ball p r) : α (q, 0) = q :=
    congrArg Prod.fst (hβ q (ball_subset_closedBall hq)).1
  have hV0 (q : E) (hq : q ∈ ball p r) : V (q, 0) = ContinuousLinearMap.id ℝ E :=
    congrArg Prod.snd (hβ q (ball_subset_closedBall hq)).1
  have hsol (q : E) (hq : q ∈ ball p r) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt (fun s => α (q, s)) (f (α (q, t))) t ∧
      HasDerivAt (fun s => V (q, s))
        ((fderiv ℝ f (α (q, t))).comp (V (q, t))) t :=
    ⟨((hβ q (ball_subset_closedBall hq)).2 t ht).2.fst,
      ((hβ q (ball_subset_closedBall hq)).2 t ht).2.snd⟩
  have hBmem (q : E) (hq : q ∈ ball p r) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      α (q, t) ∈ B := ((hβ q (ball_subset_closedBall hq)).2 t ht).1
  have hsub : ball p r ×ˢ Ioo (-ε) ε ⊆ closedBall p r ×ˢ Ioo (-ε) ε :=
    fun z hz => ⟨ball_subset_closedBall hz.1, hz.2⟩
  refine ⟨r, hr, ε, hε, α, V, hβc.fst.mono hsub, hβc.snd.mono hsub,
    fun q hq => ⟨hα0 q hq, hV0 q hq, hsol q hq, ?_⟩⟩
  intro t ht
  by_cases hnonneg : 0 ≤ t
  · have htime {s : ℝ} (hs : s ∈ Icc 0 t) : s ∈ Ioo (-ε) ε := by
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    exact hasFDerivAt_flow_endpoint f α q (ball p r) B (isOpen_ball.mem_nhds hq)
      (convex_ball p a) hBdiff K L t hnonneg hBK hBL
      (fun z hz => norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hz) hBK)
      hα0 (fun x hx s hs => (hsol x hx s (htime hs)).1)
      (fun x hx s hs => hBmem x hx s (htime hs))
      (fun s => V (q, s)) (hV0 q hq) (fun s hs => (hsol q hq s (htime hs)).2)
  · have htime {s : ℝ} (hs : s ∈ Icc t 0) : s ∈ Ioo (-ε) ε := by
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    exact hasFDerivAt_flow_endpoint_nonpos f α q (ball p r) B (isOpen_ball.mem_nhds hq)
      (convex_ball p a) hBdiff K L t (le_of_lt (lt_of_not_ge hnonneg)) hBK hBL
      (fun z hz => norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hz) hBK)
      hα0 (fun x hx s hs => (hsol x hx s (htime hs)).1)
      (fun x hx s hs => hBmem x hx s (htime hs))
      (fun s => V (q, s)) (hV0 q hq) (fun s hs => (hsol q hq s (htime hs)).2)

end
end PositiveEinsteinFour.FlowCalculus

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlowJointDifferentiability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual time derivative and the constructed initial-data derivative
give the joint derivative of a local autonomous flow. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set
open scoped _root_.Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasStrictFDerivAt_joint_flow
    (f : E → E) (α : E × ℝ → E) (V : E × ℝ → E →L[ℝ] E)
    (u : E × ℝ)
    (hinitial : ∀ᶠ z in 𝓝 u,
      HasFDerivAt (fun q => α (q, z.2)) (V z) z.1)
    (htime : ∀ᶠ z in 𝓝 u,
      HasDerivAt (fun t => α (z.1, t)) (f (α z)) z.2)
    (hV : ContinuousAt V u)
    (hvelocity : ContinuousAt (fun z => f (α z)) u) :
    HasStrictFDerivAt α
      ((V u).coprod (ContinuousLinearMap.toSpanSingleton ℝ (f (α u)))) u := by
  have ht : ∀ᶠ z in 𝓝 u, HasFDerivAt (fun t => α (z.1, t))
      (ContinuousLinearMap.toSpanSingleton ℝ (f (α z))) z.2 :=
    htime.mono fun z hz => hz.hasFDerivAt
  have hc : ContinuousAt
      (fun z => ContinuousLinearMap.toSpanSingleton ℝ (f (α z))) u :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).continuous.continuousAt.comp
      hvelocity
  exact hasStrictFDerivAt_uncurry_coprod
    (f := fun q t => α (q, t))
    (f₁ := fun q t => V (q, t))
    (f₂ := fun q t => ContinuousLinearMap.toSpanSingleton ℝ (f (α (q, t))))
    hinitial ht hV hc

/-- A C² autonomous field has an actual jointly differentiable local flow.
The linear part in the initial state is supplied by the variational ODE. -/
theorem exists_jointly_differentiable_local_flow [CompleteSpace E]
    (f : E → E) (p : E) (hf : ContDiffAt ℝ 2 f p) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∃ α : E × ℝ → E, ∃ V : E × ℝ → E →L[ℝ] E,
        ContinuousOn α (Metric.ball p r ×ˢ Ioo (-ε) ε) ∧
        ContinuousOn V (Metric.ball p r ×ˢ Ioo (-ε) ε) ∧
        ∀ q ∈ Metric.ball p r,
          α (q, 0) = q ∧ V (q, 0) = ContinuousLinearMap.id ℝ E ∧
          ∀ t ∈ Ioo (-ε) ε,
            HasDerivAt (fun s => α (q, s)) (f (α (q, t))) t ∧
            HasDerivAt (fun s => V (q, s))
              ((fderiv ℝ f (α (q, t))).comp (V (q, t))) t ∧
            HasStrictFDerivAt α
              ((V (q, t)).coprod
                (ContinuousLinearMap.toSpanSingleton ℝ (f (α (q, t))))) (q, t) := by
  obtain ⟨r₀, hr₀, ε₀, hε₀, α, V, hαc, hVc, hsol⟩ :=
    exists_differentiable_local_flow f p hf
  have hfnear : ∀ᶠ z in 𝓝 p, ContinuousAt f z :=
    (hf.eventually (by norm_num)).mono fun z hz => hz.continuousAt
  have hp0 : α (p, 0) = p := (hsol p (Metric.mem_ball_self hr₀)).1
  have hpD : (p, (0 : ℝ)) ∈ Metric.ball p r₀ ×ˢ Ioo (-ε₀) ε₀ :=
    ⟨Metric.mem_ball_self hr₀, by constructor <;> linarith⟩
  have hαat : ContinuousAt α (p, 0) :=
    hαc.continuousAt ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds hpD)
  have hnear : ∀ᶠ z in 𝓝 (p, (0 : ℝ)), ContinuousAt f (α z) :=
    hαat.tendsto.eventually (by simpa only [hp0] using hfnear)
  obtain ⟨δ, hδ, hδnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let r := min r₀ (δ / 2)
  let ε := min ε₀ (δ / 2)
  have hr : 0 < r := lt_min hr₀ (half_pos hδ)
  have hε : 0 < ε := lt_min hε₀ (half_pos hδ)
  have hsub : Metric.ball p r ×ˢ Ioo (-ε) ε ⊆
      Metric.ball p r₀ ×ˢ Ioo (-ε₀) ε₀ := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    refine ⟨Metric.ball_subset_ball (min_le_left _ _) hq, ?_⟩
    have he : ε ≤ ε₀ := min_le_left _ _
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨r, hr, ε, hε, α, V, hαc.mono hsub, hVc.mono hsub, ?_⟩
  intro q hq
  have hq₀ : q ∈ Metric.ball p r₀ := Metric.ball_subset_ball (min_le_left _ _) hq
  refine ⟨(hsol q hq₀).1, (hsol q hq₀).2.1, ?_⟩
  intro t ht
  have hu₀ : (q, t) ∈ Metric.ball p r₀ ×ˢ Ioo (-ε₀) ε₀ :=
    hsub (show (q, t) ∈ Metric.ball p r ×ˢ Ioo (-ε) ε from ⟨hq, ht⟩)
  have hnhds : Metric.ball p r₀ ×ˢ Ioo (-ε₀) ε₀ ∈ 𝓝 (q, t) :=
    (Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds hu₀
  have hi : ∀ᶠ z in 𝓝 (q, t),
      HasFDerivAt (fun x => α (x, z.2)) (V z) z.1 := by
    filter_upwards [hnhds] with z hz
    exact (hsol z.1 hz.1).2.2.2 z.2 hz.2
  have ht' : ∀ᶠ z in 𝓝 (q, t),
      HasDerivAt (fun s => α (z.1, s)) (f (α z)) z.2 := by
    filter_upwards [hnhds] with z hz
    exact ((hsol z.1 hz.1).2.2.1 z.2 hz.2).1
  have hfc : ContinuousAt f (α (q, t)) := by
    apply hδnear
    rw [Prod.dist_eq, dist_zero_right, Real.norm_eq_abs, max_lt_iff]
    constructor
    · exact (Metric.mem_ball.mp hq).trans_le (min_le_right _ _) |>.trans
        (half_lt_self hδ)
    · exact (abs_lt.mpr ht).trans_le (min_le_right _ _) |>.trans
        (half_lt_self hδ)
  refine ⟨((hsol q hq₀).2.2.1 t hu₀.2).1,
    ((hsol q hq₀).2.2.1 t hu₀.2).2, ?_⟩
  exact hasStrictFDerivAt_joint_flow f α V (q, t) hi ht'
    (hVc.continuousAt hnhds) (hfc.comp (hαc.continuousAt hnhds))

end
end PositiveEinsteinFour.FlowCalculus

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlowGermUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform local uniqueness for parameterized actual ODE solutions.
This identifies the existing flow with its variational lifts on a whole
neighborhood, as required for higher derivatives in the initial data. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set Metric Filter
open scoped ContDiff _root_.Topology

noncomputable section

variable {P E : Type*} [NormedAddCommGroup P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem local_solution_family_eventuallyEq (f : E → E) (α β : P × ℝ → E)
    (p : P) (hαc : ContinuousAt α (p, 0)) (hβc : ContinuousAt β (p, 0))
    (hinit : ∀ᶠ q in 𝓝 p, α (q, 0) = β (q, 0))
    (hα : ∀ᶠ z in 𝓝 (p, (0 : ℝ)),
      HasDerivAt (fun t => α (z.1, t)) (f (α z)) z.2)
    (hβ : ∀ᶠ z in 𝓝 (p, (0 : ℝ)),
      HasDerivAt (fun t => β (z.1, t)) (f (β z)) z.2)
    (hf : ContDiffAt ℝ 1 f (α (p, 0))) : α =ᶠ[𝓝 (p, (0 : ℝ))] β := by
  obtain ⟨K, U, hU, hLip⟩ := hf.exists_lipschitzOnWith
  have hαU : ∀ᶠ z in 𝓝 (p, (0 : ℝ)), α z ∈ U := hαc.preimage_mem_nhds hU
  have hβU : ∀ᶠ z in 𝓝 (p, (0 : ℝ)), β z ∈ U :=
    hβc.preimage_mem_nhds (by simpa only [hinit.self_of_nhds] using hU)
  have hi : ∀ᶠ z in 𝓝 (p, (0 : ℝ)), α (z.1, 0) = β (z.1, 0) := by
    have ht : Tendsto (fun z : P × ℝ => z.1) (𝓝 (p, 0)) (𝓝 p) :=
      continuous_fst.continuousAt
    exact ht.eventually hinit
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
    (hα.and (hβ.and (hαU.and (hβU.and hi))))
  have hh : 0 < δ / 2 := half_pos hδ
  have hrect (q : P) (hq : q ∈ ball p (δ / 2)) (t : ℝ)
      (ht : t ∈ Ioo (-(δ / 2)) (δ / 2)) :
      dist (q, t) (p, (0 : ℝ)) < δ := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨(mem_ball.mp hq).trans (half_lt_self hδ),
      ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hz : (0 : ℝ) ∈ Ioo (-(δ / 2)) (δ / 2) := ⟨by linarith, hh⟩
  have hn : ball p (δ / 2) ×ˢ Ioo (-(δ / 2)) (δ / 2) ∈ 𝓝 (p, (0 : ℝ)) :=
    (isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨mem_ball_self hh, hz⟩
  filter_upwards [hn] with z hz'
  have heq := ODE_solution_unique_of_mem_Ioo
    (v := fun _ => f) (s := fun _ => U)
    (fun _ _ => hLip) hz
    (fun t ht => ⟨(hnear (hrect z.1 hz'.1 t ht)).1,
      (hnear (hrect z.1 hz'.1 t ht)).2.2.1⟩)
    (fun t ht => ⟨(hnear (hrect z.1 hz'.1 t ht)).2.1,
      (hnear (hrect z.1 hz'.1 t ht)).2.2.2.1⟩)
    (hnear (hrect z.1 hz'.1 0 hz)).2.2.2.2
  exact heq hz'.2

end
end PositiveEinsteinFour.FlowCalculus

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlowVariationalRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variational lift loses exactly one finite derivative. -/

namespace PositiveEinsteinFour.FlowCalculus

open scoped ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem variationalField_contDiffAt_order (n : ℕ) (f : E → E)
    (q : VariationSpace E) (hf : ContDiffAt ℝ (n + 1 : ℕ) f q.1) :
    ContDiffAt ℝ n (variationalField f) q := by
  have hD : ContDiffAt ℝ n (fderiv ℝ f) q.1 := hf.fderiv_right (by first | simp | exact_mod_cast le_top)
  exact ((hf.of_le (by exact_mod_cast Nat.le_succ n)).comp q contDiffAt_fst).prodMk
    ((hD.comp q contDiffAt_fst).clm_comp contDiffAt_snd)

end
end PositiveEinsteinFour.FlowCalculus

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlowFiniteRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite smooth dependence of actual local ODE solutions on initial data.
The induction applies the existing first-variation construction to its own
variational field, and uses uniqueness to identify the resulting derivatives. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set Metric Filter
open scoped ContDiff _root_.Topology

noncomputable section

universe u

theorem local_flow_contDiffAt_finite (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (f : E → E) (α : E × ℝ → E) (p : E),
      ContDiffAt ℝ (n + 2 : ℕ) f p →
      ContDiffAt ℝ 0 α (p, 0) →
      (∀ᶠ q in 𝓝 p, α (q, 0) = q) →
      (∀ᶠ z in 𝓝 (p, (0 : ℝ)),
        HasDerivAt (fun t => α (z.1, t)) (f (α z)) z.2) →
      ContDiffAt ℝ n α (p, 0) := by
  induction n with
  | zero =>
    intro E _ _ _ f α p _ hc _ _
    exact hc
  | succ n ih =>
    intro E _ _ _ f α p hf hc hi hs
    have hf2 : ContDiffAt ℝ 2 f p := hf.of_le (by exact_mod_cast Nat.le_add_left 2 (n + 1))
    obtain ⟨r, hr, ε, hε, A, V, hAc, hVc, hAV⟩ :=
      exists_jointly_differentiable_local_flow f p hf2
    let U := ball p r ×ˢ Ioo (-ε) ε
    have hz : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    have hU : U ∈ 𝓝 (p, (0 : ℝ)) :=
      (isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨mem_ball_self hr, hz⟩
    have hA0 : ∀ᶠ q in 𝓝 p, A (q, 0) = q := by
      filter_upwards [ball_mem_nhds p hr] with q hq
      exact (hAV q hq).1
    have hAs : ∀ᶠ z in 𝓝 (p, (0 : ℝ)),
        HasDerivAt (fun t => A (z.1, t)) (f (A z)) z.2 := by
      filter_upwards [hU] with z hz
      exact ((hAV z.1 hz.1).2.2 z.2 hz.2).1
    have hAeq : α =ᶠ[𝓝 (p, (0 : ℝ))] A := by
      have hiA : ∀ᶠ q in 𝓝 p, α (q, 0) = A (q, 0) := by
        filter_upwards [hi, hA0] with q hq hAq
        exact hq.trans hAq.symm
      apply local_solution_family_eventuallyEq f α A p hc.continuousAt
        (hAc.continuousAt hU) hiA hs hAs
      simpa only [hi.self_of_nhds] using hf2.of_le (by norm_num)
    let B : E × ℝ → VariationSpace E := fun z => (A z, V z)
    let p₀ : VariationSpace E := (p, ContinuousLinearMap.id ℝ E)
    have hB0 : ∀ᶠ q in 𝓝 p, B (q, 0) = (q, ContinuousLinearMap.id ℝ E) := by
      filter_upwards [ball_mem_nhds p hr] with q hq
      exact Prod.ext (hAV q hq).1 (hAV q hq).2.1
    have hBc : ContinuousAt B (p, 0) :=
      (hAc.continuousAt hU).prodMk (hVc.continuousAt hU)
    have hBs : ∀ᶠ z in 𝓝 (p, (0 : ℝ)),
        HasDerivAt (fun t => B (z.1, t)) (variationalField f (B z)) z.2 := by
      filter_upwards [hU] with z hz
      exact (((hAV z.1 hz.1).2.2 z.2 hz.2).1).prodMk
        (((hAV z.1 hz.1).2.2 z.2 hz.2).2.1)
    have hf3 : ContDiffAt ℝ 3 f p := hf.of_le (by exact_mod_cast Nat.le_add_left 3 n)
    have hg2 : ContDiffAt ℝ 2 (variationalField f) p₀ :=
      variationalField_contDiffAt_order 2 f p₀ hf3
    obtain ⟨r₁, hr₁, ε₁, hε₁, G, W, hGc, _, hGW⟩ :=
      exists_jointly_differentiable_local_flow (variationalField f) p₀ hg2
    let U₁ := ball p₀ r₁ ×ˢ Ioo (-ε₁) ε₁
    have hz₁ : (0 : ℝ) ∈ Ioo (-ε₁) ε₁ := ⟨by linarith, hε₁⟩
    have hU₁ : U₁ ∈ 𝓝 (p₀, (0 : ℝ)) :=
      (isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨mem_ball_self hr₁, hz₁⟩
    have hG0 : ∀ᶠ q in 𝓝 p₀, G (q, 0) = q := by
      filter_upwards [ball_mem_nhds p₀ hr₁] with q hq
      exact (hGW q hq).1
    have hGs : ∀ᶠ z in 𝓝 (p₀, (0 : ℝ)),
        HasDerivAt (fun t => G (z.1, t)) (variationalField f (G z)) z.2 := by
      filter_upwards [hU₁] with z hz
      exact ((hGW z.1 hz.1).2.2 z.2 hz.2).1
    have hg : ContDiffAt ℝ (n + 2 : ℕ) (variationalField f) p₀ :=
      variationalField_contDiffAt_order (n + 2) f p₀ (by simpa [Nat.add_assoc] using hf)
    have hGn : ContDiffAt ℝ n G (p₀, 0) := ih (VariationSpace E)
      (variationalField f) G p₀ hg (contDiffAt_zero.mpr ⟨U₁, hU₁, hGc⟩) hG0 hGs
    let H : E × ℝ → VariationSpace E × ℝ :=
      fun z => ((z.1, ContinuousLinearMap.id ℝ E), z.2)
    have hH : ContDiff ℝ ∞ H :=
      (contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd
    have hH0 : H (p, 0) = (p₀, 0) := rfl
    have hHq : Continuous (fun q : E => (q, ContinuousLinearMap.id ℝ E)) :=
      continuous_id.prodMk continuous_const
    have hGHn : ContDiffAt ℝ n (G ∘ H) (p, 0) :=
      hGn.comp (p, 0) (hH.contDiffAt.of_le (by first | simp | exact_mod_cast le_top))
    have hGH0 : ∀ᶠ q in 𝓝 p,
        (G ∘ H) (q, 0) = (q, ContinuousLinearMap.id ℝ E) := by
      have ht : Tendsto (fun q : E => (q, ContinuousLinearMap.id ℝ E))
          (𝓝 p) (𝓝 p₀) := hHq.continuousAt
      exact ht.eventually hG0
    have hGHs : ∀ᶠ z in 𝓝 (p, (0 : ℝ)),
        HasDerivAt (fun t => (G ∘ H) (z.1, t))
          (variationalField f ((G ∘ H) z)) z.2 := by
      have ht : Tendsto H (𝓝 (p, 0)) (𝓝 (p₀, 0)) := hH.continuous.continuousAt
      exact ht.eventually hGs
    have hBGeq : B =ᶠ[𝓝 (p, (0 : ℝ))] (G ∘ H) := by
      apply local_solution_family_eventuallyEq (variationalField f) B (G ∘ H) p hBc
        hGHn.continuousAt
      · filter_upwards [hB0, hGH0] with q hBq hGq
        exact hBq.trans hGq.symm
      · exact hBs
      · exact hGHs
      · simpa only [hB0.self_of_nhds] using hg2.of_le (by norm_num)
    have hBn : ContDiffAt ℝ n B (p, 0) :=
      hGHn.congr_of_eventuallyEq hBGeq
    let D : E × ℝ → E × ℝ →L[ℝ] E := fun z =>
      (V z).coprod (ContinuousLinearMap.toSpanSingleton ℝ (f (A z)))
    have hfn : ContDiffAt ℝ n f p := hf.of_le (by exact_mod_cast Nat.le_add_right n 3)
    have hvel : ContDiffAt ℝ n (fun z => f (A z)) (p, 0) := by
      have hAinit : A (p, 0) = p := hA0.self_of_nhds
      have hfp : ContDiffAt ℝ n f (A (p, 0)) := by rwa [hAinit]
      exact hfp.comp (p, 0) hBn.fst
    have hspan : ContDiffAt ℝ n
        (fun z => ContinuousLinearMap.toSpanSingleton ℝ (f (A z))) (p, 0) :=
      (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).contDiff.contDiffAt.comp
        (p, 0) hvel
    have hDn : ContDiffAt ℝ n D (p, 0) := by
      change ContDiffAt ℝ n (fun z =>
        (V z).comp (ContinuousLinearMap.fst ℝ E ℝ) +
        (ContinuousLinearMap.toSpanSingleton ℝ (f (A z))).comp
          (ContinuousLinearMap.snd ℝ E ℝ)) (p, 0)
      exact (hBn.snd.clm_comp contDiffAt_const).add (hspan.clm_comp contDiffAt_const)
    have hAn : ContDiffAt ℝ (n + 1 : ℕ) A (p, 0) := by
      apply contDiffAt_succ_iff_hasFDerivAt.mpr
      refine ⟨D, ⟨U, hU, ?_⟩, hDn⟩
      intro z hz
      exact (((hAV z.1 hz.1).2.2 z.2 hz.2).2.2).hasFDerivAt
    exact hAn.congr_of_eventuallyEq hAeq

end
end PositiveEinsteinFour.FlowCalculus

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized Euclidean four-dimensional Gaussian used in the local
heat construction. All integrals use the actual Euclidean volume measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory GaussianFourier

noncomputable section

def fourHeatGaussian (t : ℝ) (x : FourSpace) : ℝ :=
  ((4 * Real.pi * t) ^ 2)⁻¹ * Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2)

theorem fourHeatGaussian_continuous (t : ℝ) : Continuous (fourHeatGaussian t) := by
  exact continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul (continuous_norm.pow 2)))

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianDifferential
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate derivatives of the Euclidean heat kernel in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators

noncomputable section

theorem fourHeatGaussian_hasFDerivAt (t : ℝ) (x : FourSpace) :
    HasFDerivAt (fourHeatGaussian t)
      (fourHeatGaussian t x • (-(4 * t)⁻¹ • (2 • innerSL ℝ x))) x := by
  have h := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul
    (-(4 * t)⁻¹)).exp).const_mul (((4 * Real.pi * t) ^ 2)⁻¹)
  unfold fourHeatGaussian
  simpa only [smul_smul, mul_assoc] using h

theorem fourHeatGaussian_partial (t : ℝ) (ht : t ≠ 0) (i : Fin 4) (x : FourSpace) :
    partialDeriv (fourHeatGaussian t) i x =
      (-x i / (2 * t)) * fourHeatGaussian t x := by
  unfold partialDeriv
  rw [(fourHeatGaussian_hasFDerivAt t x).fderiv]
  have hb : coordinateVector i = (EuclideanSpace.basisFun (Fin 4) ℝ) i := by
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
  simp only [smul_apply, innerSL_apply_apply, hb, EuclideanSpace.inner_basisFun_real,
    smul_eq_mul]
  field_simp
  ring

theorem fourHeatGaussian_coordinate_hasFDerivAt (i : Fin 4) (x : FourSpace) :
    HasFDerivAt (fun y : FourSpace => y i)
      (innerSL ℝ ((EuclideanSpace.basisFun (Fin 4) ℝ) i)) x := by
  convert (innerSL ℝ ((EuclideanSpace.basisFun (Fin 4) ℝ) i)).hasFDerivAt (x := x) using 1
  all_goals try with_reducible_and_instances rfl
  funext y
  rw [innerSL_apply_apply, real_inner_comm, EuclideanSpace.inner_basisFun_real]

theorem fourHeatGaussian_partial_partial (t : ℝ) (ht : t ≠ 0)
    (i j : Fin 4) (x : FourSpace) :
    partialDeriv (partialDeriv (fourHeatGaussian t) i) j x =
      (x i * x j / (4 * t ^ 2) - (if i = j then 1 else 0) / (2 * t)) *
        fourHeatGaussian t x := by
  have heq : partialDeriv (fourHeatGaussian t) i =
      fun y => (-y i / (2 * t)) * fourHeatGaussian t y := by
    funext y
    exact fourHeatGaussian_partial t ht i y
  rw [heq]
  have hc := ((fourHeatGaussian_coordinate_hasFDerivAt i x).neg.mul_const ((2 * t)⁻¹))
  have hd := hc.mul (fourHeatGaussian_hasFDerivAt t x)
  simp only [← div_eq_mul_inv, Pi.neg_apply] at hd
  change HasFDerivAt (fun y : FourSpace => -y i / (2 * t) * fourHeatGaussian t y) _ x at hd
  unfold partialDeriv
  rw [hd.fderiv]
  have hb : coordinateVector j = (EuclideanSpace.basisFun (Fin 4) ℝ) j := by
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
  simp only [add_apply, smul_apply, innerSL_apply_apply, hb, neg_apply]
  simp only [EuclideanSpace.inner_basisFun_real]
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, if_true]
    field_simp
    ring
  · simp only [hij, Ne.symm hij, ite_false, if_false]
    field_simp
    ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianEquation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized Gaussian solves the actual flat heat equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators

noncomputable section

theorem fourHeatGaussian_hasDerivAt_time (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    HasDerivAt (fun s => fourHeatGaussian s x)
      ((‖x‖ ^ 2 / (4 * t ^ 2) - 2 / t) * fourHeatGaussian t x) t := by
  have ht4 : 4 * t ≠ 0 := mul_ne_zero (by norm_num) ht.ne'
  have hp : 4 * Real.pi * t ≠ 0 := by positivity
  have ha := (((hasDerivAt_id t).const_mul (4 * Real.pi)).pow 2).inv (pow_ne_zero 2 hp)
  have hb := (((((hasDerivAt_id t).const_mul 4).inv ht4).neg).mul_const (‖x‖ ^ 2)).exp
  have hh := ha.mul hb
  refine hh.congr_deriv ?_
  · simp only [fourHeatGaussian, id_eq, Pi.inv_apply, Pi.pow_apply, Pi.neg_apply, mul_one]
    field_simp
    ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianTimeRegularity
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint positive-time continuity of the Gaussian and its actual time derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped _root_.Topology

noncomputable section

def fourHeatGaussianTimeFactor (t : ℝ) (x : FourSpace) : ℝ :=
  ‖x‖ ^ 2 / (4 * t ^ 2) - 2 / t

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_LocalCoordinateMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer a local image-measure identity through measurable coordinate
maps with an actual left inverse. No invariant-measure statement is assumed. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem measure_eq_of_map_eq_of_leftInverse_ae {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ₁ μ₂ : Measure X)
    (f : X → Y) (r : Y → X) (hf : Measurable f) (hr : Measurable r)
    (h₁ : ∀ᵐ x ∂μ₁, r (f x) = x) (h₂ : ∀ᵐ x ∂μ₂, r (f x) = x)
    (heq : Measure.map f μ₁ = Measure.map f μ₂) : μ₁ = μ₂ := by
  have hleft (μ : Measure X) (h : ∀ᵐ x ∂μ, r (f x) = x) :
      Measure.map r (Measure.map f μ) = μ := by
    rw [Measure.map_map hr hf]
    calc
      _ = Measure.map id μ := Measure.map_congr h
      _ = μ := Measure.map_id
  exact (hleft μ₁ h₁).symm.trans ((congrArg (Measure.map r) heq).trans (hleft μ₂ h₂))

theorem coordinate_map_restrict {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (C : ℝ≥0∞) (f : X → Y) (hf : Measurable f)
    (S : Set X) (T : Set Y) (hfi : InjOn f S) (hfT : MapsTo f S T)
    (hchart : Measure.map f (μ.restrict S) = C • ν.restrict T)
    (V : Set X) (hVS : V ⊆ S) (himage : MeasurableSet (f '' V)) :
    Measure.map f (μ.restrict V) = C • ν.restrict (f '' V) := by
  have hpre : f ⁻¹' (f '' V) ∩ S = V := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, heq⟩, hx⟩
      exact (hfi (hVS hy) hx heq) ▸ hy
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, hVS hx⟩
  have hsub : f '' V ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfT (hVS hx)
  calc
    _ = (Measure.map f (μ.restrict S)).restrict (f '' V) := by
      rw [Measure.restrict_map hf himage, Measure.restrict_restrict (hf himage), hpre]
    _ = C • ν.restrict (f '' V) := by
      rw [hchart, Measure.restrict_smul, Measure.restrict_restrict himage,
        inter_eq_left.mpr hsub]

theorem local_image_measure_of_coordinates {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (C : ℝ≥0∞)
    (f : X → Y) (r : Y → X) (hf : Measurable f) (hr : Measurable r)
    (S : Set X) (T : Set Y) (hS : MeasurableSet S)
    (hleft : ∀ x ∈ S, r (f x) = x) (hfT : MapsTo f S T)
    (hchart : Measure.map f (μ.restrict S) = C • ν.restrict T)
    (Φ : X → X) (F : Y → Y) (hΦ : Measurable Φ) (hF : Measurable F)
    (U : Set X) (hU : MeasurableSet U) (hUS : U ⊆ S) (hΦS : Φ '' U ⊆ S)
    (hΦU : MeasurableSet (Φ '' U)) (hfU : MeasurableSet (f '' U))
    (hfΦU : MeasurableSet (f '' (Φ '' U)))
    (hconj : ∀ x ∈ U, f (Φ x) = F (f x))
    (hvolume : Measure.map F (ν.restrict (f '' U)) = ν.restrict (F '' (f '' U))) :
    Measure.map Φ (μ.restrict U) = μ.restrict (Φ '' U) := by
  have hfi : InjOn f S := by
    intro x hx y hy heq
    exact (hleft x hx).symm.trans ((congrArg r heq).trans (hleft y hy))
  have hu := coordinate_map_restrict μ ν C f hf S T hfi hfT hchart U hUS hfU
  have hw := coordinate_map_restrict μ ν C f hf S T hfi hfT hchart
    (Φ '' U) hΦS hfΦU
  have himage : F '' (f '' U) = f '' (Φ '' U) := by
    simp only [image_image]
    apply image_congr
    intro x hx
    exact (hconj x hx).symm
  have hpush : Measure.map f (Measure.map Φ (μ.restrict U)) =
      Measure.map f (μ.restrict (Φ '' U)) := by
    calc
      _ = Measure.map F (Measure.map f (μ.restrict U)) := by
        rw [Measure.map_map hf hΦ, Measure.map_map hF hf]
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem hU] with x hx
        exact hconj x hx
      _ = C • ν.restrict (f '' (Φ '' U)) := by
        rw [hu, Measure.map_smul, hvolume, himage]
      _ = _ := hw.symm
  have hsupport : ∀ᵐ x ∂Measure.map Φ (μ.restrict U), x ∈ S := by
    apply (ae_map_iff hΦ.aemeasurable hS).mpr
    filter_upwards [ae_restrict_mem hU] with x hx
    exact hΦS ⟨x, hx, rfl⟩
  apply measure_eq_of_map_eq_of_leftInverse_ae _ _ f r hf hr _ _ hpush
  · filter_upwards [hsupport] with x hx
    exact hleft x hx
  · filter_upwards [ae_restrict_mem hΦU] with x hx
    exact hleft x (hΦS hx)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricChartLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chart map is Lipschitz on a sufficiently small Riemannian ball.
Short paths between points of the smaller ball stay in the neighborhood
where the chart differential is bounded. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M]

theorem iInf_open_interval_p0 (a b : ℝ≥0∞) (hab : a < b) :
    (⨅ r : {r : ℝ≥0∞ // a < r ∧ r < b}, (r : ℝ≥0∞)) = a := by
  apply iInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · intro r
    exact r.property.1.le
  · intro w hw
    obtain ⟨r, har, hr⟩ := exists_between (lt_min hw hab)
    exact ⟨⟨r, har, hr.trans_le (min_le_right _ _)⟩,
      hr.trans_le (min_le_left _ _)⟩

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeightedCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The regularity premise in the radial Riemann sums follows from ordinary
bounded curvature and bounded curvature derivative along the frame flow. -/

namespace PositiveEinsteinFour.Averages

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sineWeight_abs_le_two (t : ℝ) : |sineWeight t| ≤ 2 := by
  rw [abs_of_nonneg (sineWeight_nonneg t)]
  unfold sineWeight
  linarith [Real.neg_one_le_cos (2 * Real.pi * t)]

/-- A bounded differentiable curve with bounded derivative supplies the
global Lipschitz estimate used by the sine-mode discretization. -/
theorem sineWeighted_rescale_lipschitz {f f' : ℝ → E} {B D : ℝ}
    (hderiv : ∀ s, HasDerivAt f (f' s) s)
    (hbound : ∀ s, ‖f s‖ ≤ B) (hbound' : ∀ s, ‖f' s‖ ≤ D)
    (t a b : ℝ) :
    ‖sineWeight a • f (t * a) - sineWeight b • f (t * b)‖ ≤
      (2 * Real.pi * B + 2 * D * |t|) * |a - b| := by
  have hf (x y : ℝ) : ‖f x - f y‖ ≤ D * |x - y| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := Set.univ) (fun z _ => (hderiv z).hasDerivWithinAt)
        (fun z _ => hbound' z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  have hid : sineWeight a • f (t * a) - sineWeight b • f (t * b) =
      (sineWeight a - sineWeight b) • f (t * a) +
        sineWeight b • (f (t * a) - f (t * b)) := by module
  rw [hid]
  calc
    _ ≤ ‖(sineWeight a - sineWeight b) • f (t * a)‖ +
        ‖sineWeight b • (f (t * a) - f (t * b))‖ := norm_add_le _ _
    _ = |sineWeight a - sineWeight b| * ‖f (t * a)‖ +
        |sineWeight b| * ‖f (t * a) - f (t * b)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (2 * Real.pi * |a - b|) * B + 2 * (D * |t * a - t * b|) := by
      apply add_le_add
      · exact mul_le_mul (Jacobi.sineWeight_lipschitz a b) (hbound _)
          (norm_nonneg _) (by positivity)
      · exact mul_le_mul (sineWeight_abs_le_two b) (hf _ _)
          (norm_nonneg _) (by norm_num)
    _ = _ := by rw [← mul_sub, abs_mul]; ring

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicJacobiAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite algebra relating the linearized coordinate geodesic
equation to the curvature convention used by the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

abbrev JacobiCoordinateVector := Fin 4 → ℝ

def jacobiConnection (Γ : Fin 4 → Mat4) (v : JacobiCoordinateVector) : Mat4 :=
  ∑ i, v i • Γ i

def jacobiConnectionDerivative (D : Fin 4 → Fin 4 → Mat4)
    (v w : JacobiCoordinateVector) : Mat4 := ∑ i, ∑ j, (v i * w j) • D i j

def jacobiCurvature (Γ : Fin 4 → Mat4) (D : Fin 4 → Fin 4 → Mat4)
    (v w : JacobiCoordinateVector) : Mat4 :=
  ∑ i, ∑ j, (v i * w j) • (D i j - D j i + Γ i * Γ j - Γ j * Γ i)

theorem weighted_matrix_swap (D : Fin 4 → Fin 4 → Mat4)
    (v w : JacobiCoordinateVector) :
    (∑ i, ∑ j, (v i * w j) • D j i) = ∑ i, ∑ j, (w i * v j) • D i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

theorem jacobiConnection_mul (Γ : Fin 4 → Mat4)
    (v w : JacobiCoordinateVector) :
    jacobiConnection Γ v * jacobiConnection Γ w =
      ∑ i, ∑ j, (v i * w j) • (Γ i * Γ j) := by
  simp only [jacobiConnection, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

theorem jacobiCurvature_eq (Γ : Fin 4 → Mat4) (D : Fin 4 → Fin 4 → Mat4)
    (v w : JacobiCoordinateVector) :
    jacobiCurvature Γ D v w =
      jacobiConnectionDerivative D v w - jacobiConnectionDerivative D w v +
        jacobiConnection Γ v * jacobiConnection Γ w -
          jacobiConnection Γ w * jacobiConnection Γ v := by
  simp only [jacobiCurvature, smul_sub, smul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  rw [weighted_matrix_swap D v w, weighted_matrix_swap (fun i j => Γ i * Γ j) v w,
    ← jacobiConnection_mul Γ v w, ← jacobiConnection_mul Γ w v]
  rfl

theorem jacobiConnection_mulVec_comm (Γ : Fin 4 → Mat4)
    (hΓ : ∀ a i j, Γ i a j = Γ j a i) (v w : JacobiCoordinateVector) :
    jacobiConnection Γ v *ᵥ w = jacobiConnection Γ w *ᵥ v := by
  ext a
  simp only [jacobiConnection, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hΓ a i j]
  ring

theorem jacobiConnectionDerivative_mulVec_comm (D : Fin 4 → Fin 4 → Mat4)
    (hD : ∀ r a i j, D r i a j = D r j a i)
    (v w u : JacobiCoordinateVector) :
    jacobiConnectionDerivative D v w *ᵥ u =
      jacobiConnectionDerivative D v u *ᵥ w := by
  have hm (w : JacobiCoordinateVector) : jacobiConnectionDerivative D v w =
      ∑ i, v i • jacobiConnection (D i) w := by
    simp only [jacobiConnectionDerivative, jacobiConnection, Finset.smul_sum, smul_smul]
  calc
    _ = ∑ i, v i • (jacobiConnection (D i) w *ᵥ u) := by
      rw [hm w, Matrix.sum_mulVec]
      simp only [Matrix.smul_mulVec]
    _ = ∑ i, v i • (jacobiConnection (D i) u *ᵥ w) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [jacobiConnection_mulVec_comm (D i) (hD i)]
    _ = _ := by
      rw [hm u, Matrix.sum_mulVec]
      simp only [Matrix.smul_mulVec]

/-- The coordinate variation equation implies the covariant Jacobi
equation. Only torsion freedom and its differentiated identity enter. -/
theorem linearized_geodesic_curvature_identity
    (Γ : Fin 4 → Mat4) (D : Fin 4 → Fin 4 → Mat4)
    (hΓ : ∀ a i j, Γ i a j = Γ j a i)
    (hD : ∀ r a i j, D r i a j = D r j a i)
    (v a y w b : JacobiCoordinateVector)
    (ha : a = -(jacobiConnection Γ v *ᵥ v))
    (hb : b = -(jacobiConnectionDerivative D y v *ᵥ v) -
      jacobiConnection Γ w *ᵥ v - jacobiConnection Γ v *ᵥ w) :
    b + jacobiConnectionDerivative D v v *ᵥ y + jacobiConnection Γ a *ᵥ y +
      (2 : ℝ) • (jacobiConnection Γ v *ᵥ w) +
      jacobiConnection Γ v *ᵥ (jacobiConnection Γ v *ᵥ y) +
      jacobiCurvature Γ D y v *ᵥ v = 0 := by
  have ha' : jacobiConnection Γ a *ᵥ y =
      -(jacobiConnection Γ y *ᵥ (jacobiConnection Γ v *ᵥ v)) := by
    rw [jacobiConnection_mulVec_comm Γ hΓ a y, ha, Matrix.mulVec_neg]
  rw [hb, ha', jacobiConnectionDerivative_mulVec_comm D hD v v y,
    jacobiConnection_mulVec_comm Γ hΓ w v, jacobiCurvature_eq,
    Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    jacobiConnection_mulVec_comm Γ hΓ v y]
  module

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual orientation double cover, obtained by applying the determinant
sign representation to the tangent bundle's transition functions. Its two-point
fibers are glued by the genuine derivatives of chart changes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle Filter _root_.Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def orientationSignChange (a : ℝ) (s : Bool) : Bool := if 0 < a then s else !s

theorem orientationSignChange_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (s : Bool) :
    orientationSignChange b (orientationSignChange a s) = orientationSignChange (b * a) s := by
  by_cases hpa : 0 < a <;> by_cases hpb : 0 < b
  · simp only [orientationSignChange, ite_eq_left hpa, ite_eq_left hpb, ite_eq_left (mul_pos hpb hpa)]
  · have hbn : b < 0 := lt_of_le_of_ne (le_of_not_gt hpb) hb
    simp only [orientationSignChange, ite_eq_left hpa, ite_eq_right hpb,
      ite_eq_right (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hbn.le hpa.le))]
  · have han : a < 0 := lt_of_le_of_ne (le_of_not_gt hpa) ha
    simp only [orientationSignChange, ite_eq_right hpa, ite_eq_left hpb,
      ite_eq_right (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hpb.le han.le))]
  · have han : a < 0 := lt_of_le_of_ne (le_of_not_gt hpa) ha
    have hbn : b < 0 := lt_of_le_of_ne (le_of_not_gt hpb) hb
    simp only [orientationSignChange, ite_eq_right hpa, ite_eq_right hpb,
      ite_eq_left (mul_pos_of_neg_of_neg hbn han), Bool.not_not]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Actual normalized Weyl tensors and their first three covariant derivatives
have the same chart transition law in every slot. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem sum_cross_pairs (f h : Fin 4 → Fin 4 → ℝ) :
    (∑ p, ∑ q, ∑ r, ∑ s, f p s * h q r) =
      (∑ p, ∑ s, f p s) * (∑ q, ∑ r, h q r) := by
  calc
    _ = ∑ p, ∑ q, ∑ r, (∑ s, f p s) * h q r := by
      simp only [Finset.sum_mul]
    _ = ∑ p, (∑ s, f p s) * (∑ q, ∑ r, h q r) := by
      simp only [Finset.mul_sum]
    _ = _ := by simp only [Finset.sum_mul]

theorem sum_parallel_pairs (f h : Fin 4 → Fin 4 → ℝ) :
    (∑ p, ∑ q, ∑ r, ∑ s, f p r * h q s) =
      (∑ p, ∑ r, f p r) * (∑ q, ∑ s, h q s) := by
  calc
    _ = ∑ p, ∑ q, ∑ r, f p r * (∑ s, h q s) := by
      simp only [Finset.mul_sum]
    _ = ∑ p, ∑ q, (∑ r, f p r) * (∑ s, h q s) := by
      simp only [Finset.sum_mul]
    _ = ∑ p, (∑ r, f p r) * (∑ q, ∑ s, h q s) := by
      simp only [Finset.mul_sum]
    _ = _ := by simp only [Finset.sum_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual invariant probability on the oriented orthogonal matrix
fiber. This is the compact fiber measure for the frame-bundle construction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory

noncomputable section

abbrev OrientedOrthogonalFour := Matrix.specialOrthogonalGroup (Fin 4) ℝ

instance instIsTopologicalGroupSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour : IsTopologicalGroup OrientedOrthogonalFour where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    change Continuous (fun p : OrientedOrthogonalFour × OrientedOrthogonalFour =>
      p.1.val * p.2.val)
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun S : OrientedOrthogonalFour => star S.val)
    exact continuous_subtype_val.star

instance instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour : MeasurableSpace OrientedOrthogonalFour := borel OrientedOrthogonalFour
instance instBorelSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour : BorelSpace OrientedOrthogonalFour := ⟨rfl⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Sharp endpoint estimates in coordinates given by a fixed linear
isomorphism. Only the path argument changes; the metric is the actual
Riemannian path metric throughout. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M]

theorem iInf_open_interval_p1 (a b : ℝ≥0∞) (hab : a < b) :
    (⨅ r : {r : ℝ≥0∞ // a < r ∧ r < b}, (r : ℝ≥0∞)) = a := by
  apply iInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · intro r
    exact r.property.1.le
  · intro w hw
    obtain ⟨r, har, hr⟩ := exists_between (lt_min hw hab)
    exact ⟨⟨r, har, hr.trans_le (min_le_right _ _)⟩,
      hr.trans_le (min_le_left _ _)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first-order exterior and codifferential symbols on a two-form jet,
including the exact quadratic identity used in the Weitzenböck formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators

noncomputable section

theorem sum3_swap_first (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ i, ∑ j, ∑ k, f j i k := Finset.sum_comm

theorem sum3_swap_last (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ i, ∑ j, ∑ k, f i k j := by
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

theorem sum3_cycle (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ i, ∑ j, ∑ k, f k i j :=
  (sum3_swap_first f).trans (sum3_swap_last (fun i j k => f j i k))

def twoFormExteriorComponent (A : Fin 4 → Fin 4 → Fin 4 → ℝ) (i j k : Fin 4) : ℝ :=
  A i j k - A j i k + A k i j

def twoFormCodiffComponent (A : Fin 4 → Fin 4 → Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  -∑ i, A i i j

theorem twoFormExterior_square_sum (A : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hA : ∀ i j k, A i k j = -A i j k) :
    (∑ i, ∑ j, ∑ k, twoFormExteriorComponent A i j k ^ 2) =
      3 * (∑ i, ∑ j, ∑ k, A i j k ^ 2) -
        6 * (∑ i, ∑ j, ∑ k, A i j k * A j i k) := by
  have hS₁ : (∑ i, ∑ j, ∑ k, A j i k ^ 2) = ∑ i, ∑ j, ∑ k, A i j k ^ 2 :=
    (sum3_swap_first (fun i j k => A i j k ^ 2)).symm
  have hS₂ : (∑ i, ∑ j, ∑ k, A k i j ^ 2) = ∑ i, ∑ j, ∑ k, A i j k ^ 2 :=
    (sum3_cycle (fun i j k => A i j k ^ 2)).symm
  have hE : (∑ i, ∑ j, ∑ k, A i j k * A k i j) =
      -(∑ i, ∑ j, ∑ k, A i j k * A j i k) := by
    rw [sum3_swap_last]
    calc
      _ = ∑ i, ∑ j, ∑ k, -(A i j k * A j i k) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [hA i j k, neg_mul]
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hF : (∑ i, ∑ j, ∑ k, A j i k * A k i j) =
      ∑ i, ∑ j, ∑ k, A i j k * A j i k := by
    rw [sum3_swap_first]
    calc
      _ = -(∑ i, ∑ j, ∑ k, A i j k * A k i j) := by
        simp only [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [hA k i j, mul_neg]
      _ = _ := by rw [hE, neg_neg]
  calc
    _ = (∑ i, ∑ j, ∑ k, A i j k ^ 2) + (∑ i, ∑ j, ∑ k, A j i k ^ 2) +
        (∑ i, ∑ j, ∑ k, A k i j ^ 2) - 2 * (∑ i, ∑ j, ∑ k, A i j k * A j i k) +
        2 * (∑ i, ∑ j, ∑ k, A i j k * A k i j) -
        2 * (∑ i, ∑ j, ∑ k, A j i k * A k i j) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      unfold twoFormExteriorComponent
      ring
    _ = _ := by rw [hS₁, hS₂, hE, hF]; ring

def twoFormDeRhamQuadratic (A : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  (1 / 6 : ℝ) * (∑ i, ∑ j, ∑ k, twoFormExteriorComponent A i j k ^ 2) +
    ∑ k, twoFormCodiffComponent A k ^ 2

theorem twoFormDeRhamQuadratic_nonneg (A : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    0 ≤ twoFormDeRhamQuadratic A := by
  unfold twoFormDeRhamQuadratic
  positivity

theorem twoFormDeRhamQuadratic_eq (A : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hA : ∀ i j k, A i k j = -A i j k) :
    twoFormDeRhamQuadratic A = (1 / 2 : ℝ) * (∑ i, ∑ j, ∑ k, A i j k ^ 2) +
      (∑ i, ∑ j, ∑ k, A i i k * A j j k) -
      (∑ i, ∑ j, ∑ k, A i j k * A j i k) := by
  have hc : (∑ k, twoFormCodiffComponent A k ^ 2) =
      ∑ i, ∑ j, ∑ k, A i i k * A j j k := by
    change (∑ k, (-(∑ i, A i i k)) ^ 2) = _
    simp only [neg_sq]
    simp only [pow_two]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  unfold twoFormDeRhamQuadratic
  rw [twoFormExterior_square_sum A hA, hc]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The contraction used by the curvature action on two-forms commutes
with actual orthogonal changes of frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem sum_two_indices (f : (Fin 2 → Fin 4) → ℝ) :
    (∑ a, f a) = ∑ i, ∑ j, f ![i, j] := by
  simp only [sum_tensor_indices_cons, Fintype.sum_unique]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  congr 1

theorem sum_four_indices_p1 (f : (Fin 4 → Fin 4) → ℝ) :
    (∑ a, f a) = ∑ i, ∑ j, ∑ k, ∑ l, f ![i,j,k,l] := by
  simp only [sum_tensor_indices_cons, Fintype.sum_unique]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  congr 1

def twoTensorContraction (R : CovariantCoordinates 4) (T : CovariantCoordinates 2) :
    CovariantCoordinates 2 := fun a => ∑ c, ∑ d, R ![a 0, a 1, c, d] * T ![c, d]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature action on the six two-form coordinates. The
minus sign matches the convention R(i,j,k,l) = <R(i,j)k,l>. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoTensorContractionLinear (R : CovariantCoordinates 4) :
    CovariantCoordinates 2 →ₗ[ℝ] CovariantCoordinates 2 where
  toFun := twoTensorContraction R
  map_add' S T := by
    funext a
    simp only [twoTensorContraction, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r T := by
    funext a
    simp only [twoTensorContraction, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuous dependence of the finite-dimensional curvature action on
the actual four-tensor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoTensorContractionFamily : CovariantCoordinates 4 →ₗ[ℝ]
    (CovariantCoordinates 2 →ₗ[ℝ] CovariantCoordinates 2) where
  toFun := twoTensorContractionLinear
  map_add' R S := by
    apply LinearMap.ext
    intro T
    funext a
    change twoTensorContraction (R + S) T a = twoTensorContraction R T a + twoTensorContraction S T a
    simp only [twoTensorContraction, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r R := by
    apply LinearMap.ext
    intro T
    funext a
    change twoTensorContraction (r • R) T a = r * twoTensorContraction R T a
    simp only [twoTensorContraction, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous flow that fixes the radial coordinate and preserves the
ambient product measure preserves every energy shell. The continuity step
upgrades the usual almost-everywhere conclusion to every positive radius. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory MeasureTheory.Measure Set Filter TopologicalSpace
open scoped ENNReal _root_.Topology

noncomputable section

abbrev PositiveRadius := Ioi (0 : ℝ)

instance radialCubicMeasure_openPos :
    Measure.IsOpenPosMeasure (Measure.volumeIoiPow 3) := by
  let μ : Measure PositiveRadius := Measure.comap Subtype.val (volume : Measure ℝ)
  let : Measure.IsOpenPosMeasure μ := by
    constructor
    intro U hU hne
    change Measure.comap Subtype.val (volume : Measure ℝ) U ≠ 0
    rw [comap_subtype_coe_apply measurableSet_Ioi]
    exact (isOpen_Ioi.isOpenMap_subtype_val U hU).measure_ne_zero volume (hne.image _)
  constructor
  intro U hU hne
  change (μ.withDensity (fun r => ENNReal.ofReal (r.val ^ 3))) U ≠ 0
  have hm : Measurable (fun r : PositiveRadius => ENNReal.ofReal (r.val ^ 3)) :=
    (ENNReal.continuous_ofReal.comp (continuous_subtype_val.pow 3)).measurable
  have he : {r : PositiveRadius | ENNReal.ofReal (r.val ^ 3) ≠ 0} = univ := by
    apply Set.eq_univ_of_forall
    intro r
    exact (ENNReal.ofReal_pos.mpr (pow_pos r.property 3)).ne'
  intro hzero
  have hz := (withDensity_apply_eq_zero (μ := μ) (s := U) hm).mp hzero
  rw [he, univ_inter] at hz
  exact hU.measure_ne_zero μ hne hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual six-dimensional Weitzenböck potential and its first two
matrix traces. These are local algebraic identities, not an index formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

abbrev TwoFormMatrix := Matrix (Fin 6) (Fin 6) ℝ

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite curvature contraction in the two-form Weitzenböck identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormCurvature_sum_two_indices (f : (Fin 2 → Fin 4) → ℝ) :
    (∑ v, f v) = ∑ i, ∑ j, f ![i,j] := by
  simp only [sum_tensor_indices_cons, Fintype.sum_unique]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  congr 1

theorem twoFormCurvature_sum_four_indices (f : (Fin 4 → Fin 4) → ℝ) :
    (∑ v, f v) = ∑ i, ∑ j, ∑ k, ∑ l, f ![i,j,k,l] := by
  simp only [sum_tensor_indices_cons, Fintype.sum_unique]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  congr 1

theorem sum_four_swap_middle_last (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, f i l k j := by
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ k, ∑ j, ∑ l, f i j k l := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ j, f i j k l := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature tensor norm is four times the square norm of
its matrix on the six increasing index pairs. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem sum_four_components (f : (Fin 4 → Fin 4) → ℝ) :
    (∑ a, f a) = ∑ i, ∑ j, ∑ k, ∑ l, f ![i,j,k,l] := by
  simp only [sum_tensor_indices_cons, Fintype.sum_unique]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  congr 1

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full inverse-frame variational equation. The head is the radial
component, whose acceleration vanishes; its zero-position solution is linear. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The zero-position radial solution is exactly linear. -/
theorem radial_jacobi_pair_eq (y z : ℝ → ℝ) (w a b : ℝ)
    (hzero : (0 : ℝ) ∈ Ioo a b) (hy0 : y 0 = 0) (hz0 : z 0 = w)
    (hy : ∀ s ∈ Ioo a b, HasDerivAt y (z s) s)
    (hz : ∀ s ∈ Ioo a b, HasDerivAt z 0 s) :
    ∀ s ∈ Ioo a b, y s = s * w ∧ z s = w := by
  have hconst (s : ℝ) (hs : s ∈ Ioo a b) : z s = w := by
    rw [← hz0]
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun r hr => (hz r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hz r hr).deriv) hs hzero
  have hdiff (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (fun r => y r - r * w) 0 s := by
    have h := (hy s hs).sub ((hasDerivAt_id s).mul_const w)
    simpa only [hconst s hs, one_mul, sub_self, Pi.sub_apply, id_eq] using! h
  intro s hs
  refine ⟨?_, hconst s hs⟩
  have h := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun r hr => (hdiff r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hdiff r hr).deriv) hs hzero
  change y s - s * w = y 0 - 0 * w at h
  rw [hy0, zero_mul, sub_zero] at h
  exact sub_eq_zero.mp h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Alternating smooth covariant fields give the existing actual
six-coordinate two-form sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def CovariantTwoFormSkew (T : M → CovariantCoordinates 2) : Prop :=
  ∀ x i j, T x ![j,i] = -T x ![i,j]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A local minimum of the actual energy forces the second derivative to
be nonnegative.  The finite-piece version cancels the chart boundary
terms before applying this elementary one-variable fact. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology BigOperators

noncomputable section

theorem finite_piece_secondDeriv (n : ℕ) (E : ℕ → ℝ → ℝ) (D : ℕ → ℝ)
    (hfd : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i < n, DifferentiableAt ℝ (E i) s)
    (hD : ∀ i < n, HasDerivAt (deriv (E i)) (D i) 0) :
    HasDerivAt (deriv (fun s => ∑ i ∈ Finset.range n, E i s))
      (∑ i ∈ Finset.range n, D i) 0 := by
  have hs := HasDerivAt.fun_sum (fun i (hi : i ∈ Finset.range n) =>
    hD i (Finset.mem_range.mp hi))
  have heq : deriv (fun s => ∑ i ∈ Finset.range n, E i s) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => ∑ i ∈ Finset.range n, deriv (E i) s) := by
    filter_upwards [hfd] with s hs
    exact deriv_fun_sum (fun i hi => hs i (Finset.mem_range.mp hi))
  exact hs.congr_of_eventuallyEq heq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual two-form Hodge star as a six-dimensional matrix, and
its action on the first pair of curvature indices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormHodgeMatrix : TwoFormMatrix :=
  !![0,0,0,0,0,1;
     0,0,0,0,-1,0;
     0,0,0,1,0,0;
     0,0,1,0,0,0;
     0,-1,0,0,0,0;
     1,0,0,0,0,0]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exterior derivative from smooth one-forms to two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

def twoCovariantAlternation (T : CovariantCoordinates 2) : CovariantCoordinates 2 :=
  fun a => T a - T (a ∘ Equiv.swap 0 1)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Vanishing of the intrinsic L2 norm detects the zero smooth one-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem oneForm_squareNorm (T : CovariantCoordinates 1) :
    frameTensorSquareNorm T = ∑ i, T ![i] ^ 2 := by
  unfold frameTensorSquareNorm frameTensorPairing
  rw [sum_tensor_indices_cons]
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro i _
  have he (a : Fin 0 → Fin 4) : T (Fin.cons i a) = T ![i] := by
    congr 1
    ext k
    fin_cases k
    rfl
  rw [he]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Endpoint curves are affine in a common chart.  In any overlapping chart,
their first and second jets are the actual derivatives of the chart change.
Restriction followed by constant extension gives globally continuous jet
functions without requiring a chart change to be regular outside its overlap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

variable [IsManifold I4 ∞ M]

theorem intervalExtension_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) {a b s : ℝ} (hab : a ≤ b)
    (hs : s ∈ Ioo a b) {v : E} (hf : HasDerivAt f v s) :
    HasDerivAt (IccExtend hab (fun q : Icc a b => f q)) v s := by
  apply hf.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
  exact IccExtend_of_mem hab _ ⟨ht.1.le, ht.2.le⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity of the actual exterior derivative on smooth one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoCovariantAlternationLinear : CovariantCoordinates 2 →ₗ[ℝ] CovariantCoordinates 2 where
  toFun := twoCovariantAlternation
  map_add' T U := by funext a; simp only [twoCovariantAlternation, Pi.add_apply]; ring
  map_smul' r T := by
    funext a
    simp only [twoCovariantAlternation, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification of an actual normal variation with the columns of
the globally chosen Jacobi solution. Uniqueness uses only the first-order
equation and its initial values. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix Set
open scoped _root_.Topology NNReal Matrix.Norms.L2Operator

noncomputable section

def jacobiColumn (v : Fin 3 → ℝ) : NormalMatrix :=
  fun i j => if j = 0 then v i else 0

theorem mul_jacobiColumn (R : NormalMatrix) (v : Fin 3 → ℝ) :
    R * jacobiColumn v = jacobiColumn (R *ᵥ v) := by
  ext i j
  by_cases hj : j = 0
  · subst j
    simp only [Matrix.mul_apply, jacobiColumn, ite_true, if_true, Matrix.mulVec, dotProduct]
  · simp only [Matrix.mul_apply, jacobiColumn, hj, ite_false, if_false, mul_zero,
      Finset.sum_const_zero]

end
end PositiveEinsteinFour.Jacobi

end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Two elementary assembly steps for the actual Hamiltonian-volume proof:
local image-measure identities glue, and a neighborhood of preserving times
for the complete unit tangent flow gives every real time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

/-- Local image-measure identities for a homeomorphism determine its
pushforward on the whole second-countable space. -/
theorem measurePreserving_of_local_image {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (f : X ≃ₜ X) (μ : Measure X)
    (hlocal : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      Measure.map f (μ.restrict U) = μ.restrict (f '' U)) :
    MeasurePreserving f μ μ := by
  choose U hU hx hm using hlocal
  obtain ⟨s, hs, hcover⟩ := countable_cover_nhds (fun x => (hU x).mem_nhds (hx x))
  have himage : ⋃ x ∈ s, f '' U x = (univ : Set X) := by
    rw [← image_iUnion₂, hcover, image_univ_of_surjective f.surjective]
  refine ⟨f.measurable, Measure.ext_of_biUnion_eq_univ hs himage ?_⟩
  intro x _
  rw [f.measurableEmbedding.restrict_map μ (f '' U x),
    preimage_image_eq _ f.injective]
  exact hm x

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local comparison on an open chart domain. The measures outside the
chart play no role, so neighborhoods are required only at its points. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem measure_restrict_eq_of_local {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [SecondCountableTopology X] (μ ν : Measure X) (T : Set X)
    (hlocal : ∀ x ∈ T, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ T ∧
      μ.restrict U = ν.restrict U) : μ.restrict T = ν.restrict T := by
  choose U hU hx hsub heq using hlocal
  obtain ⟨s, hs, hcover⟩ := (HereditarilyLindelofSpace.isLindelof T).elim_nhds_subcover'
    U (fun x hxT => (hU x hxT).mem_nhds (hx x hxT))
  have hcov : (⋃ x ∈ s, U (x : X) x.property) = T := by
    apply Subset.antisymm _ hcover
    apply iUnion₂_subset
    intro x _
    exact hsub x x.property
  rw [← hcov]
  exact (Measure.restrict_biUnion_congr hs).mpr (fun x _ => heq x x.property)

theorem measure_restrict_le_of_local {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ ν : Measure X) (T : Set X) (hT : IsOpen T)
    (hlocal : ∀ x ∈ T, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ T ∧
      μ.restrict U ≤ ν.restrict U) : μ.restrict T ≤ ν.restrict T := by
  have hinf : (μ ⊓ ν).restrict T = μ.restrict T ⊓ ν.restrict T := by
    simpa only [Set.image_insert_eq, Set.image_singleton, sInf_pair] using
      (Measure.restrict_sInf_eq_sInf_restrict (m := {μ, ν})
        (by simp : ({μ, ν} : Set (Measure X)).Nonempty) hT.measurableSet)
  apply inf_eq_left.mp
  rw [← hinf]
  apply measure_restrict_eq_of_local
  intro x hx
  obtain ⟨U, hU, hxU, hUT, hle⟩ := hlocal x hx
  refine ⟨U, hU, hxU, hUT, ?_⟩
  have hi : (μ ⊓ ν).restrict U = μ.restrict U ⊓ ν.restrict U := by
    simpa only [Set.image_insert_eq, Set.image_singleton, sInf_pair] using
      (Measure.restrict_sInf_eq_sInf_restrict (m := {μ, ν})
        (by simp : ({μ, ν} : Set (Measure X)).Nonempty) hU.measurableSet)
  rw [hi, inf_eq_left.mpr hle]

theorem measure_restrict_le_of_sharp_local_comparison {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ ν : Measure X) (T : Set X) (hT : IsOpen T)
    (hlocal : ∀ a : ℝ≥0∞, a < 1 → ∀ x ∈ T, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ U ⊆ T ∧ (a • μ).restrict U ≤ ν.restrict U) :
    μ.restrict T ≤ ν.restrict T := by
  apply Measure.le_iff.mpr
  intro A _
  apply ENNReal.le_of_forall_lt_one_mul_le
  intro a ha
  have h := measure_restrict_le_of_local (a • μ) ν T hT (hlocal a ha)
  simpa only [Measure.restrict_smul, Measure.smul_apply, smul_eq_mul] using h A

end
end PositiveEinsteinFour.Geometry
end


section

/-! Put the actual metric and density comparisons into the same
constant-density form. All estimates are on genuine chart measures. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

theorem ofReal_sqrt_four (x : ℝ) (hx : 0 ≤ x) :
    (ENNReal.ofReal (Real.sqrt x)) ^ (4 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  rw [show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
  congr 1
  calc
    Real.sqrt x ^ 4 = (Real.sqrt x ^ 2) ^ 2 := by ring
    _ = x ^ 2 := by rw [Real.sq_sqrt hx]

theorem ofReal_inv_sqrt_four (x : ℝ) (hx : 0 < x) :
    (ENNReal.ofReal (1 / Real.sqrt x)) ^ (4 : ℝ) = (ENNReal.ofReal (x ^ 2))⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.mpr hx),
    show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast, ← ENNReal.inv_pow]
  rw [← ENNReal.rpow_natCast _ 4]
  norm_num only [Nat.cast_ofNat]
  rw [ofReal_sqrt_four x hx.le]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact invariant radius slabs. A finite collection of the constructed
Hamiltonian charts provides one positive time valid throughout each slab. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem finite_positive_lower_bound_p0 {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ ε > (0 : ℝ), ∀ i ∈ s, ε ≤ f i := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _hf
    exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    intro hf
    obtain ⟨ε, hε, he⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min (f i) ε, lt_min (hf i (Finset.mem_insert_self _ _)) hε, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (he j hj)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identify metric Hausdorff measure in a chart from the proved sharp
metric comparison and the continuous density, using local measure gluing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

theorem density_comparison_parameter (a : ℝ) (ha : 0 ≤ a) (haone : a < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      a * (1 + δ) ^ 2 ≤ 1 - δ ∧ a * (1 + δ) ≤ (1 - δ) ^ 2 := by
  let δ := (1 - a) / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδone : δ < 1 := by dsimp [δ]; linarith
  have heq : a = 1 - 8 * δ := by dsimp [δ]; ring
  refine ⟨δ, hδ, hδone, ?_, ?_⟩
  · rw [heq]
    nlinarith [sq_nonneg δ, mul_nonneg hδ.le (sq_nonneg δ)]
  · rw [heq]
    nlinarith [sq_nonneg δ]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Frame-bundle integral realizations of the intrinsic two-form pairings. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem frameTensorPairing_three (A B : CovariantCoordinates 3) :
    frameTensorPairing A B = ∑ i, ∑ j, ∑ k, A ![i,j,k] * B ![i,j,k] := by
  unfold frameTensorPairing
  simp only [sum_tensor_indices_cons, Fintype.sum_unique]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  congr 1

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exterior and trace tensors of a two-form covariant derivative.
Their norms are independent of the orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormCodiffTensor (A : CovariantCoordinates 3) : CovariantCoordinates 1 :=
  fun v => -∑ i, A ![i,i,v 0]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rough Green pairing is bounded by the L2 value norm.
This is the estimate needed to close the covariant derivative graph. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

abbrev TwoTensorEuclidean := EuclideanSpace ℝ (Fin 2 → Fin 4)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite tensor estimates for the chart localization of two-forms.
The bounds involve the actual value and covariant energy density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem tensor_component_sq_le {n : ℕ} (T : CovariantCoordinates n) (a : Fin n → Fin 4) :
    |T a| ^ 2 ≤ frameTensorSquareNorm T := by
  rw [sq_abs]
  simpa only [frameTensorSquareNorm, frameTensorPairing, pow_two] using
    (Finset.single_le_sum (fun b _ => sq_nonneg (T b)) (Finset.mem_univ a))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The traced second covariant derivative is an actual smooth two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def twoFormTraceLinear : CovariantCoordinates 4 →ₗ[ℝ] CovariantCoordinates 2 where
  toFun T v := ∑ i, T (Fin.cons i (Fin.cons i v))
  map_add' T U := by funext v; simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r T := by funext v; simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatDriftTransportAlgebra
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite contractions in the coordinate transformation of the drift. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem heat_inverse_congruence_component (J a : Mat4) (p q : Fin 4) :
    (∑ i, ∑ j, J p i * a i j * J q j) = (J * a * Jᵀ) p q := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem heat_weighted_connection_trace (J a H : Mat4) (D : Fin 4 → Mat4)
    (hH : J * a * Jᵀ = H) (r : Fin 4) :
    (∑ i, ∑ j, a i j * (weightedConnection J D i * J) r j) =
      ∑ p, ∑ q, H p q * D p r q := by
  have he (i j : Fin 4) : a i j * (weightedConnection J D i * J) r j =
      ∑ p, ∑ q, (J p i * a i j * J q j) * D p r q := by
    simp only [weightedConnection, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [he]
  calc
    _ = ∑ p, ∑ q, ∑ i, ∑ j, (J p i * a i j * J q j) * D p r q := by
      conv_lhs =>
        arg 2
        ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      conv_lhs =>
        arg 2
        ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      simp_rw [← Finset.sum_mul]
      rw [heat_inverse_congruence_component, hH]

theorem heat_drift_transport_algebra (J a H : Mat4) (C P D : Fin 4 → Mat4)
    (hC : ∀ i, J * C i = P i + weightedConnection J D i * J)
    (hH : J * a * Jᵀ = H) (r : Fin 4) :
    (∑ k, J r k * (∑ i, ∑ j, a i j * C i k j)) -
      (∑ i, ∑ j, a i j * P i r j) = ∑ p, ∑ q, H p q * D p r q := by
  have he : (∑ k, J r k * (∑ i, ∑ j, a i j * C i k j)) =
      ∑ i, ∑ j, a i j * (J * C i) r j := by
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  simp_rw [hC, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  rw [add_sub_cancel_left]
  exact heat_weighted_connection_trace J a H D hH r

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatRoughTraceAlgebra
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction of the twice-differentiated pullback. The Jacobian
derivative cancels exactly against the transformed density drift. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem heat_trace_pullback_algebra (J a H Q : Mat4) (hH : J * a * Jᵀ = H) :
    (∑ i, ∑ j, a i j * (∑ r, ∑ s, J r i * J s j * Q r s)) =
      ∑ r, ∑ s, H r s * Q r s := by
  have he (i j : Fin 4) : (∑ r, ∑ s, J r i * J s j * Q r s) =
      (weightedConnection J (fun r => Matrix.of (fun _ s => Q r s)) i * J) 0 j := by
    simp only [weightedConnection, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp_rw [he]
  exact heat_weighted_connection_trace J a H (fun r => Matrix.of (fun _ s => Q r s)) hH 0

theorem heat_rough_trace_algebra (J a H Q : Mat4)
    (P : Fin 4 → Mat4) (b S B : Fin 4 → ℝ)
    (hH : J * a * Jᵀ = H)
    (hP : ∀ i j r, P j r i = P i r j)
    (hb : ∀ r, (∑ i, J r i * b i) - (∑ i, ∑ j, a i j * P i r j) = B r) :
    -(∑ i, ∑ j, a i j *
      ((∑ r, P j r i * S r) + (∑ r, ∑ s, J r i * J s j * Q r s))) +
      (∑ i, b i * (∑ r, J r i * S r)) =
        -(∑ r, ∑ s, H r s * Q r s) + ∑ r, B r * S r := by
  have hp : (∑ i, ∑ j, a i j * (∑ r, P j r i * S r)) =
      ∑ r, (∑ i, ∑ j, a i j * P j r i) * S r := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  have hq : (∑ i, b i * (∑ r, J r i * S r)) =
      ∑ r, (∑ i, J r i * b i) * S r := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb' (r : Fin 4) : (∑ i, J r i * b i) -
      (∑ i, ∑ j, a i j * P j r i) = B r := by
    have he : (∑ i, ∑ j, a i j * P j r i) = ∑ i, ∑ j, a i j * P i r j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hP i j r]
    rw [he]
    exact hb r
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hp, hq, heat_trace_pullback_algebra J a H Q hH]
  have h : (∑ r, (∑ i, J r i * b i) * S r) -
      (∑ r, (∑ i, ∑ j, a i j * P j r i) * S r) = ∑ r, B r * S r := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [← sub_mul, hb']
  linarith only [h]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelDerivative
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Sobolev regularity in four dimensions is characterized by the
four actual distributional coordinate derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

/-- The actual distributional derivative in one Euclidean coordinate. -/
def scalarCoordinateDerivative (i : Fin 4) (u : 𝓢'(V, ℂ)) : 𝓢'(V, ℂ) :=
  ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} u

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelCommutator
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact localization of the distributional Laplacian, and the loss of
only one Sobolev order in its smooth-cutoff commutator. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

def scalarSchwartzCoordinateDerivative (i : Fin 4) (a : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} a

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelSobolev
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily high scalar Sobolev regularity produces a smooth function.
The representative is constructed by inverse Fourier integration, rather than
assumed as an elliptic regularity input. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal BoundedContinuousFunction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sobolevReciprocal (n : ℕ) (x : E) : ℂ :=
  Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-(n : ℝ)))

theorem scalar_fourier_weight_memL1 (u : 𝓢'(E, ℂ))
    (hu : ∀ n : ℕ, MemSobolev (n : ℝ) 2 u) (k : ℕ) :
    ∃ w : Lp ℂ 1 (volume : Measure E),
      smulLeftCLM ℂ (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ k)) (𝓕 u) = w := by
  let d := Module.finrank ℝ E
  have hdim : (Module.finrank ℝ E : ℝ) < 2 * ((d + 1 : ℕ) : ℝ) := by
    dsimp [d]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)]
  have hreg : MemSobolev ((d + 1 : ℕ) : ℝ) 2
      (besselPotential E ℂ (2 * (k : ℝ)) u) := by
    rw [memSobolev_besselPotential_iff]
    convert hu (2 * k + (d + 1)) using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  obtain ⟨w, hw⟩ := hreg.fourier_memL1 hdim
  refine ⟨w, ?_⟩
  rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply] at hw
  convert hw using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  simp only [mul_div_cancel_left₀ (k : ℝ) (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_natCast]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelCutoffs
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete nested compact cutoffs inside the unit ball. Their radii tend
to one, while each support lies strictly inside the next region of value one. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

def scalarBumpGap (r : ℝ) (k : ℕ) : ℝ := (1 - r) * (1 / 4 : ℝ) ^ (k + 1)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Integer-order Bessel inverses on the actual Euclidean L2 space.
These supply the common smooth approximation for the higher nonlinear bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℂ)

def integerBesselSymbol (n : ℕ) (x : V) : ℂ :=
  ((1 + ‖x‖ ^ 2) ^ (-((n : ℝ) / 2)) : ℝ)

theorem integerBesselSymbol_temperate (n : ℕ) :
    (integerBesselSymbol n).HasTemperateGrowth := by
  unfold integerBesselSymbol
  fun_prop

theorem integerBesselSymbol_bound (n : ℕ) (x : V) :
    ‖integerBesselSymbol n x‖ ≤ 1 := by
  rw [integerBesselSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖])
    (neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) (by norm_num)))

theorem integerBesselSymbol_memLp (n : ℕ) :
    MemLp (integerBesselSymbol n) ∞ (volume : Measure V) :=
  memLp_top_of_bound (integerBesselSymbol_temperate n).1.continuous.aestronglyMeasurable
    1 (.of_forall (integerBesselSymbol_bound n))

def scalarSchwartzIntegerBesselInverse (n : ℕ) (φ : S) : S :=
  SchwartzMap.fourierMultiplierCLM ℂ (integerBesselSymbol n) φ

theorem scalarSchwartzIntegerBesselInverse_distribution (n : ℕ) (φ : S) :
    (scalarSchwartzIntegerBesselInverse n φ : T) = besselPotential V ℂ (-(n : ℝ)) (φ : T) := by
  rw [scalarSchwartzIntegerBesselInverse, besselPotential]
  have hs : integerBesselSymbol n =
      fun x : V => (((1 + ‖x‖ ^ 2) ^ ((-(n : ℝ)) / 2) : ℝ) : ℂ) := by
    funext x
    simp only [integerBesselSymbol, neg_div]
  rw [← hs]
  exact (fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (integerBesselSymbol_temperate n) φ).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Schwartz test operator is exactly the normalized scalar coordinate
operator, including its real and imaginary parts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

theorem scalar_real_map_mul (L : ℂ →L[ℝ] ℝ) (r : ℝ) (z : ℂ) :
    L ((r : ℂ) * z) = r * L z := by
  rw [← Complex.real_smul, L.map_smul]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong L2 control of the finite coordinate jets of the Bessel inverse.
All derivatives are the actual distributional derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter LineDeriv
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℂ)

/-- A finite ordered coordinate derivative on tempered distributions. -/
def scalarCoordinateJet : List (Fin 4) → T →L[ℂ] T
  | [] => ContinuousLinearMap.id ℂ T
  | i :: is => (lineDerivOpCLM ℂ T (EuclideanSpace.basisFun (Fin 4) ℝ i)).comp
      (scalarCoordinateJet is)

@[simp] theorem scalarCoordinateJet_nil (u : T) : scalarCoordinateJet [] u = u := rfl

@[simp] theorem scalarCoordinateJet_cons (i : Fin 4) (is : List (Fin 4)) (u : T) :
    scalarCoordinateJet (i :: is) u = scalarCoordinateDerivative i (scalarCoordinateJet is u) := rfl

theorem scalarCoordinateJet_memSobolev (is : List (Fin 4)) {s : ℝ} {u : T}
    (hu : MemSobolev s 2 u) :
    MemSobolev (s - (is.length : ℝ)) 2 (scalarCoordinateJet is u) := by
  induction is with
  | nil => simpa using hu
  | cons i is ih =>
    have h := ih.lineDerivOp (m := EuclideanSpace.basisFun (Fin 4) ℝ i)
    simpa only [scalarCoordinateJet_cons, scalarCoordinateDerivative,
      List.length_cons, Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using h

def scalarSchwartzCoordinateJet : List (Fin 4) → S →L[ℂ] S
  | [] => ContinuousLinearMap.id ℂ S
  | i :: is => (lineDerivOpCLM ℂ S (EuclideanSpace.basisFun (Fin 4) ℝ i)).comp
      (scalarSchwartzCoordinateJet is)

theorem scalarSchwartzCoordinateJet_distribution (is : List (Fin 4)) (φ : S) :
    (scalarSchwartzCoordinateJet is φ : T) = scalarCoordinateJet is (φ : T) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    calc
      _ = scalarCoordinateDerivative i (scalarSchwartzCoordinateJet is φ : T) :=
        (lineDerivOp_toTemperedDistributionCLM_eq (scalarSchwartzCoordinateJet is φ)
          (EuclideanSpace.basisFun (Fin 4) ℝ i)).symm
      _ = _ := by rw [ih]; rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rescaled metric coefficients satisfy the quantitative
hypotheses of the local elliptic inverse, including the adjoint drift. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff SchwartzMap LineDeriv

noncomputable section

def scalarEllipticEstimateConstant : ℝ :=
  16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20

def scalarEllipticSmallSize : ℝ := (2 * scalarEllipticEstimateConstant)⁻¹

theorem scalarEllipticEstimateConstant_pos : 0 < scalarEllipticEstimateConstant := by
  unfold scalarEllipticEstimateConstant
  positivity

theorem scalarEllipticSmallSize_pos : 0 < scalarEllipticSmallSize := by
  unfold scalarEllipticSmallSize
  exact inv_pos.mpr (mul_pos two_pos scalarEllipticEstimateConstant_pos)

theorem scalarEllipticSmallSize_small :
    (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * scalarEllipticSmallSize < 1 := by
  change scalarEllipticEstimateConstant * (2 * scalarEllipticEstimateConstant)⁻¹ < 1
  have he : scalarEllipticEstimateConstant * (2 * scalarEllipticEstimateConstant)⁻¹ = 1 / 2 := by
    field_simp [ne_of_gt scalarEllipticEstimateConstant_pos]
  rw [he]
  norm_num

theorem scalar_rescaling_budget (κ δ : ℝ) (hδ : 0 ≤ δ) :
    |κ| * (δ / (9 * (|κ| + 1))) ≤ δ / 9 := by
  have hd : 0 < |κ| + 1 := by positivity
  have he : 0 ≤ δ / (9 * (|κ| + 1)) := div_nonneg hδ (by positivity)
  calc
    _ ≤ (|κ| + 1) * (δ / (9 * (|κ| + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) he
    _ = δ / 9 := by field_simp [ne_of_gt hd]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Critical L4 control of the finite Bessel jets retaining one derivative. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter LineDeriv Set
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)

local instance instFactLeENNRealOfNat_solutions_8 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

theorem schwartz_eLpNorm_two (φ : S) :
    eLpNorm φ 2 volume = ENNReal.ofReal ‖φ.toLp 2 volume‖ := by
  rw [ofReal_norm]
  exact (Lp.enorm_toLp (φ.memLp 2 volume)).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single smooth approximation controls all the finite jets used in the
nonlinear bootstrap, in L2, L4 and L-infinity at their required orders. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local instance instFactLeENNRealOfNat_solutions_11 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local six-component heat operator in a radial frame. The additional
first-order Gaussian term vanishes by the radial connection identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

abbrev HeatMat6 := Matrix (Fin 6) (Fin 6) ℝ

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real smooth approximations carrying the same higher-order derivative
limits as their complex Fourier construction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter LineDeriv
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local instance instFactLeENNRealOfNat_solutions_14 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Six-component Euclidean L2 realizations of the local two-form and
its covariant derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

def twoFormComponentIndex : Fin 6 → Fin 2 → Fin 4 :=
  ![![0,1], ![0,2], ![0,3], ![1,2], ![1,3], ![2,3]]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Absolute values in actual Lp and the convergence of positive smooth
regularizations of an approximating scalar sequence. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}

def scalarLpAbs (f : Lp ℝ p μ) : Lp ℝ p μ :=
  lipschitzWith_one_norm.compLp norm_zero f

theorem scalarLpAbs_coe (f : Lp ℝ p μ) :
    scalarLpAbs f =ᵐ[μ] fun x => |f x| :=
  lipschitzWith_one_norm.coeFn_compLp norm_zero f

theorem scalarLpAbs_norm [Fact (1 ≤ p)] (f : Lp ℝ p μ) : ‖scalarLpAbs f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (scalarLpAbs_coe f)]
  exact congrArg ENNReal.toReal (eLpNorm_norm f)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The lifted tensor's pairing is the intrinsic normal-frame pairing
at the base point. No choice of reference-frame regularity is needed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_euclideanTensor_inner (T U : CovariantCoordinates 2) :
    inner ℝ (WithLp.toLp 2 T : TwoTensorEuclidean) (WithLp.toLp 2 U) =
      frameTensorPairing T U := by
  change (∑ a, inner ℝ (T a) (U a)) = _
  simp only [RCLike.inner_apply, conj_trivial, frameTensorPairing, mul_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform control of compact chart tensors in the frame-bundle norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem twoTensorEuclidean_norm_le_sum (T : CovariantCoordinates 2) :
    ‖(WithLp.toLp 2 T : TwoTensorEuclidean)‖ ≤ ∑ a, |T a| := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun a => |T a|) (fun _ _ => abs_nonneg _)
  simp only [sq_abs] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mp
  simpa only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! The metric product rule for the six-component skew connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeat_skew_pairing (A : HeatMat6) (hA : Aᵀ = -A)
    (p q : Fin 6 → ℝ) :
    (∑ k, (∑ l, A k l * p l) * q k) =
      -(∑ k, p k * ∑ l, A k l * q l) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hs (k l : Fin 6) : A l k = -A k l := congrFun (congrFun hA k) l
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hs k l]
  ring

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Symmetry of the two finite contractions in the connection energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem fourHeat_potential_pairing_symm (V : HeatMat6)
    (hV : ∀ k l, V k l = V l k) (u v : Fin 6 → ℝ) :
    (∑ k, u k * ∑ l, V k l * v l) = ∑ k, v k * ∑ l, V k l * u l := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hV l k]
  ring

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The determinant and first zero of the complex-space-form Jacobi matrix. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section

def complexJacobiRadius : ℝ := Real.pi / Real.sqrt 2

end
end PositiveEinsteinFour.Jacobi
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The Hausdorff topology determined by the actual projective overlaps. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

def complexProjectiveEvaluation (p : ComplexProjective2) : ComplexProjective2 → ℝ :=
  fun q => cp2Overlap q p

@[instance_reducible] def complexProjectiveTopology : TopologicalSpace ComplexProjective2 :=
  TopologicalSpace.induced complexProjectiveEvaluation inferInstance

attribute [local instance] complexProjectiveTopology

theorem complexProjectiveEvaluation_injective : Function.Injective complexProjectiveEvaluation := by
  intro p q hpq
  have h := congrFun hpq p
  change cp2Overlap p p = cp2Overlap p q at h
  rw [cp2Overlap_self] at h
  exact (cp2Overlap_eq_one_iff p q).mp h.symm

theorem complexProjectiveEvaluation_isEmbedding : Topology.IsEmbedding complexProjectiveEvaluation :=
  complexProjectiveEvaluation_injective.isEmbedding_induced

theorem complexProjective_t2Space : T2Space ComplexProjective2 :=
  complexProjectiveEvaluation_isEmbedding.t2Space

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


