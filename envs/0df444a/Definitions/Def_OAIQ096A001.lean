-- Prove2me | Definitions.Def_OAIQ096A001
-- name    : OAIQ096A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:28:07.570436+00:00
-- url     : https://prove2.me/theorems/7b27d333-691d-415e-81ab-56eb9ff24165
-- title:
--   Definitions bundle OAIQ096A001 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 268 declarations of OpenAI's Lean: 104 definitions, 4 inductive types or structures, 9 instances and 151 theorems. The definitions and types are `OAI.CubicFirstMoment.CubicThetaAxis`, `OAI.CubicFirstMoment.CubicThetaCoordinateAnalytic`, `OAI.CubicFirstMoment.CubicThetaCoordinateJetBound`, `OAI.CubicFirstMoment.CubicThetaForcingBand`, `OAI.CubicFirstMoment.CubicThetaGradient`, `OAI.CubicFirstMoment.CubicThetaIntegerPoint`, `OAI.CubicFirstMoment.CubicThetaLocalEnergyAmbient`, `OAI.CubicFirstMoment.CubicThetaLocalJet`, `OAI.CubicFirstMoment.CubicThetaPoint`, `OAI.CubicFirstMoment.CubicThetaTangent`, `OAI.CubicFirstMoment.CubicThetaTangentIndex`, `OAI.CubicFirstMoment.CubicThetaTorusL2`, `OAI.CubicFirstMoment.FiniteVerticalOrder`, `OAI.CubicFirstMoment.FixedScaleMomentBounds`, `OAI.CubicFirstMoment.GammaInverseFiniteOrder`, `OAI.CubicFirstMoment.GammaQuotientStripBound`, `OAI.CubicFirstMoment.HasPowerExponent`, `OAI.CubicFirstMoment.LocalSobolev.H1Target`, `OAI.CubicFirstMoment.LocalSobolev.TangentComplexL2`, `OAI.CubicFirstMoment.LocalSobolev.energyRellich_borel`, `OAI.CubicFirstMoment.LocalSobolev.imagH1`, `OAI.CubicFirstMoment.LocalSobolev.imagTest`, `OAI.CubicFirstMoment.LocalSobolev.localRellich_tangent_borel`, `OAI.CubicFirstMoment.LocalSobolev.realH1`, `OAI.CubicFirstMoment.LocalSobolev.realTest`, `OAI.CubicFirstMoment.LocalSobolev.rellichValue_borel`, `OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume`, `OAI.CubicFirstMoment.LocalSobolev.tangentFunctionL2`, `OAI.CubicFirstMoment.LocalSobolev.tangent_borel`, `OAI.CubicFirstMoment.LogarithmicWeightFamily`, `OAI.CubicFirstMoment.UniformLogWeights`, `OAI.CubicFirstMoment.complexAngular`, `OAI.CubicFirstMoment.cubicThetaAxisFunction`, `OAI.CubicFirstMoment.cubicThetaCartesianPoint`, `OAI.CubicFirstMoment.cubicThetaConstant`, `OAI.CubicFirstMoment.cubicThetaCoordinateCenter`, `OAI.CubicFirstMoment.cubicThetaCoordinateLine`, `OAI.CubicFirstMoment.cubicThetaFirstJetConstant`, `OAI.CubicFirstMoment.cubicThetaFunctionEnergy`, `OAI.CubicFirstMoment.cubicThetaHeightConstant` and 68 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_H1`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_ArzelaAscoli`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2`, `CubicGram_LatticePoisson`, `CubicGram_PeriodicPoisson`, `CubicMoment_Estimates_FixedAngularHecke`, `CubicMoment_Estimates_FixedScalePowers`, `CubicMoment_Estimates_HeckeCompletedOrder`, `CubicMoment_Estimates_HeckeDualContour`, `CubicMoment_Estimates_LogarithmicPhase`, `CubicMoment_Estimates_LogarithmicWeightFamily`, `CubicMoment_Estimates_MellinWeightFamily`, `CubicMoment_Estimates_MomentExponents`, `CubicMoment_Estimates_PolynomialStrip`, `CubicMoment_Estimates_TypeILogCoefficients`, `CubicMoment_Theta_CubicThetaBorelSection`, `CubicMoment_Theta_CubicThetaCircleActual`, `CubicMoment_Theta_CubicThetaCompactEnergyBound`, `CubicMoment_Theta_CubicThetaCompactRowBounds`, `CubicMoment_Theta_CubicThetaCoordinateAxis`, `CubicMoment_Theta_CubicThetaCoordinateJets`, `CubicMoment_Theta_CubicThetaCutoffEnergy`, `CubicMoment_Theta_CubicThetaEisensteinBounds`, `CubicMoment_Theta_CubicThetaEllipticTrace`, `CubicMoment_Theta_CubicThetaEnergyCoordinates`, `CubicMoment_Theta_CubicThetaForcingProfile`, `CubicMoment_Theta_CubicThetaFunction`, `CubicMoment_Theta_CubicThetaGlobalGradient`, `CubicMoment_Theta_CubicThetaGridAnalytic`, `CubicMoment_Theta_CubicThetaGridEquation`, `CubicMoment_Theta_CubicThetaHyperbolicMeasure`, `CubicMoment_Theta_CubicThetaIntegerBox`, `CubicMoment_Theta_CubicThetaInversionGeometry`, `CubicMoment_Theta_CubicThetaLocalEnergyGraph`, `CubicMoment_Theta_CubicThetaLocalEnergyJet`, `CubicMoment_Theta_CubicThetaLocalEnergyRellich`, `CubicMoment_Theta_CubicThetaLocalRellich`, `CubicMoment_Theta_CubicThetaLocalRellichValue`, `CubicMoment_Theta_CubicThetaLocalizationSobolevBound`, `CubicMoment_Theta_CubicThetaMobiusAction`, `CubicMoment_Theta_CubicThetaMobiusContinuity`, `CubicMoment_Theta_CubicThetaMobiusGenerators`, `CubicMoment_Theta_CubicThetaMobiusGeometry`, `CubicMoment_Theta_CubicThetaMobiusMatrix`, `CubicMoment_Theta_CubicThetaMobiusSmooth`, `CubicMoment_Theta_CubicThetaPointFrame`, `CubicMoment_Theta_CubicThetaProperAction`, `CubicMoment_Theta_CubicThetaQuotient`, `CubicMoment_Theta_CubicThetaQuotientCharts`, `CubicMoment_Theta_CubicThetaRadialEnergyNorm`, `CubicMoment_Theta_CubicThetaSobolevEnergy`, `CubicMoment_Theta_CubicThetaSupportedTangent`, `CubicMoment_Theta_CubicThetaTangentEnergy`, `CubicMoment_Theta_CubicThetaTangentIsometry`, `CubicMoment_Theta_CubicThetaTangentSobolev`, `CubicMoment_Theta_CubicThetaTangentVolume`, `CubicMoment_Theta_CubicThetaTorusModes`, `CubicMoment_Transform_MetaplecticVoronoi`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A004`, `OAIQ096A005` and `OAIQ096A006`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
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
    exact (HasCompactSupport.smul_left (f := fun _ : E => c) hf.2)

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

/-- `H¹` is complete (a Hilbert space once the ambient `L²` spaces are). -/
instance instCompleteSpace_h1 : CompleteSpace (↥(h1 (μ := μ) (E := E))) := by
  classical
  exact (isClosed_h1 (μ := μ) (E := E)).isComplete.completeSpace_coe

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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation
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
    convert hadd.comp hneg using 1
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_ArzelaAscoli
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
            rw [dist_sub_right]
            exact hxy
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
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
    exact (continuous_const.mul hf_cont)
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate
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
    have hInner' : ContDiff ℝ 1 (fun t : ℝ => x + t • a) := hInner.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2
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

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
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
-- module Solutions.OAIQ096_CM.CubicGram_LatticePoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein real coordinates, measure factors and translated lattice Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

namespace CubicFirstMoment

def realCoordMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -1/2; 0, Real.sqrt 3 / 2]

def tracePair (z w : ℂ) : ℝ := 2 * (z * w).re

def dualRealCoords (y : Fin 2 → ℝ) : ℂ :=
  ((y 0 / 2 : ℝ) : ℂ) - (((y 0 + 2 * y 1) / (2 * Real.sqrt 3) : ℝ) : ℂ) * Complex.I

lemma tracePair_add_left (z x w : ℂ) :
    tracePair (z + x) w = tracePair z w + tracePair x w := by
  simp only [tracePair, add_mul, Complex.add_re]
  ring

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PeriodicPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic lattice Poisson summation and exact trace frequencies. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma fourierChar_int (n : ℤ) : (Real.fourierChar (n : ℝ) : ℂ) = 1 := by
  rw [Real.fourierChar_apply]
  push_cast
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedAngularHecke
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative fixed-angular Hecke prime estimates

The published input is the degree-two, nonexceptional specialization of
Kaneko--Thorner, *Highly uniform prime number theorems*, Ann. Inst. Fourier
75 (2025), Theorem 1.2, pp. 1904--1905 (restating Iwaniec--Kowalski,
Theorem 5.13), with the zero-free region and completion from Rajan (1998),
Proposition 1 and Section 1. The exponential conductor-dependent error
is retained. Arbitrary logarithmic savings are derived below; they are
not included among the published-input hypotheses.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators

namespace CubicFirstMoment

/-- The conductor-dependent error in the published prime number theorem. -/
def heckeExponentialError (c x Q : ℝ) : ℝ :=
  x * (Real.log (x * Q)) ^ 4 *
    Real.exp (-c * Real.log x / (Real.log Q + Real.sqrt (Real.log x)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MomentExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic exponents of actual positive sequences and the limits
of the proved moment inequalities. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace CubicFirstMoment

def HasPowerExponent (Y f : ℕ → ℝ) (a : ℝ) : Prop :=
  Tendsto (fun j => Real.log (f j)/Real.log (Y j)) atTop (𝓝 a)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDualContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving finite dual polynomials back to the symmetry line. The only
new conditional analytic input is the bounded-strip polynomial estimate
for the classical Gamma quotient, a specialization of NIST DLMF 5.11.9
(uniformly for bounded real parts). The half-integer-line estimate needed
for the discarded tail was proved directly in GammaLeftLine. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

/-- The elementary quotient in the trivial infinity-type equation. -/
def gammaFEQuotient (s : ℂ) : ℂ := Complex.Gamma (1-s)/Complex.Gamma s

/-- Small bounded-strip consequence of the uniform vertical Stirling
formula, NIST DLMF (5.11.9), https://dlmf.nist.gov/5.11.E9.
This concerns only the classical Gamma function, not an arithmetic sum. -/
def GammaQuotientStripBound (a : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ ∈ Icc a (1/2:ℝ), ∀ u : ℝ,
    ‖gammaFEQuotient (σ+(u:ℂ)*Complex.I)‖ ≤ C*(1+|u|)^N

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial strip growth from finite order and polynomial boundary
bounds. The finite-order hypothesis is much weaker than the conclusion;
the proof uses the Phragmén–Lindelöf theorem in mathlib. -/

noncomputable section
open Set Filter Asymptotics
namespace CubicFirstMoment

/-- A finite-order bound restricted to a closed vertical strip. -/
def FiniteVerticalOrder (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
    ‖f z‖ ≤ Real.exp (C*(1+|z.im|)^k)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeCompletedOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Classical order-one completion as the weak analytic input.
Thorner--Zaman, ANT 13 (2019), §2C, p.1049, Eq. (2-15), states
that the completed primitive nonprincipal Hecke function is entire of
order one. The coarse quadratic exponential majorant below is sufficient.
The reciprocal Gamma strip bound is a weak consequence of the uniform
vertical Stirling formula, DLMF 5.11.9, and its entire reciprocal (5.2.2).
These inputs concern individual analytic functions, not arithmetic means. -/

noncomputable section
open Set
namespace CubicFirstMoment

/-- Weak reciprocal-Gamma growth, on one bounded strip only. -/
def GammaInverseFiniteOrder (a b : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, s.re ∈ Icc a b →
    ‖(Complex.Gamma s)⁻¹‖ ≤ Real.exp (B*(1+|s.im|)^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedScalePowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed dilations preserve every strict exponent margin used by the
finite output partition. -/
noncomputable section
open Filter
namespace CubicFirstMoment

structure FixedScaleMomentBounds (Y σ κ c ε T : ℝ) : Prop where
  threshold : T ≤ σ*Y
  log_bound : 1 ≤ Real.log (σ*Y)
  first_window : (σ*Y)^(1-κ) ≤ Y^(1-κ/2) ∧ Y^(1+κ/2) ≤ (σ*Y)^(1+κ)
  balanced_window : (σ*Y)^(1/3-κ) ≤ Y^(1/3-κ/2) ∧ Y^(1/3+κ/2) ≤ (σ*Y)^(1/3+κ)
  small_bound : Y^(κ/2) ≤ (σ*Y)^κ
  height_bound : Y^(9/25:ℝ) ≤ (σ*Y)^(721/2000:ℝ)
  upper_bound : Y ≤ (σ*Y)^2
  lower_bound : (2*(σ*Y))^(c/2) ≤ (2*Y)^c
  saving_bound : (σ*Y)^(7/3-ε) ≤ Y^(7/3-ε/2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeightFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Mellin estimates for the smooth weight families occurring in
Type I. The hypotheses state common support and derivative bounds in
logarithmic coordinates. No transform or moment estimate is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology SchwartzMap ContDiff FourierTransform BigOperators
namespace CubicFirstMoment

structure UniformLogWeights {ι : Type*} (W : ι → ℝ → ℂ) where
  compact : ∀ i, HasCompactSupport (W i)
  positive : ∀ i, tsupport (W i) ⊆ Ioi 0
  smooth : ∀ i, ContDiff ℝ ∞ (W i)
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  support_bound : ∀ i u, u ∈ tsupport (fun v : ℝ => W i (Real.exp (-v))) → |u| ≤ radius
  derivative_bound : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ i u,
    ‖iteratedFDeriv ℝ n (fun v : ℝ => W i (Real.exp (-v))) u‖ ≤ B

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogarithmicWeightFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial logarithmic derivative cost can be normalized by any
fixed positive power of the outer length. This gives a uniform smooth
family without discarding the original, varying test functions. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

structure LogarithmicWeightFamily {γ : Type*} (Y : γ → ℝ) (W : γ → ℝ → ℂ) where
  length_one : ∀ i, 1 ≤ Y i
  compact : ∀ i, HasCompactSupport (W i)
  positive : ∀ i, tsupport (W i) ⊆ Ioi 0
  smooth : ∀ i, ContDiff ℝ ∞ (W i)
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  support_bound : ∀ i u, u ∈ tsupport (fun v => W i (Real.exp (-v))) → |u| ≤ radius
  derivative_bound : ∀ n : ℕ, ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ i u,
    ‖iteratedFDeriv ℝ n (fun v => W i (Real.exp (-v))) u‖ ≤ C*(1+Real.log (Y i))^A

def normalizedLogWeight {γ : Type*} (Y : γ → ℝ) (W : γ → ℝ → ℂ) (s : ℝ)
    (i : γ) (x : ℝ) : ℂ := (Y i^(-s):ℝ) • W i x

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticVoronoi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal level/angular Voronoi input of Dunn--Radziwill,
arXiv:2109.07463v3, Proposition 5.3, equations (5.79)--(5.82), pp.33--34.
The raw formula is kept separate from its proved Gauss/phase normalization.
The index `n` below denotes the actual frequency `n / lambda`; zero is excluded.
No estimate for a completed sum is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def complexAngular (ℓ : ℤ) (z : ℂ) : ℂ := (z/(‖z‖:ℂ))^ℓ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogarithmicPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmically bounded height twists preserve the smooth weight
family used by the low-height Type-I theorem. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def linearHeightPhase (t x : ℝ) : ℂ := Complex.exp ((t*x:ℝ)*Complex.I)

abbrev logarithmicPhaseIndex {γ : Type*} (Y : γ → ℝ) (d : ℕ) :=
  {p : γ × ℝ // |p.2| ≤ (1+Real.log (Y p.1))^d}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeILogCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed logarithmic coefficient factors can be retained in the actual
weight family. This is the form used by short logarithmic convolutions. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def logPowerWeight {γ : Type*} (Y : γ → ℝ) (W : γ → ℝ → ℂ)
    (d : ℕ) (i : γ) (x : ℝ) : ℂ := ((1+Real.log (Y i))^d:ℝ) • W i x

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete theta and auxiliary Fourier series from DR v3 (5.6),
(5.7), (5.13) and (5.14), with their proved analytic properties. Modular
transformation identities remain to be established. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaConstant : ℝ := 3^(5/2:ℝ)/2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric inversion in the cubic theta transformation, restricted
only by positive height and nonzero level. No automorphy law is assumed. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRadius (p : ℂ × ℝ) : ℝ := Complex.normSq p.1+p.2^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMobiusGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal hyperbolic three-space action used in DR v3, Section 5.1.
The determinant calculation is kept explicit, before using the action
to transport the cubic theta series. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaMobiusDenominator (g : SL(2,ℂ)) (p : ℂ × ℝ) : ℝ :=
  Complex.normSq (g 1 0*p.1+g 1 1)+Complex.normSq (g 1 0)*p.2^2

def cubicThetaMobiusNumerator (g : SL(2,ℂ)) (p : ℂ × ℝ) : ℂ :=
  (g 0 0*p.1+g 0 1)*star (g 1 0*p.1+g 1 1)+g 0 0*star (g 1 0)*(p.2^2:ℝ)

def cubicThetaMobius (g : SL(2,ℂ)) (p : ℂ × ℝ) : ℂ × ℝ :=
  (cubicThetaMobiusNumerator g p/(cubicThetaMobiusDenominator g p:ℂ),
    p.2/cubicThetaMobiusDenominator g p)

lemma cubicThetaMobius_det (g : SL(2,ℂ)) :
    g 0 0*g 1 1-g 0 1*g 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using g.property

lemma cubicThetaMobius_denominator_pos (g : SL(2,ℂ)) {p : ℂ × ℝ}
    (hp : 0 < p.2) : 0 < cubicThetaMobiusDenominator g p := by
  by_cases hc : g 1 0 = 0
  · have hd : g 1 1 ≠ 0 := by
      intro hd
      have h := cubicThetaMobius_det g
      rw [hc,hd,mul_zero,mul_zero,sub_zero] at h
      exact zero_ne_one h
    simpa only [cubicThetaMobiusDenominator,hc,zero_mul,zero_add,
      Complex.normSq_zero,mul_zero,add_zero] using Complex.normSq_pos.mpr hd
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (mul_pos (Complex.normSq_pos.mpr hc) (sq_pos_of_pos hp))

lemma cubicThetaMobius_height_pos (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0 < p.2) :
    0 < (cubicThetaMobius g p).2 :=
  div_pos hp (cubicThetaMobius_denominator_pos g hp)

lemma normSq_lagrange (A B a b : ℂ) (t : ℝ) :
    (Complex.normSq A+Complex.normSq a*t)*(Complex.normSq B+Complex.normSq b*t)-
      Complex.normSq (A*star B+a*star b*(t:ℂ)) =
        Complex.normSq (A*b-a*B)*t := by
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

lemma cubicThetaMobius_radius (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaRadius (cubicThetaMobius g p) =
      (Complex.normSq (g 0 0*p.1+g 0 1)+Complex.normSq (g 0 0)*p.2^2)/
        cubicThetaMobiusDenominator g p := by
  have hD := ne_of_gt (cubicThetaMobius_denominator_pos g hp)
  have h := normSq_lagrange (g 0 0*p.1+g 0 1) (g 1 0*p.1+g 1 1)
    (g 0 0) (g 1 0) (p.2^2)
  have he : (g 0 0*p.1+g 0 1)*g 1 0-g 0 0*(g 1 0*p.1+g 1 1) = -1 := by
    linear_combination -cubicThetaMobius_det g
  rw [he,Complex.normSq_neg,Complex.normSq_one,one_mul] at h
  change cubicThetaRadius (cubicThetaMobius g p) = _
  unfold cubicThetaRadius cubicThetaMobius
  simp only [Complex.normSq_div,Complex.normSq_ofReal,div_pow]
  rw [← pow_two (cubicThetaMobiusDenominator g p)]
  change (Complex.normSq (g 0 0*p.1+g 0 1)+Complex.normSq (g 0 0)*p.2^2)*
    cubicThetaMobiusDenominator g p-Complex.normSq (cubicThetaMobiusNumerator g p) = p.2^2 at h
  field_simp
  linear_combination -h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMobiusMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hermitian coordinates for the actual hyperbolic action. They give
the composition law without any analytic or automorphy assumption. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaHermitian (p : ℂ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(cubicThetaRadius p:ℂ),p.1;star p.1,1]

def cubicThetaMobiusQuadratic (g : SL(2,ℂ)) (p : ℂ × ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (g : Matrix (Fin 2) (Fin 2) ℂ)*cubicThetaHermitian p*
    (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ

lemma cubicThetaMobiusQuadratic_entries (g : SL(2,ℂ)) (p : ℂ × ℝ) :
    cubicThetaMobiusQuadratic g p =
      !![((Complex.normSq (g 0 0*p.1+g 0 1)+Complex.normSq (g 0 0)*p.2^2:ℝ):ℂ),
          cubicThetaMobiusNumerator g p;
          star (cubicThetaMobiusNumerator g p),(cubicThetaMobiusDenominator g p:ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [cubicThetaMobiusQuadratic,cubicThetaHermitian,cubicThetaRadius,
      cubicThetaMobiusNumerator,cubicThetaMobiusDenominator,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.conjTranspose_apply,Matrix.of_apply,
      Complex.ofReal_add,Complex.ofReal_mul,Complex.normSq_eq_conj_mul_self,
      map_add,map_mul,Complex.star_def,Complex.conj_ofReal,Complex.conj_conj] <;> dsimp <;> ring

lemma cubicThetaHermitian_mobius (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaHermitian (cubicThetaMobius g p) =
      (cubicThetaMobiusDenominator g p:ℂ)⁻¹ • cubicThetaMobiusQuadratic g p := by
  have hD : (cubicThetaMobiusDenominator g p:ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (cubicThetaMobius_denominator_pos g hp)
  rw [cubicThetaMobiusQuadratic_entries]
  ext i j
  fin_cases i <;> fin_cases j
  · change (cubicThetaRadius (cubicThetaMobius g p):ℂ) =
      (cubicThetaMobiusDenominator g p:ℂ)⁻¹ *
        ((Complex.normSq (g 0 0*p.1+g 0 1)+Complex.normSq (g 0 0)*p.2^2:ℝ):ℂ)
    rw [cubicThetaMobius_radius g hp,Complex.ofReal_div]
    ring
  · change cubicThetaMobiusNumerator g p/(cubicThetaMobiusDenominator g p:ℂ) =
      (cubicThetaMobiusDenominator g p:ℂ)⁻¹*cubicThetaMobiusNumerator g p
    ring
  · change star (cubicThetaMobiusNumerator g p/(cubicThetaMobiusDenominator g p:ℂ)) =
      (cubicThetaMobiusDenominator g p:ℂ)⁻¹*star (cubicThetaMobiusNumerator g p)
    simp only [map_div₀,Complex.star_def,Complex.conj_ofReal]
    ring
  · change (1:ℂ) = (cubicThetaMobiusDenominator g p:ℂ)⁻¹*(cubicThetaMobiusDenominator g p:ℂ)
    exact (inv_mul_cancel₀ hD).symm

lemma cubicThetaMobiusQuadratic_comp (g h : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaMobiusQuadratic h (cubicThetaMobius g p) =
      (cubicThetaMobiusDenominator g p:ℂ)⁻¹ • cubicThetaMobiusQuadratic (h*g) p := by
  rw [cubicThetaMobiusQuadratic,cubicThetaHermitian_mobius g hp]
  simp only [Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  simp only [cubicThetaMobiusQuadratic,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.conjTranspose_mul,Matrix.mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMobiusAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composition and positive-height action for the hyperbolic matrices
used in the cubic theta transformation. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaMobiusDenominator_comp (g h : SL(2,ℂ))
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaMobiusDenominator h (cubicThetaMobius g p) =
      cubicThetaMobiusDenominator (h*g) p/cubicThetaMobiusDenominator g p := by
  have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1)
    (cubicThetaMobiusQuadratic_comp g h hp)
  simp only [cubicThetaMobiusQuadratic_entries,Matrix.of_apply,Matrix.cons_val_one,Matrix.cons_val_zero,
    Matrix.smul_apply,smul_eq_mul] at hm
  have he : (cubicThetaMobiusDenominator h (cubicThetaMobius g p):ℂ) =
      (cubicThetaMobiusDenominator (h*g) p:ℂ)/(cubicThetaMobiusDenominator g p:ℂ) := by
    rw [hm]
    ring
  exact_mod_cast he

lemma cubicThetaHermitian_comp (g h : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaHermitian (cubicThetaMobius h (cubicThetaMobius g p)) =
      cubicThetaHermitian (cubicThetaMobius (h*g) p) := by
  have hD : (cubicThetaMobiusDenominator g p:ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (cubicThetaMobius_denominator_pos g hp)
  have hD' : (cubicThetaMobiusDenominator (h*g) p:ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (cubicThetaMobius_denominator_pos (h*g) hp)
  rw [cubicThetaHermitian_mobius h (cubicThetaMobius_height_pos g hp),
    cubicThetaMobiusQuadratic_comp g h hp,cubicThetaHermitian_mobius (h*g) hp,smul_smul,
    cubicThetaMobiusDenominator_comp g h hp,Complex.ofReal_div]
  congr 1
  field_simp

theorem cubicThetaMobius_comp (g h : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaMobius h (cubicThetaMobius g p) = cubicThetaMobius (h*g) p := by
  apply Prod.ext
  · have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1)
      (cubicThetaHermitian_comp g h hp)
    simpa only [cubicThetaHermitian,Matrix.cons_val_zero,Matrix.of_apply,Matrix.cons_val_one] using hm
  · change (p.2/cubicThetaMobiusDenominator g p)/
      cubicThetaMobiusDenominator h (cubicThetaMobius g p) =
        p.2/cubicThetaMobiusDenominator (h*g) p
    rw [cubicThetaMobiusDenominator_comp g h hp]
    have hD := ne_of_gt (cubicThetaMobius_denominator_pos g hp)
    have hD' := ne_of_gt (cubicThetaMobius_denominator_pos (h*g) hp)
    field_simp

@[simp] lemma cubicThetaMobius_one (p : ℂ × ℝ) : cubicThetaMobius 1 p = p := by
  apply Prod.ext <;>
    simp [cubicThetaMobius,cubicThetaMobiusNumerator,cubicThetaMobiusDenominator]

/-- Hyperbolic three-space in the coordinates of the manuscript. -/
def CubicThetaPoint := {p : ℂ × ℝ // 0 < p.2}

instance instMulActionSpecialLinearGroupFinOfNatNatComplexCubicThetaPoint : MulAction SL(2,ℂ) CubicThetaPoint where
  smul g p := ⟨cubicThetaMobius g p.val,cubicThetaMobius_height_pos g p.property⟩
  one_smul p := Subtype.ext (cubicThetaMobius_one p.val)
  mul_smul g h p := Subtype.ext (cubicThetaMobius_comp h g p.property).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMobiusContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the actual hyperbolic matrix action, used to transport
compact core charts. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaMobiusDenominator_continuous (g : SL(2,ℂ)) :
    Continuous (cubicThetaMobiusDenominator g) := by
  unfold cubicThetaMobiusDenominator
  fun_prop

lemma cubicThetaMobiusNumerator_continuous (g : SL(2,ℂ)) :
    Continuous (cubicThetaMobiusNumerator g) := by
  unfold cubicThetaMobiusNumerator
  fun_prop

lemma cubicThetaMobius_continuousAt (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    ContinuousAt (cubicThetaMobius g) p := by
  have hD := (cubicThetaMobiusDenominator_continuous g).continuousAt (x:=p)
  have hN := (cubicThetaMobiusNumerator_continuous g).continuousAt (x:=p)
  have hd := (cubicThetaMobius_denominator_pos g hp).ne'
  unfold cubicThetaMobius
  exact (hN.div (Complex.continuous_ofReal.continuousAt.comp hD)
    (Complex.ofReal_ne_zero.mpr hd)).prodMk (continuous_snd.continuousAt.div hD hd)

lemma cubicThetaMobius_continuousOn (g : SL(2,ℂ)) {S : Set (ℂ × ℝ)}
    (hS : ∀ p∈S, 0<p.2) : ContinuousOn (cubicThetaMobius g) S :=
  fun p hp => (cubicThetaMobius_continuousAt g (hS p hp)).continuousWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit determinant-one frame carrying (0,1) to any positive-height
point. It transports fixed-point calculations to the unit Hermitian form. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPointFrame (p : CubicThetaPoint) : SL(2,ℂ) :=
  ⟨!![(Real.sqrt p.val.2:ℂ),p.val.1/(Real.sqrt p.val.2:ℂ);0,1/(Real.sqrt p.val.2:ℂ)],by
    rw [Matrix.det_fin_two_of]
    have hs : (Real.sqrt p.val.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr p.property).ne'
    field_simp
    ring⟩

lemma cubicThetaPointFrame_denominator (p : CubicThetaPoint) :
    cubicThetaMobiusDenominator (cubicThetaPointFrame p) (0,1)=1/p.val.2 := by
  simp only [cubicThetaMobiusDenominator,cubicThetaPointFrame,Matrix.of_apply,
    Matrix.cons_val_one,Matrix.cons_val_zero,zero_mul,zero_add,Complex.normSq_div,
    Complex.normSq_one,Complex.normSq_ofReal,one_pow,Complex.normSq_zero,mul_one,add_zero]
  rw [Real.mul_self_sqrt p.property.le]

lemma cubicThetaPointFrame_numerator (p : CubicThetaPoint) :
    cubicThetaMobiusNumerator (cubicThetaPointFrame p) (0,1)=p.val.1/(p.val.2:ℂ) := by
  have hs : (Real.sqrt p.val.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr p.property).ne'
  have hv : (Real.sqrt p.val.2:ℂ)^2=(p.val.2:ℂ) := by exact_mod_cast Real.sq_sqrt p.property.le
  simp only [cubicThetaMobiusNumerator,cubicThetaPointFrame,Matrix.of_apply,
    Matrix.cons_val_one,Matrix.cons_val_zero,zero_mul,zero_add,star_zero,mul_zero,add_zero,
    one_pow,map_div₀,Complex.star_def,Complex.conj_ofReal,map_one]
  rw [← hv]
  field_simp

lemma cubicThetaPointFrame_base (p : CubicThetaPoint) :
    cubicThetaMobius (cubicThetaPointFrame p) (0,1)=p.val := by
  apply Prod.ext
  · change cubicThetaMobiusNumerator (cubicThetaPointFrame p) (0,1)/
        (cubicThetaMobiusDenominator (cubicThetaPointFrame p) (0,1):ℂ)=p.val.1
    rw [cubicThetaPointFrame_numerator,cubicThetaPointFrame_denominator,Complex.ofReal_div,Complex.ofReal_one]
    field_simp [Complex.ofReal_ne_zero.mpr p.property.ne']
  · change 1/cubicThetaMobiusDenominator (cubicThetaPointFrame p) (0,1)=p.val.2
    rw [cubicThetaPointFrame_denominator]
    field_simp [p.property.ne']

lemma cubicThetaPointFrame_inverse (p : CubicThetaPoint) :
    cubicThetaMobius (cubicThetaPointFrame p)⁻¹ p.val=(0,1) := by
  rw [← cubicThetaPointFrame_base p,cubicThetaMobius_comp _ _ (by norm_num)]
  simp

lemma cubicThetaPointFrame_conjugate_fixed (p : CubicThetaPoint) (g : SL(2,ℂ))
    (hg : cubicThetaMobius g p.val=p.val) :
    cubicThetaMobius ((cubicThetaPointFrame p)⁻¹*g*cubicThetaPointFrame p) (0,1)=(0,1) := by
  rw [← cubicThetaMobius_comp _ _ (by norm_num),cubicThetaPointFrame_base,
    ← cubicThetaMobius_comp g (cubicThetaPointFrame p)⁻¹ p.property,hg,cubicThetaPointFrame_inverse]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEllipticTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed points give a trace bound by transporting to the base point.
These are explicit matrix calculations for the actual hyperbolic action. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaBaseFixed_row_norms (g : SL(2,ℂ))
    (hg : cubicThetaMobius g (0,1)=(0,1)) :
    Complex.normSq (g 0 0)+Complex.normSq (g 0 1)=1 ∧
    Complex.normSq (g 1 0)+Complex.normSq (g 1 1)=1 := by
  have hD : cubicThetaMobiusDenominator g (0,1)=1 := by
    have h := congrArg Prod.snd hg
    change 1/cubicThetaMobiusDenominator g (0,1)=1 at h
    have he := (div_eq_iff (cubicThetaMobius_denominator_pos g (by norm_num)).ne').mp h
    linarith
  have hb : Complex.normSq (g 1 0)+Complex.normSq (g 1 1)=1 := by
    simpa [cubicThetaMobiusDenominator,add_comm] using hD
  have ht := cubicThetaMobius_radius g (p:=(0,1)) (by norm_num)
  rw [hg,hD] at ht
  have ha : Complex.normSq (g 0 0)+Complex.normSq (g 0 1)=1 := by
    simpa [cubicThetaRadius,add_comm] using ht.symm
  exact ⟨ha,hb⟩

lemma cubicThetaBaseFixed_trace_norm (g : SL(2,ℂ))
    (hg : cubicThetaMobius g (0,1)=(0,1)) : ‖g 0 0+g 1 1‖ ≤ 2 := by
  obtain ⟨ha,hd⟩ := cubicThetaBaseFixed_row_norms g hg
  simp only [Complex.normSq_eq_norm_sq] at ha hd
  have ha' : ‖g 0 0‖ ≤ 1 := by nlinarith [sq_nonneg ‖g 0 1‖]
  have hd' : ‖g 1 1‖ ≤ 1 := by nlinarith [sq_nonneg ‖g 1 0‖]
  exact (norm_add_le _ _).trans (by linarith)

lemma cubicThetaBaseFixed_trace_two (g : SL(2,ℂ))
    (hg : cubicThetaMobius g (0,1)=(0,1)) (ht : g 0 0+g 1 1=2) : g=1 := by
  obtain ⟨ha,hd⟩ := cubicThetaBaseFixed_row_norms g hg
  have hr := congrArg Complex.re ht
  have hr2 : (2:ℂ).re=(2:ℝ) := rfl
  rw [Complex.add_re,hr2] at hr
  simp only [Complex.normSq_apply] at ha hd
  have har : (g 0 0).re ≤ 1 := by
    nlinarith [sq_nonneg (g 0 0).im,sq_nonneg (g 0 1).re,sq_nonneg (g 0 1).im]
  have hdr : (g 1 1).re ≤ 1 := by
    nlinarith [sq_nonneg (g 1 1).im,sq_nonneg (g 1 0).re,sq_nonneg (g 1 0).im]
  have har' : (g 0 0).re=1 := by linarith
  have hdr' : (g 1 1).re=1 := by linarith
  rw [har'] at ha
  rw [hdr'] at hd
  have hai : (g 0 0).im=0 := by
    nlinarith [sq_nonneg (g 0 1).re,sq_nonneg (g 0 1).im]
  have hdi : (g 1 1).im=0 := by
    nlinarith [sq_nonneg (g 1 0).re,sq_nonneg (g 1 0).im]
  have hbr : (g 0 1).re=0 := by
    nlinarith [sq_nonneg (g 0 0).im,sq_nonneg (g 0 1).im]
  have hbi : (g 0 1).im=0 := by
    nlinarith [sq_nonneg (g 0 0).im,sq_nonneg (g 0 1).re]
  have hcr : (g 1 0).re=0 := by
    nlinarith [sq_nonneg (g 1 1).im,sq_nonneg (g 1 0).im]
  have hci : (g 1 0).im=0 := by
    nlinarith [sq_nonneg (g 1 1).im,sq_nonneg (g 1 0).re]
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [har',hdr',hai,hdi,hbr,hbi,hcr,hci]

lemma cubicThetaMatrixTrace_conjugate (h g : SL(2,ℂ)) :
    (h⁻¹*g*h) 0 0+(h⁻¹*g*h) 1 1=g 0 0+g 1 1 := by
  have he : Matrix.trace ((h⁻¹*g*h).val)=Matrix.trace g.val := by
    rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.trace_mul_cycle]
    rw [← Matrix.SpecialLinearGroup.coe_mul,mul_inv_cancel,Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mul]
  simpa [Matrix.trace,Fin.sum_univ_two] using he

lemma cubicThetaFixed_trace_norm (p : CubicThetaPoint) (g : SL(2,ℂ))
    (hg : cubicThetaMobius g p.val=p.val) : ‖g 0 0+g 1 1‖ ≤ 2 := by
  have h := cubicThetaBaseFixed_trace_norm _ (cubicThetaPointFrame_conjugate_fixed p g hg)
  rwa [cubicThetaMatrixTrace_conjugate] at h

lemma cubicThetaFixed_trace_two (p : CubicThetaPoint) (g : SL(2,ℂ))
    (hg : cubicThetaMobius g p.val=p.val) (ht : g 0 0+g 1 1=2) : g=1 := by
  have hc : (cubicThetaPointFrame p)⁻¹*g*cubicThetaPointFrame p=1 := by
    apply cubicThetaBaseFixed_trace_two _ (cubicThetaPointFrame_conjugate_fixed p g hg)
    rwa [cubicThetaMatrixTrace_conjugate]
  have he := congrArg (fun u => cubicThetaPointFrame p*u*(cubicThetaPointFrame p)⁻¹) hc
  simpa [mul_assoc] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMobiusGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation and level inversion matrices in the exact coordinates
used by the cubic theta Fourier and Mellin expansions. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaTranslationMatrix (t : ℂ) : SL(2,ℂ) :=
  ⟨!![1,t;0,1],by simp [Matrix.det_fin_two]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive quadratic majorant for the initial cubic Eisenstein series.
This supplies actual convergence, rather than relying on formal reindexing. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaHeightConstant (p : ℂ × ℝ) : ℝ :=
  2*(2+(1+2*Complex.normSq p.1)/p.2^2)

lemma normSq_sub_le (a b : ℂ) :
    Complex.normSq (a-b) ≤ 2*Complex.normSq a+2*Complex.normSq b := by
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  nlinarith [sq_nonneg (a.re+b.re),sq_nonneg (a.im+b.im)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactRowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform arithmetic row bounds for transformations between two
compact positive-height charts. These bounds give local finiteness of
the actual arithmetic action. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

def heightControl (p : ℂ × ℝ) : ℝ :=
  (2+(1+2*Complex.normSq p.1)/p.2^2)*p.2

lemma heightControl_continuousOn {K : Set (ℂ × ℝ)}
    (hK : ∀ p∈K, 0<p.2) : ContinuousOn heightControl K := by
  intro p hp
  unfold heightControl
  fun_prop (disch := exact pow_ne_zero _ (hK p hp).ne')

lemma inverseHeight_continuousOn {K : Set (ℂ × ℝ)}
    (hK : ∀ p∈K, 0<p.2) : ContinuousOn (fun p : ℂ × ℝ => 1/p.2) K := by
  intro p hp
  exact (continuousAt_const.div continuous_snd.continuousAt (hK p hp).ne').continuousWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProperAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Eisenstein and principal-group actions are properly
discontinuous. This supplies the topological quotient needed for global
cusp gluing from proved compact-chart transport bounds. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

instance cubicThetaPoint_topology : TopologicalSpace CubicThetaPoint :=
  inferInstanceAs (TopologicalSpace {p : ℂ × ℝ // 0<p.2})

instance cubicThetaPoint_t2 : T2Space CubicThetaPoint :=
  inferInstanceAs (T2Space {p : ℂ × ℝ // 0<p.2})

instance cubicThetaPoint_secondCountable : SecondCountableTopology CubicThetaPoint :=
  inferInstanceAs (SecondCountableTopology {p : ℂ × ℝ // 0<p.2})

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual topological quotient by the principal level-three group.
Proper discontinuity supplies Hausdorffness; the open quotient map
preserves local compactness. -/
noncomputable section
namespace CubicFirstMoment

instance cubicThetaPoint_locallyCompact : LocallyCompactSpace CubicThetaPoint :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ × ℝ | 0<p.2}).locallyCompactSpace

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotientCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete local coordinate charts for the principal quotient, obtained
from the proved covering map and the open positive-height half-space. -/
noncomputable section
open Topology
namespace CubicFirstMoment

def positiveHeightOpen : TopologicalSpace.Opens (ℂ × ℝ) :=
  ⟨{p | 0<p.2},isOpen_lt continuous_const continuous_snd⟩

def cubicThetaPointInclusion : OpenPartialHomeomorph CubicThetaPoint (ℂ × ℝ) :=
  positiveHeightOpen.openPartialHomeomorphSubtypeCoe ⟨⟨(0,1),by change (0:ℝ)<1; norm_num⟩⟩

lemma cubicThetaPointInclusion_source : cubicThetaPointInclusion.source=Set.univ := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable choice of representatives for the actual principal
quotient, obtained from a countable disjoint refinement of covering charts. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

instance cubicThetaPoint_measurableSpace : MeasurableSpace CubicThetaPoint := borel _
instance cubicThetaPoint_borelSpace : BorelSpace CubicThetaPoint := ⟨rfl⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-circle coefficients of the actual fixed-height theta series.
Both orientations retain their precise signed angular coefficients. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

local instance instFactLtRealOfNat_solutions_5 : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMobiusSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the literal matrix action on positive-height points. -/
noncomputable section
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

lemma cubicThetaMobiusDenominator_contDiff (g : SL(2,ℂ)) :
    ContDiff ℝ ∞ (cubicThetaMobiusDenominator g) := by
  have hn : ContDiff ℝ ∞ Complex.normSq := by
    change ContDiff ℝ ∞ (fun z : ℂ => Complex.reCLM z*Complex.reCLM z+
      Complex.imCLM z*Complex.imCLM z)
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  exact (hn.comp (by fun_prop)).add (contDiff_const.mul (contDiff_snd.pow 2))

lemma cubicThetaMobiusNumerator_contDiff (g : SL(2,ℂ)) :
    ContDiff ℝ ∞ (cubicThetaMobiusNumerator g) := by
  have hz : ContDiff ℝ ∞ (fun p : ℂ × ℝ => g 1 0*p.1+g 1 1) := by fun_prop
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℝ => star (g 1 0*p.1+g 1 1)) := by
    simpa only [Function.comp_def,Complex.star_def,Complex.conjCLE_apply] using Complex.conjCLE.contDiff.comp hz
  exact ((by fun_prop : ContDiff ℝ ∞ (fun p : ℂ × ℝ => g 0 0*p.1+g 0 1)).mul hc).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_snd.pow 2)))

lemma cubicThetaMobius_contDiffAt (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (cubicThetaMobius g) p := by
  have hD := (cubicThetaMobiusDenominator_contDiff g).contDiffAt (x:=p)
  have hN := (cubicThetaMobiusNumerator_contDiff g).contDiffAt (x:=p)
  have hd := (cubicThetaMobius_denominator_pos g hp).ne'
  unfold cubicThetaMobius
  simp only [div_eq_mul_inv]
  exact (hN.mul ((Complex.ofRealCLM.contDiff.contDiffAt.comp p hD).inv
    (Complex.ofReal_ne_zero.mpr hd))).prodMk (contDiffAt_snd.mul (hD.inv hd))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTangentIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized differential of an actual Mobius transformation is
an orthogonal automorphism of the three-dimensional real tangent space. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

abbrev CubicThetaTangent := WithLp 2 (ℂ × ℝ)

def cubicThetaTangentCoordinates : CubicThetaTangent ≃L[ℝ] ℂ × ℝ :=
  (WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).toContinuousLinearEquiv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTangentEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squared differential norm is independent of the orthonormal
tangent frame. This is the complex-valued Dirichlet energy, expressed
as the sum of the real and imaginary dual norms. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaTangentBasis := stdOrthonormalBasis ℝ CubicThetaTangent

def cubicThetaTangentEnergy (L : CubicThetaTangent →L[ℝ] ℂ) : ℝ :=
  ∑ i, ‖L (cubicThetaTangentBasis i)‖^2

lemma cubicThetaTangentEnergy_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ CubicThetaTangent) (L : CubicThetaTangent →L[ℝ] ℂ) :
    (∑ i, ‖L (b i)‖^2)=‖Complex.reCLM.comp L‖^2+‖Complex.imCLM.comp L‖^2 := by
  rw [b.norm_dual (Complex.reCLM.comp L),b.norm_dual (Complex.imCLM.comp L),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ContinuousLinearMap.comp_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    ← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The intrinsic tangent energy equals the literal three-coordinate
Euclidean gradient. This connects the global form to the local density. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaTangentEnergy_coordinates (L : (ℂ × ℝ) →L[ℝ] ℂ) :
    cubicThetaTangentEnergy (L.comp cubicThetaTangentCoordinates.toContinuousLinearMap)=
      ‖L (1,0)‖^2+‖L (Complex.I,0)‖^2+‖L (0,1)‖^2 := by
  let bR : OrthonormalBasis Unit ℝ ℝ :=
    FiniteDimensional.orthonormalBasisSingleton Unit ℝ (Module.finrank_self ℝ) 1 (by simp)
  let b := Complex.orthonormalBasisOneI.prod bR
  rw [cubicThetaTangentEnergy,cubicThetaTangentEnergy_basis,
    ← cubicThetaTangentEnergy_basis b]
  simp only [b,OrthonormalBasis.prod_apply,Fintype.sum_sum_type,Function.comp_apply,
    Sum.elim_inl,Sum.elim_inr,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,cubicThetaTangentCoordinates,
    LinearMap.inl_apply,LinearMap.inr_apply]
  simp only [Fintype.sum_unique,bR,FiniteDimensional.orthonormalBasisSingleton_apply,
    Fin.sum_univ_succ,Complex.coe_orthonormalBasisOneI,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalEnergyJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual local hyperbolic energy jets: the value has weight v^(-3/2),
and each Euclidean derivative has weight v^(-1/2). Their squared norm
is the hyperbolic mass plus Dirichlet density. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

abbrev CubicThetaLocalJet := EuclideanSpace ℂ (Fin 4)

def cubicThetaLocalEnergyJet (f : ℂ × ℝ → ℂ) (y : ℂ × ℝ) : CubicThetaLocalJet :=
  WithLp.toLp 2 ![(y.2^(-3/2:ℝ)) • f y,
    (y.2^(-1/2:ℝ)) • fderiv ℝ f y (1,0),
    (y.2^(-1/2:ℝ)) • fderiv ℝ f y (Complex.I,0),
    (y.2^(-1/2:ℝ)) • fderiv ℝ f y (0,1)]

lemma cubicTheta_weighted_positive_continuous (a : ℝ) {f : ℂ × ℝ → ℂ}
    (hf : Continuous f) (hp : tsupport f ⊆ {y : ℂ × ℝ | 0<y.2}) :
    Continuous (fun y => (y.2^a) • f y) := by
  have hw : ContinuousOn (fun y : ℂ × ℝ => y.2^a) {y | 0<y.2} :=
    continuous_snd.continuousOn.rpow_const (fun y hy => Or.inl hy.ne')
  apply (hw.smul hf.continuousOn).continuous_of_tsupport_subset
    (isOpen_lt continuous_const continuous_snd)
  exact (tsupport_smul_subset_right (fun y : ℂ × ℝ => y.2^a) f).trans hp

lemma cubicThetaLocalEnergyJet_continuous {f : ℂ × ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hp : tsupport f ⊆ {y : ℂ × ℝ | 0<y.2}) :
    Continuous (cubicThetaLocalEnergyJet f) := by
  have hd (v : ℂ × ℝ) : Continuous (fun y => fderiv ℝ f y v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hs (v : ℂ × ℝ) : tsupport (fun y => fderiv ℝ f y v) ⊆ {y : ℂ × ℝ | 0<y.2} :=
    (tsupport_fderiv_apply_subset (𝕜:=ℝ) (f:=f) v).trans hp
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact cubicTheta_weighted_positive_continuous _ hf.continuous hp
  · exact cubicTheta_weighted_positive_continuous _ (hd _) (hs _)
  · exact cubicTheta_weighted_positive_continuous _ (hd _) (hs _)
  · exact cubicTheta_weighted_positive_continuous _ (hd _) (hs _)

lemma cubicThetaLocalEnergyJet_compact {f : ℂ × ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (cubicThetaLocalEnergyJet f) := by
  apply hf.mono'
  intro y hy
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  have hd := fderiv_of_notMem_tsupport (𝕜:=ℝ) hn
  apply hy
  ext i
  fin_cases i <;> simp [cubicThetaLocalEnergyJet,hz,hd]

lemma cubicThetaLocalEnergyJet_memLp {f : ℂ × ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ {y : ℂ × ℝ | 0<y.2}) :
    MemLp (cubicThetaLocalEnergyJet f) 2 (volume : Measure (ℂ × ℝ)) :=
  (cubicThetaLocalEnergyJet_continuous hf hp).memLp_of_hasCompactSupport
    (cubicThetaLocalEnergyJet_compact hc)

lemma cubicThetaLocalEnergyJet_norm_sq (f : ℂ × ℝ → ℂ) {y : ℂ × ℝ} (hy : 0<y.2) :
    ‖cubicThetaLocalEnergyJet f y‖^2=‖f y‖^2/y.2^3+
      (‖fderiv ℝ f y (1,0)‖^2+‖fderiv ℝ f y (Complex.I,0)‖^2+
        ‖fderiv ℝ f y (0,1)‖^2)/y.2 := by
  have hw (a : ℝ) : (y.2^a)^2=y.2^(a*2) := (Real.rpow_mul_natCast hy.le a 2).symm
  have h₁ : (y.2^(-3/2:ℝ))^2=(y.2^3)⁻¹ := by rw [hw]; norm_num
  have h₂ : (y.2^(-1/2:ℝ))^2=y.2⁻¹ := by rw [hw]; norm_num [Real.rpow_neg_one]
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [cubicThetaLocalEnergyJet,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hy.le _),mul_pow,h₁,h₂]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCutoffEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative product estimates for the compact core cutoffs.
The coefficient is compactly supported, so its supremum is finite. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaTangentEnergy_nonneg (L : CubicThetaTangent →L[ℝ] ℂ) :
    0 ≤ cubicThetaTangentEnergy L := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

def cubicThetaFunctionEnergy (f : ℂ × ℝ → ℂ) (y : ℂ × ℝ) : ℝ :=
  cubicThetaTangentEnergy ((fderiv ℝ f y).comp cubicThetaTangentCoordinates.toContinuousLinearMap)

lemma cubicThetaLocalEnergyJet_density (f : ℂ × ℝ → ℂ) {y : ℂ × ℝ} (hy : 0<y.2) :
    ‖cubicThetaLocalEnergyJet f y‖^2=
      (‖f y‖^2+y.2^2*cubicThetaFunctionEnergy f y)/y.2^3 := by
  rw [cubicThetaLocalEnergyJet_norm_sq f hy]
  unfold cubicThetaFunctionEnergy
  rw [cubicThetaTangentEnergy_coordinates]
  field_simp [hy.ne']

lemma cubicThetaFunctionEnergy_continuous {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (cubicThetaFunctionEnergy φ) := by
  unfold cubicThetaFunctionEnergy cubicThetaTangentEnergy
  apply continuous_finsetSum
  intro i hi
  exact (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm).pow 2

lemma cubicThetaFunctionEnergy_compact {φ : ℂ × ℝ → ℂ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (cubicThetaFunctionEnergy φ) := by
  apply hφ.mono'
  intro y hy
  by_contra hn
  have hd := fderiv_of_notMem_tsupport (𝕜:=ℝ) hn
  apply hy
  simp only [cubicThetaFunctionEnergy,hd,ContinuousLinearMap.zero_comp,
    cubicThetaTangentEnergy,zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactEnergyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a fixed compact subset of positive height, the hyperbolic
energy controls the Euclidean energy with one uniform constant. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaCompact_euclideanEnergy_bound {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : K⊆{y : ℂ × ℝ | 0<y.2}) :
    ∃ C≥0, ∀ (f : ℂ × ℝ → ℂ), tsupport f⊆K → ∀ y,
      ‖f y‖^2+cubicThetaFunctionEnergy f y≤C*‖cubicThetaLocalEnergyJet f y‖^2 := by
  obtain ⟨H₀,hH₀⟩ := hK.exists_bound_of_continuousOn continuous_snd.continuousOn
  let H := max H₀ 0
  have hH : 0≤H := le_max_right _ _
  have hC : 0≤H^3+H := add_nonneg (pow_nonneg hH _) hH
  refine ⟨H^3+H,hC,fun f hf y => ?_⟩
  by_cases hyK : y∈K
  · have hy : 0<y.2 := hpos hyK
    have hvH : y.2≤H := (le_abs_self _).trans ((hH₀ y hyK).trans (le_max_left _ _))
    have hv3 : y.2^3≤H^3 := by gcongr
    have hE : 0 ≤ cubicThetaFunctionEnergy f y := cubicThetaTangentEnergy_nonneg _
    have hA := mul_le_mul_of_nonneg_right hv3 (sq_nonneg ‖f y‖)
    have hB := mul_le_mul_of_nonneg_right hvH (mul_nonneg (sq_nonneg y.2) hE)
    rw [cubicThetaLocalEnergyJet_density f hy,← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hy 3)).mpr
    nlinarith [mul_nonneg hH (sq_nonneg ‖f y‖),
      mul_nonneg (pow_nonneg hH 3) (mul_nonneg (sq_nonneg y.2) hE)]
  · have hyf : y∉tsupport f := fun hy => hyK (hf hy)
    have hz := image_eq_zero_of_notMem_tsupport hyf
    have hd := fderiv_of_notMem_tsupport (𝕜:=ℝ) hyf
    have hr := mul_nonneg hC (sq_nonneg ‖cubicThetaLocalEnergyJet f y‖)
    simpa only [hz,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
      cubicThetaFunctionEnergy,hd,ContinuousLinearMap.zero_comp,cubicThetaTangentEnergy,
      zero_apply,norm_zero,Finset.sum_const_zero,add_zero] using hr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGridEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of each nonzero actual Eisenstein row term with a
translated hyperbolic kernel, and its eigenvalue equation. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaCartesianPoint (x y v : ℝ) : ℂ × ℝ :=
  ((x:ℂ)+(y:ℂ)*Complex.I,v)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGridAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate analyticity of every actual Eisenstein summand in the
positive upper half-space. -/
noncomputable section
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def CubicThetaCoordinateAnalytic (F : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) : Prop :=
  AnalyticAt ℝ (fun t : ℝ => F t y v) x ∧
    AnalyticAt ℝ (fun t : ℝ => F x t v) y ∧
    AnalyticAt ℝ (fun t : ℝ => F x y t) v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateAxis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate lines used for the spatial derivatives of the series. -/
noncomputable section
namespace CubicFirstMoment

inductive CubicThetaAxis where
  | x | y | height

def cubicThetaCoordinateLine (k : CubicThetaAxis) (x y v t : ℝ) : ℂ × ℝ :=
  match k with
  | .x => cubicThetaCartesianPoint t y v
  | .y => cubicThetaCartesianPoint x t v
  | .height => cubicThetaCartesianPoint x y t

def cubicThetaCoordinateCenter (k : CubicThetaAxis) (x y v : ℝ) : ℝ :=
  match k with
  | .x => x
  | .y => y
  | .height => v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common relative bounds for the first and second coordinate jets.
They are preserved by scalar multiplication and horizontal translation. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaAxisFunction (F : ℝ → ℝ → ℝ → ℂ) (k : CubicThetaAxis)
    (x y v : ℝ) : ℝ → ℂ :=
  match k with
  | .x => fun t => F t y v
  | .y => fun t => F x t v
  | .height => fun t => F x y t

def cubicThetaFirstJetConstant (s : ℂ) : ℝ := 3*‖s‖

def cubicThetaSecondJetConstant (s : ℂ) : ℝ :=
  2*‖s‖+‖s*(s-1)‖+‖4*s^2+2*s‖+4*‖s‖*‖s+1‖

def CubicThetaCoordinateJetBound (F : ℝ → ℝ → ℝ → ℂ) (s : ℂ) (x y v : ℝ) : Prop :=
  ∀ k : CubicThetaAxis,
    ‖deriv (cubicThetaAxisFunction F k x y v) (cubicThetaCoordinateCenter k x y v)‖ ≤
      ‖F x y v‖*(cubicThetaFirstJetConstant s/v) ∧
    ‖deriv (deriv (cubicThetaAxisFunction F k x y v)) (cubicThetaCoordinateCenter k x y v)‖ ≤
      ‖F x y v‖*(cubicThetaSecondJetConstant s/v^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcingProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The forcing profile is an entire function with values in the
supremum-norm space on the fixed radial annulus. -/
noncomputable section
namespace CubicFirstMoment

abbrev CubicThetaForcingBand := ↥(Set.Icc (1:ℝ) 2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHyperbolicMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual invariant hyperbolic measure on positive-height points.
Its density is v^-3, and arithmetic invariance follows from the proved
Jacobian, not from an assumed invariant measure. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ENNReal
namespace CubicFirstMoment

def cubicThetaHyperbolicDensity (p : ℂ × ℝ) : ℝ≥0∞ := ENNReal.ofReal ((p.2^3)⁻¹)

def cubicThetaHyperbolicMeasure : Measure (ℂ × ℝ) :=
  volume.withDensity cubicThetaHyperbolicDensity

def cubicThetaPointCoordinates (p : CubicThetaPoint) : ℂ × ℝ := p.val

def cubicThetaPointMeasure : Measure CubicThetaPoint :=
  cubicThetaHyperbolicMeasure.comap cubicThetaPointCoordinates

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual L2 gradient vector, obtained by evaluating the differential
in an orthonormal frame at the measurable representative. Its norm is
intrinsic even though its coordinates use that representative. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

abbrev CubicThetaTangentIndex := Fin (Module.finrank ℝ CubicThetaTangent)
abbrev CubicThetaGradient := EuclideanSpace ℂ CubicThetaTangentIndex

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIntegerBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coordinate boxes for the quantitative arithmetic theta tail. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace CubicFirstMoment

abbrev CubicThetaIntegerPoint := ℤ × ℤ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalEnergyGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local graph of genuine compact smooth sections and its closed
Hilbert energy space. The value and derivative entries remain tied to the
same localized section throughout the construction. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

abbrev CubicThetaLocalEnergyAmbient := Lp CubicThetaLocalJet 2 (volume : Measure (ℂ × ℝ))

lemma cubicThetaLocalEnergyJet_add {f g : ℂ × ℝ → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (y : ℂ × ℝ) :
    cubicThetaLocalEnergyJet (f+g) y=cubicThetaLocalEnergyJet f y+cubicThetaLocalEnergyJet g y := by
  ext i
  fin_cases i <;>
    simp [cubicThetaLocalEnergyJet,fderiv_add (hf y) (hg y),smul_add]

lemma cubicThetaLocalEnergyJet_smul (c : ℂ) {f : ℂ × ℝ → ℂ}
    (hf : Differentiable ℝ f) (y : ℂ × ℝ) :
    cubicThetaLocalEnergyJet (c • f) y=c • cubicThetaLocalEnergyJet f y := by
  ext i
  fin_cases i <;>
    simp [cubicThetaLocalEnergyJet,fderiv_const_smul (hf y) c] <;> ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialEnergyNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The energy norm is the literal radial quadratic form, including
its exponential Fourier potential. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicTheta_l2_norm_sq_measure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {X : Type*} [MeasurableSpace X] {μ : Measure X} (F : Lp E 2 μ) :
    ‖F‖^2=∫ t : X, ‖F t‖^2 ∂μ := by
  calc
    _ = (inner ℂ F F).re := (inner_self_eq_norm_sq (𝕜:=ℂ) F).symm
    _ = ∫ t : X, (inner ℂ (F t) (F t)).re ∂μ :=
      (integral_re (L2.integrable_inner (𝕜:=ℂ) F F)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      exact inner_self_eq_norm_sq (𝕜:=ℂ) (F t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTangentSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local complex energy has genuine real and imaginary Sobolev
components in Euclidean Sobolev space. The change from
product coordinates to the Hilbert tangent space preserves volume. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

namespace LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

lemma tangentCoordinates_measurePreserving : MeasurePreserving cubicThetaTangentCoordinates
    (volume : Measure CubicThetaTangent) (volume : Measure (ℂ × ℝ)) := by
  exact WithLp.volume_preserving_ofLp ℂ ℝ

def tangentBorelVolume : @Measure CubicThetaTangent (borel CubicThetaTangent) := by
  let : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
  let : BorelSpace CubicThetaTangent := ⟨rfl⟩
  exact volume

instance tangentBorelVolume_finiteOnCompacts :
    let : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
    IsFiniteMeasureOnCompacts tangentBorelVolume := by
  let : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
  let : BorelSpace CubicThetaTangent := ⟨rfl⟩
  change IsFiniteMeasureOnCompacts (volume : Measure CubicThetaTangent)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def realTest (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    C1c (E:=CubicThetaTangent) :=
  ⟨fun u => (f (cubicThetaTangentCoordinates u)).re,
    (Complex.reCLM.contDiff.comp (hf.comp cubicThetaTangentCoordinates.contDiff)),
    (hc.comp_homeomorph cubicThetaTangentCoordinates.toHomeomorph).comp_left (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)⟩

def imagTest (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    C1c (E:=CubicThetaTangent) :=
  ⟨fun u => (f (cubicThetaTangentCoordinates u)).im,
    (Complex.imCLM.contDiff.comp (hf.comp cubicThetaTangentCoordinates.contDiff)),
    (hc.comp_homeomorph cubicThetaTangentCoordinates.toHomeomorph).comp_left (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)⟩

def realH1 (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    h1 (E:=CubicThetaTangent) (μ:=tangentBorelVolume) :=
  ⟨graph (E:=CubicThetaTangent) (μ:=tangentBorelVolume) (realTest f hf hc),
    Submodule.le_topologicalClosure _ ⟨realTest f hf hc,rfl⟩⟩

def imagH1 (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    h1 (E:=CubicThetaTangent) (μ:=tangentBorelVolume) :=
  ⟨graph (E:=CubicThetaTangent) (μ:=tangentBorelVolume) (imagTest f hf hc),
    Submodule.le_topologicalClosure _ ⟨imagTest f hf hc,rfl⟩⟩

lemma realTest_fderiv (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (u : CubicThetaTangent) :
    fderiv ℝ (realTest f hf hc) u=Complex.reCLM.comp
      ((fderiv ℝ f (cubicThetaTangentCoordinates u)).comp
        cubicThetaTangentCoordinates.toContinuousLinearMap) := by
  exact (Complex.reCLM.hasFDerivAt.comp u
    ((hf.differentiable one_ne_zero _).hasFDerivAt.comp u
      cubicThetaTangentCoordinates.hasFDerivAt)).fderiv

lemma imagTest_fderiv (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (u : CubicThetaTangent) :
    fderiv ℝ (imagTest f hf hc) u=Complex.imCLM.comp
      ((fderiv ℝ f (cubicThetaTangentCoordinates u)).comp
        cubicThetaTangentCoordinates.toContinuousLinearMap) := by
  exact (Complex.imCLM.hasFDerivAt.comp u
    ((hf.differentiable one_ne_zero _).hasFDerivAt.comp u
      cubicThetaTangentCoordinates.hasFDerivAt)).fderiv

lemma gradient_norm_sq (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (u : CubicThetaTangent) :
    ‖grad (realTest f hf hc) u‖^2+‖grad (imagTest f hf hc) u‖^2=
      cubicThetaFunctionEnergy f (cubicThetaTangentCoordinates u) := by
  simp only [grad,LinearIsometryEquiv.norm_map,realTest_fderiv,imagTest_fderiv]
  exact (cubicThetaTangentEnergy_basis cubicThetaTangentBasis _).symm

end LocalSobolev
end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTangentVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the Borel measure used by the Sobolev library with the
canonical tangent volume. This removes the measurable-space diamond
without changing or postulating a measure. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment.LocalSobolev

lemma canonicalVolume_transport (m : MeasurableSpace CubicThetaTangent)
    (hm : borel CubicThetaTangent=m) :
    letI : MeasurableSpace CubicThetaTangent := m
    letI : BorelSpace CubicThetaTangent := ⟨hm.symm⟩
    (volume : Measure CubicThetaTangent)=Eq.ndrec (motive:=fun m => @Measure CubicThetaTangent m) tangentBorelVolume hm := by
  subst m
  rfl

lemma map_transport (m : MeasurableSpace CubicThetaTangent)
    (hm : borel CubicThetaTangent=m) :
    @Measure.map CubicThetaTangent (ℂ × ℝ) m inferInstance cubicThetaTangentCoordinates
        (Eq.ndrec (motive:=fun m => @Measure CubicThetaTangent m) tangentBorelVolume hm)=
      @Measure.map CubicThetaTangent (ℂ × ℝ) (borel CubicThetaTangent) inferInstance
        cubicThetaTangentCoordinates tangentBorelVolume := by
  subst m
  rfl

lemma tangentBorelVolume_map :
    @Measure.map CubicThetaTangent (ℂ × ℝ) (borel CubicThetaTangent) inferInstance
      cubicThetaTangentCoordinates tangentBorelVolume=volume := by
  have he := canonicalVolume_transport (inferInstance : MeasurableSpace CubicThetaTangent) BorelSpace.measurable_eq.symm
  have hm := tangentCoordinates_measurePreserving.map_eq
  rw [he,map_transport] at hm
  exact hm

lemma tangentBorelVolume_measurePreserving :
    letI : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
    MeasurePreserving cubicThetaTangentCoordinates tangentBorelVolume
      (volume : Measure (ℂ × ℝ)) := by
  let : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
  let : BorelSpace CubicThetaTangent := ⟨rfl⟩
  exact ⟨cubicThetaTangentCoordinates.continuous.measurable,tangentBorelVolume_map⟩

lemma tangentBorelVolume_integral (f : ℂ × ℝ → ℝ) :
    (∫ u, f (cubicThetaTangentCoordinates u) ∂tangentBorelVolume)=∫ y, f y := by
  let : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
  let : BorelSpace CubicThetaTangent := ⟨rfl⟩
  exact tangentBorelVolume_measurePreserving.integral_comp
    cubicThetaTangentCoordinates.toHomeomorph.measurableEmbedding f

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSupportedTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported complex chart sections give actual supported
real Sobolev vectors. The Euclidean Rellich theorem applies to these
vectors, with the concrete transported compact support. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance tangent_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance tangent_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩

lemma realTest_support {K : Set (ℂ × ℝ)} (f : ℂ × ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hK : tsupport f⊆K) :
    tsupport (realTest f hf hc : CubicThetaTangent → ℝ)⊆cubicThetaTangentCoordinates ⁻¹' K := by
  change tsupport (Complex.re ∘ (f ∘ cubicThetaTangentCoordinates))⊆_
  exact (tsupport_comp_subset (g:=Complex.re) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _).trans
    ((tsupport_comp_subset_preimage f cubicThetaTangentCoordinates.continuous).trans (preimage_mono hK))

lemma imagTest_support {K : Set (ℂ × ℝ)} (f : ℂ × ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hK : tsupport f⊆K) :
    tsupport (imagTest f hf hc : CubicThetaTangent → ℝ)⊆cubicThetaTangentCoordinates ⁻¹' K := by
  change tsupport (Complex.im ∘ (f ∘ cubicThetaTangentCoordinates))⊆_
  exact (tsupport_comp_subset (g:=Complex.im) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _).trans
    ((tsupport_comp_subset_preimage f cubicThetaTangentCoordinates.continuous).trans (preimage_mono hK))

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalRellich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two supported real Sobolev components give a compact complex
L2 inclusion on every concrete compact coordinate set. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance localRellich_tangent_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance localRellich_tangent_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩

abbrev TangentComplexL2 := Lp ℂ 2 tangentBorelVolume

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSobolevEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real and imaginary Sobolev vectors are bounded by the
complex Euclidean energy integral. This is the norm comparison needed
to apply the local compact inclusion to the automorphic energy. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance sobolevEnergy_tangent_borel_re72163_1 : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance sobolevEnergy_tangent_borelSpace_re72163_1 : BorelSpace CubicThetaTangent := ⟨rfl⟩
lemma l2_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : Lp V 2 tangentBorelVolume) : ‖u‖^2=∫ x, ‖u x‖^2 ∂tangentBorelVolume := by
  calc
    _ = inner ℝ u u := (real_inner_self_eq_norm_sq u).symm
    _ = ∫ x, inner ℝ (u x) (u x) ∂tangentBorelVolume := L2.inner_def u u
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      exact real_inner_self_eq_norm_sq (u x)

lemma value_norm_sq (g : C1c (E:=CubicThetaTangent)) :
    ‖toL2 (μ:=tangentBorelVolume) g‖^2=∫ x, ‖(g:CubicThetaTangent → ℝ) x‖^2 ∂tangentBorelVolume := by
  rw [l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [(memLp_of_mem_C1c (μ:=tangentBorelVolume) g.property).coeFn_toLp] with x hx
  change ‖((memLp_of_mem_C1c (μ:=tangentBorelVolume) g.property).toLp _) x‖^2=_
  rw [hx]

lemma gradientL2_norm_sq (g : C1c (E:=CubicThetaTangent)) :
    ‖toL2Grad (μ:=tangentBorelVolume) g‖^2=∫ x, ‖grad (g:CubicThetaTangent → ℝ) x‖^2 ∂tangentBorelVolume := by
  rw [l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [(memLp_grad_of_mem_C1c (μ:=tangentBorelVolume) g.property).coeFn_toLp] with x hx
  change ‖((memLp_grad_of_mem_C1c (μ:=tangentBorelVolume) g.property).toLp _) x‖^2=_
  rw [hx]

lemma four_norms_eq (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ‖toL2 (μ:=tangentBorelVolume) (realTest f hf hc)‖^2+
      ‖toL2 (μ:=tangentBorelVolume) (imagTest f hf hc)‖^2+
      ‖toL2Grad (μ:=tangentBorelVolume) (realTest f hf hc)‖^2+
      ‖toL2Grad (μ:=tangentBorelVolume) (imagTest f hf hc)‖^2=
        ∫ y, ‖f y‖^2+cubicThetaFunctionEnergy f y := by
  let r := realTest f hf hc
  let i := imagTest f hf hc
  have hr := (memLp_of_mem_C1c (μ:=tangentBorelVolume) r.property).integrable_norm_pow (by norm_num)
  have hi := (memLp_of_mem_C1c (μ:=tangentBorelVolume) i.property).integrable_norm_pow (by norm_num)
  have hdr := (memLp_grad_of_mem_C1c (μ:=tangentBorelVolume) r.property).integrable_norm_pow (by norm_num)
  have hdi := (memLp_grad_of_mem_C1c (μ:=tangentBorelVolume) i.property).integrable_norm_pow (by norm_num)
  have h₁ := integral_add hr hi
  have h₂ := integral_add (hr.add hi) hdr
  have h₃ := integral_add ((hr.add hi).add hdr) hdi
  simp only [Pi.add_apply] at h₁ h₂ h₃
  rw [h₂,h₁] at h₃
  rw [value_norm_sq,value_norm_sq,gradientL2_norm_sq,gradientL2_norm_sq,← h₃]

  calc
    _ = ∫ u, ‖f (cubicThetaTangentCoordinates u)‖^2+
        cubicThetaFunctionEnergy f (cubicThetaTangentCoordinates u) ∂tangentBorelVolume := by
      apply integral_congr_ae
      filter_upwards with u
      have hg := LocalSobolev.gradient_norm_sq f hf hc u
      have hv : ‖(realTest f hf hc : CubicThetaTangent → ℝ) u‖^2+
          ‖(imagTest f hf hc : CubicThetaTangent → ℝ) u‖^2=
          ‖f (cubicThetaTangentCoordinates u)‖^2 := by
        simp only [realTest,imagTest,Real.norm_eq_abs,sq_abs,← Complex.normSq_eq_norm_sq,
          Complex.normSq_apply]
        ring
      linear_combination hv+hg
    _ = _ := tangentBorelVolume_integral (fun y => ‖f y‖^2+cubicThetaFunctionEnergy f y)

lemma prod_norm_sq_le {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    (v : V) (w : W) : ‖(v,w)‖^2≤‖v‖^2+‖w‖^2 := by
  rw [Prod.norm_mk]
  rcases le_total ‖v‖ ‖w‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖v‖]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg ‖w‖]

lemma sobolev_pair_norm_sq_le (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ‖(realH1 f hf hc,imagH1 f hf hc)‖^2≤∫ y, ‖f y‖^2+cubicThetaFunctionEnergy f y := by
  have hr : ‖realH1 f hf hc‖^2≤
      ‖toL2 (μ:=tangentBorelVolume) (realTest f hf hc)‖^2+
      ‖toL2Grad (μ:=tangentBorelVolume) (realTest f hf hc)‖^2 :=
    prod_norm_sq_le _ _
  have hi : ‖imagH1 f hf hc‖^2≤
      ‖toL2 (μ:=tangentBorelVolume) (imagTest f hf hc)‖^2+
      ‖toL2Grad (μ:=tangentBorelVolume) (imagTest f hf hc)‖^2 :=
    prod_norm_sq_le _ _
  have hp := prod_norm_sq_le (realH1 f hf hc) (imagH1 f hf hc)
  rw [← four_norms_eq f hf hc]
  linarith

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalizationSobolevBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Sobolev bounds for the actual localized sections. Together
with the proved supported compact inclusion, these control the core
localization by its hyperbolic energy graph norm. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev

lemma functionEnergy_integrable {f : ℂ × ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    Integrable (fun y => ‖f y‖^2+cubicThetaFunctionEnergy f y) := by
  have hv : Continuous (fun y => ‖f y‖^2) := hf.continuous.norm.pow 2
  have he : Continuous (cubicThetaFunctionEnergy f) := cubicThetaFunctionEnergy_continuous hf
  have hvc : HasCompactSupport (fun y => ‖f y‖^2) :=
    hc.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)
  have hec : HasCompactSupport (cubicThetaFunctionEnergy f) := cubicThetaFunctionEnergy_compact hc
  have hi : Integrable (fun y => ‖f y‖^2) (volume : Measure (ℂ × ℝ)) :=
    hv.integrable_of_hasCompactSupport hvc
  have hei : Integrable (cubicThetaFunctionEnergy f) (volume : Measure (ℂ × ℝ)) :=
    he.integrable_of_hasCompactSupport hec
  exact hi.add hei

lemma compact_sobolev_bound {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : K⊆{y : ℂ × ℝ | 0<y.2}) :
    ∃ C≥0, ∀ (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f),
      tsupport f⊆K → ‖(realH1 f hf hc,imagH1 f hf hc)‖^2≤
        C*(∫ y, ‖cubicThetaLocalEnergyJet f y‖^2) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaCompact_euclideanEnergy_bound hK hpos
  refine ⟨C,hC,fun f hf hc hs => ?_⟩
  have hjet := (cubicThetaLocalEnergyJet_memLp hf hc (hs.trans hpos)).integrable_norm_pow
    (by norm_num)
  have hi := integral_mono (functionEnergy_integrable hf hc) (hjet.const_mul C) (hbound f hs)
  rw [integral_const_mul] at hi
  exact (sobolev_pair_norm_sq_le f hf hc).trans hi

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalEnergyRellich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rellich compactness on the completion of the actual local energy
graph. No independent value and derivative data are introduced. -/
noncomputable section
open Set MeasureTheory Topology
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance energyRellich_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance energyRellich_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩

abbrev H1Target (μ : Measure CubicThetaTangent) : Type _ :=
  ↥(CubicThetaTangent →₂[μ] ℝ) × ↥(CubicThetaTangent →₂[μ] CubicThetaTangent)

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalRellichValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact local energy inclusion has the original localized
complex section as its value, rather than an unrelated Sobolev vector. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance rellichValue_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance rellichValue_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩

lemma tangentFunction_memLp (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : MemLp (f ∘ cubicThetaTangentCoordinates) 2 tangentBorelVolume :=
  (hf.continuous.comp cubicThetaTangentCoordinates.continuous).memLp_of_hasCompactSupport
    (hc.comp_homeomorph cubicThetaTangentCoordinates.toHomeomorph)

def tangentFunctionL2 (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : TangentComplexL2 := (tangentFunction_memLp f hf hc).toLp _

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual trace frequencies are the full Fourier basis of the
three-Eisenstein period cell. This fixes the lattice index and Parseval
normalization for the cusp Hilbert space. -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CubicFirstMoment

local instance instMeasureSpaceUnitAddCircle_solutions : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

abbrev CubicThetaTorusL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))

end CubicFirstMoment

end

end OAI
end


