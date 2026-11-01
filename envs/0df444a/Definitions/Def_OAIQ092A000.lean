-- Prove2me | Definitions.Def_OAIQ092A000
-- name    : OAIQ092A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:45:06.78652+00:00
-- url     : https://prove2.me/theorems/3fa6c913-79e5-476e-8d07-c2d1bab9ef91
-- title:
--   Definitions bundle OAIQ092A000 of the split of OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 516 declarations of OpenAI's Lean: 421 definitions, 3 inductive types or structures and 92 theorems. The definitions and types are `MeasureTheory.Lp.extendByZeroFun`, `MeasureTheory.Lp.extendByZeroₗ`, `MeasureTheory.Lp.extendByZeroₗᵢ`, `OAI.ContinuumCoulomb.AffinePhysicalOutput.Input`, `OAI.ContinuumCoulomb.AffinePhysicalOutput.argument`, `OAI.ContinuumCoulomb.AffinePhysicalOutput.inputCode`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.Input`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.argument`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.dataCode`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.dataProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.electronsProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.errorProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.finiteValue`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.inputCode`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.listsProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.numbersProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.pairPrecision`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.pairPrecisionProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.pairValue`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.precisionProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.sitesProgram`, `OAI.ContinuumCoulomb.AffinePhysicalThreshold.value`, `OAI.ContinuumCoulomb.CappedKernelProgram.Input`, `OAI.ContinuumCoulomb.CappedKernelProgram.Triple`, `OAI.ContinuumCoulomb.CappedKernelProgram.approximate`, `OAI.ContinuumCoulomb.CappedKernelProgram.normSquare`, `OAI.ContinuumCoulomb.CappedKernelProgram.tripleCode`, `OAI.ContinuumCoulomb.CenteredGaussLabels.Radii`, `OAI.ContinuumCoulomb.CenteredGaussLabels.radiiCode`, `OAI.ContinuumCoulomb.CenteredNuclearProgram.Input`, `OAI.ContinuumCoulomb.CenteredNuclearProgram.inputCode`, `OAI.ContinuumCoulomb.CenteredPhysicalThreshold.Geometry`, `OAI.ContinuumCoulomb.CenteredPhysicalThreshold.Input`, `OAI.ContinuumCoulomb.CenteredPhysicalThreshold.amplification`, `OAI.ContinuumCoulomb.CenteredPhysicalThreshold.electronsProgram`, `OAI.ContinuumCoulomb.CenteredPhysicalThreshold.errorProgram`, `OAI.ContinuumCoulomb.CenteredPhysicalThreshold.geometryCode`, `OAI.ContinuumCoulomb.CenteredPhysicalThreshold.geometryProgram`, `OAI.ContinuumCoulomb.CenteredPhysicalThreshold.inputCode`, `OAI.ContinuumCoulomb.CenteredPhysicalThreshold.meshCubeProgram` and 384 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing`, `ContinuumCoulomb_Nuclei_SlabBoxSchedule`, `ContinuumCoulomb_Nuclei_SlabOriginSchedule`, `ContinuumCoulomb_Nuclei_SlabOriginValue`, `ContinuumCoulomb_OneParticle_AffinePhysicalOutput`, `ContinuumCoulomb_OneParticle_AffinePhysicalThreshold`, `ContinuumCoulomb_OneParticle_CenteredGaussLabels`, `ContinuumCoulomb_OneParticle_CenteredPhysicalThreshold`, `ContinuumCoulomb_OneParticle_CoulombEvaluationParameters`, `ContinuumCoulomb_OneParticle_CoulombPairEvaluation`, `ContinuumCoulomb_OneParticle_CoulombPairSum`, `ContinuumCoulomb_OneParticle_CoulombQuadrature`, `ContinuumCoulomb_OneParticle_CoulombQuadratureBudget`, `ContinuumCoulomb_OneParticle_CoulombTruncationSchedule`, `ContinuumCoulomb_OneParticle_GaussianFrequency`, `ContinuumCoulomb_OneParticle_GaussianPacket`, `ContinuumCoulomb_OneParticle_LocalizedCoulomb`, `ContinuumCoulomb_OneParticle_LocalizedCoulombLipschitz`, `ContinuumCoulomb_OneParticle_LocalizedDensityMoment`, `ContinuumCoulomb_OneParticle_LocalizedModes`, `ContinuumCoulomb_OneParticle_LocalizedRawDensity`, `ContinuumCoulomb_OneParticle_NormalizationArithmetic`, `ContinuumCoulomb_OneParticle_NormalizationQuadrature`, `ContinuumCoulomb_OneParticle_NormalizationSchedule`, `ContinuumCoulomb_OneParticle_PlanarForcing`, `ContinuumCoulomb_OneParticle_PlanarGroundTransform`, `ContinuumCoulomb_OneParticle_PlanarHeatKernel`, `ContinuumCoulomb_OneParticle_PlanarModeProperties`, `ContinuumCoulomb_OneParticle_PlanarResolvent`, `ContinuumCoulomb_OneParticle_PlanarResolventEquation`, `ContinuumCoulomb_OneParticle_RationalClamp`, `ContinuumCoulomb_OneParticle_RationalExponential`, `ContinuumCoulomb_OneParticle_RationalHeatBox`, `ContinuumCoulomb_OneParticle_RationalHeatSample`, `ContinuumCoulomb_OneParticle_RationalSixQuadrature`, `ContinuumCoulomb_OneParticle_RationalSmoothTransition`, `ContinuumCoulomb_OneParticle_RationalSquareRoot`, `ContinuumCoulomb_OneParticle_RationalTripleQuadrature`, `ContinuumCoulomb_OneParticle_ResolventSchedule`, `ContinuumCoulomb_OneParticle_SplitCoordinates`, `ContinuumCoulomb_OneParticle_TransformedGaussList`, `ContinuumCoulomb_OneParticle_VerticalMode`, `ContinuumCoulomb_Programs_AffinePhysicalThresholdProgram`, `ContinuumCoulomb_Programs_CappedKernelProgram`, `ContinuumCoulomb_Programs_CenteredGaussProgram`, `ContinuumCoulomb_Programs_CenteredNuclearProgram`, `ContinuumCoulomb_Programs_CenteredPhysicalThresholdProgram`, `ContinuumCoulomb_Programs_CoulombEvaluationProgram`, `ContinuumCoulomb_Programs_CoulombNormalizationProgram`, `ContinuumCoulomb_Programs_CoulombPairProgram`, `ContinuumCoulomb_Programs_CoulombPairSumProgram`, `ContinuumCoulomb_Programs_DyadicRootProgram`, `ContinuumCoulomb_Programs_ManufacturedFieldProgram`, `ContinuumCoulomb_Programs_PhysicalNuclearProgram`, `ContinuumCoulomb_Programs_PiProgram`, `ContinuumCoulomb_Programs_PlanarForcingProgram`, `ContinuumCoulomb_Programs_RationalExponentialProgram`, `ContinuumCoulomb_Programs_RationalQuadratureProgram`, `ContinuumCoulomb_Programs_RationalRectangleProgram`, `ContinuumCoulomb_Programs_RawCoulombSample`, `ContinuumCoulomb_Programs_RawCoulombSampleProgram`, `ContinuumCoulomb_Programs_RawDensitySample`, `ContinuumCoulomb_Programs_SquareRootProgram`, `ContinuumCoulomb_Programs_UnitCoulombProgram`, `CoulombRadii_Model`, `CoulombRadii_Packets_CoulombKernel`, `MeasureTheory_Function_LpSpace_Restrict`, `QuantumFactoring_BinaryRoots`, `QuantumFactoring_BitStackAdder`, `QuantumFactoring_BitStackBasicProcedures`, `QuantumFactoring_BitStackBinaryBasics`, `QuantumFactoring_BitStackBooleans`, `QuantumFactoring_BitStackChoice`, `QuantumFactoring_BitStackComposition`, `QuantumFactoring_BitStackConstants`, `QuantumFactoring_BitStackDivision`, `QuantumFactoring_BitStackFold`, `QuantumFactoring_BitStackFrames`, `QuantumFactoring_BitStackGCD`, `QuantumFactoring_BitStackIncrement`, `QuantumFactoring_BitStackIntegers`, `QuantumFactoring_BitStackIteration`, `QuantumFactoring_BitStackListCode`, `QuantumFactoring_BitStackListFold`, `QuantumFactoring_BitStackListLength`, `QuantumFactoring_BitStackLists`, `QuantumFactoring_BitStackMultiplier`, `QuantumFactoring_BitStackNaturals`, `QuantumFactoring_BitStackProcedures`, `QuantumFactoring_BitStackProducts`, `QuantumFactoring_BitStackPrograms`, `QuantumFactoring_BitStackQuotation`, `QuantumFactoring_BitStackRationalDivision`, `QuantumFactoring_BitStackRationals`, `QuantumFactoring_BitStackRelabel`, `QuantumFactoring_BitStackSubtractor`, `QuantumFactoring_BitStackSums`, `QuantumFactoring_BitStackUnary`, `QuantumFactoring_BitStackWords`, `QuantumFactoring_NativeAIGAddWrapper`, `QuantumFactoring_Procedure`, `QuantumFactoring_ProcedureFurther`.
--
--   **Imports.** It imports the published bundle `Def_ContinuumCoulombHardness`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ092A004`, `OAIQ092A005`, `OAIQ092A006`, `OAIQ092A007` and `OAIQ092A011`; the statements `OAI_ContinuumCoulomb_CoulombEvaluation_rawApproximate_bound`, `OAI_ContinuumCoulomb_CoulombNormalization_approximation_error` and `OAI_ContinuumCoulomb_NormalizationSchedule_approximation_error`; the proof of `RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small`.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_ContinuumCoulombHardness

section
-- module Solutions.OAIQ092_CC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
open scoped ContDiff in
/-- Backport (Mathlib d13f23b), with Mathlib's own proof: the iterated derivatives up to order `m` of a
smooth compactly supported function are uniformly bounded (Falconer all dimensions, oaiq-088: 3 modules;
OAIHecke carried its own copy). -/
theorem _root_.HasCompactSupport.exists_bound_iteratedFDeriv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} (hf : HasCompactSupport f) (hf' : ContDiff 𝕜 ∞ f) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C := by
  have key i : ∃ C, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C :=
    (hf'.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hf.iteratedFDeriv i)
  choose A hA using key
  refine ⟨max 0 ((Finset.range (m + 1)).sup' ⟨0, by simp⟩ A), le_max_left _ _, fun i hi y ↦ ?_⟩
  grw [hA i y, ← le_max_right]
  exact Finset.le_sup' A (by grind)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ092_CC.MeasureTheory_Function_LpSpace_Restrict
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
# `RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict`

`L^p` extension-by-zero maps for restricted measures.

Mathlib provides the equivalence

`MemLp (s.indicator f) p μ ↔ MemLp f p (μ.restrict s)`

(`MeasureTheory.memLp_indicator_iff_restrict`). This file packages the corresponding map on `Lp`
spaces:

`Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ`,

given by extension-by-zero (via `Set.indicator`).

## Main definitions

- `MeasureTheory.Lp.extendByZeroₗ`
- `MeasureTheory.Lp.extendByZeroₗᵢ`
-/

namespace MeasureTheory

open scoped ENNReal

namespace Lp

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {s : Set α} (hs : MeasurableSet s)

noncomputable def extendByZeroFun (f : Lp E p (μ.restrict s)) : Lp E p μ :=
  let hf : MemLp (fun x : α => f x) p (μ.restrict s) := Lp.memLp f
  let hfi : MemLp (s.indicator fun x : α => f x) p μ :=
    (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s) (f := fun x : α => f x) hs).2 hf
  hfi.toLp (s.indicator fun x : α => f x)

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
lemma extendByZeroFun_coe (f : Lp E p (μ.restrict s)) :
    extendByZeroFun (μ := μ) (p := p) (s := s) hs f =ᵐ[μ] s.indicator fun x : α => f x := by
  dsimp [extendByZeroFun]
  exact MemLp.coeFn_toLp _

/-- Extension-by-zero as a linear map `Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ`. -/
noncomputable def extendByZeroₗ : Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ where
  toFun := extendByZeroFun (μ := μ) (p := p) (s := s) hs
  map_add' f g := by
    classical
    -- Prove equality by comparing pointwise representatives.
    refine Lp.ext ?_
    have h_add_restrict :
        (fun x : α => (f + g) x) =ᵐ[μ.restrict s] fun x : α => f x + g x := by
      exact (Lp.coeFn_add (μ := μ.restrict s) f g)
    have h_add_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (f + g) x = f x + g x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_add_restrict
    filter_upwards
      [ extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (f + g)
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs g
      , coeFn_add (extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
          (extendByZeroFun (μ := μ) (p := p) (s := s) hs g)
      , h_add_on
      ] with x hfg hf hg hadd hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hadd' :
          extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using hadd.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = (f + g) x := by simp [Set.indicator_of_mem, hx]
        _ = f x + g x := hsum'
        _ = s.indicator (fun x : α => f x) x + s.indicator (fun x : α => g x) x := by
            simp [Set.indicator_of_mem, hx]
        _ = extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            simp [hf, hg]
        _ = (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
    ·
      have hadd' :
          extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using hadd.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            -- both summands are zero off `s`
            simp [Set.indicator_of_notMem, hx, hf, hg]
        _ = (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
  map_smul' c f := by
    classical
    refine Lp.ext ?_
    have h_smul_restrict :
        (fun x : α => (c • f) x) =ᵐ[μ.restrict s] fun x : α => c • f x := by
      exact (Lp.coeFn_smul (μ := μ.restrict s) c f)
    have h_smul_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (c • f) x = c • f x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_smul_restrict
    filter_upwards
      [ extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (c • f)
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , coeFn_smul c (extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
      , h_smul_on
      ] with x hcf hf hsmul hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hsmul' :
          c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using hsmul.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = (c • f) x := by simp [Set.indicator_of_mem, hx]
        _ = c • f x := hsum'
        _ = c • s.indicator (fun x : α => f x) x := by simp [Set.indicator_of_mem, hx]
        _ = c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by simp [hf]
        _ = (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := hsmul'
    ·
      have hsmul' :
          c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using hsmul.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
            have hf0 :
                extendByZeroFun (μ := μ) (p := p) (s := s) hs f x = 0 := by
              simpa [Set.indicator_of_notMem, hx] using hf
            have hcx :
                (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x = 0 := by
              calc
                (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x =
                    c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by
                      simpa [Pi.smul_apply] using hsmul
                _ = 0 := by simp [hf0]
            simpa using hcx.symm

/-- Extension-by-zero as a linear isometry. -/
noncomputable def extendByZeroₗᵢ : Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ where
  toLinearMap := extendByZeroₗ (μ := μ) (p := p) (s := s) hs
  norm_map' f := by
    classical
    -- Unfold into `MemLp.toLp` and reduce to `eLpNorm_indicator_eq_eLpNorm_restrict`.
    have hfi :
        MemLp (s.indicator fun x : α => f x) p μ :=
      (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs).2 (Lp.memLp f)
    -- Norm in the codomain is the `eLpNorm` of the indicator.
    have hnorm_out :
        ‖extendByZeroₗ (μ := μ) (p := p) (s := s) hs f‖ =
          ENNReal.toReal (eLpNorm (s.indicator fun x : α => f x) p μ) := by
      dsimp [extendByZeroₗ, extendByZeroFun]
      simp [norm_toLp (f := s.indicator (fun x : α => f x)) hfi]
    -- Rewrite the `eLpNorm` of the indicator as a restricted `eLpNorm`.
    have hnorm_restrict :
        eLpNorm (s.indicator fun x : α => f x) p μ =
          eLpNorm (fun x : α => f x) p (μ.restrict s) := by
      simpa using (eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs)
    -- Combine with the definition of the `Lp` norm on the restricted space.
    simp [hnorm_out, hnorm_restrict, norm_def]

lemma extendByZeroₗᵢ_ae_eq (f : Lp E p (μ.restrict s)) :
    ((extendByZeroₗᵢ (μ := μ) (p := p) (s := s) hs) f : α → E) =ᵐ[μ]
      s.indicator fun x : α => f x := by
  -- Unfold to the underlying `extendByZeroFun` and use the defining AE equality.
  simpa [extendByZeroₗᵢ, extendByZeroₗ] using
    (extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f)

end

end Lp

end MeasureTheory
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
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

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- `volume` is the canonical Haar measure on finite-dimensional real vector spaces.
local instance instMeasurableSpace_solutions_1 : MeasurableSpace E := borel E
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
-- module Solutions.OAIQ092_CC.CoulombRadii_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace NeutralAtom

abbrev Position := EuclideanSpace ℝ (Fin 3)

end NeutralAtom
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Packets_CoulombKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def coulombKernel (x : Position) : ℝ := ‖x‖⁻¹

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGroundTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The planar manufactured well's ground-state transform. Integration by
parts establishes positivity on actual compact C¹ test functions. Existence,
decay and the excitation gap of the specific resolvent-generated mode remain
separate analytic steps. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

abbrev PlanarPosition := EuclideanSpace ℝ (Fin 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's explicit planar forcing `(1-|r|²)₊¹⁶`, including finite
smoothness at its support boundary. The positive-part power is represented
by a polynomial plus a fractional power of a square, avoiding a nonsmooth
positive-part differentiation rule. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def positivePartSixteen (x : ℝ) : ℝ := max x 0 ^ 16

def planarForcing (r : PlanarPosition) : ℝ := positivePartSixteen (1 - ‖r‖ ^ 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized two-dimensional Gaussian heat kernel and its
convolution with the paper's explicit forcing. These prepare the positive
resolvent mode, rather than assuming the manufactured well exists. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarHeatKernel (t : ℝ) (r : PlanarPosition) : ℝ :=
  (4 * Real.pi * t)⁻¹ * Real.exp (-‖r‖ ^ 2 / (4 * t))

def planarHeatAverage (t : ℝ) (r : PlanarPosition) : ℝ :=
  ∫ b, planarHeatKernel t b * planarForcing (r - b)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the actual positive finite-smooth planar resolvent mode.
Tonelli/Fubini give an L¹ resolvent kernel of mass one, so convolution with
the manuscript's compact forcing has C⁷ regularity. The resolvent differential
equation, quantitative tails and excitation gap are subsequent steps. -/

noncomputable section
open MeasureTheory Function
open scoped Convolution
namespace ContinuumCoulomb

def planarResolventIntegrand (p : ℝ × PlanarPosition) : ℝ :=
  Real.exp (-p.1) * planarHeatKernel p.1 p.2

def planarResolventKernel (r : PlanarPosition) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), planarResolventIntegrand (t, r)

def planarResolventMode (r : PlanarPosition) : ℝ :=
  ∫ b, planarResolventKernel b * planarForcing (r - b)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity, finite L² normalization and compact support of the actual
manufactured planar potential. The differential eigen-equation and gap are
not assumed by these declarations. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def normalizedPlanarMode (r : PlanarPosition) : ℝ :=
  planarResolventMode r / Real.sqrt (∫ s, planarResolventMode s ^ 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarResolventEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential eigen-equation of the constructed resolvent mode is
obtained from its heat representation and the fundamental theorem of calculus,
not supplied as an assumption. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

def planarHeatResolventPrimitive (r : PlanarPosition) (t : ℝ) : ℝ :=
  if t = 0 then planarForcing r else Real.exp (-t) * planarHeatAverage t r

@[simp] theorem planarHeatResolventPrimitive_zero (r : PlanarPosition) :
    planarHeatResolventPrimitive r 0 = planarForcing r := by
  simp [planarHeatResolventPrimitive]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized Gaussian in the transverse direction. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

def verticalMode (freq z : ℝ) : ℝ :=
  Real.exp (-freq * z ^ 2 / 2) / Real.sqrt (Real.sqrt (Real.pi / freq))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual localized modes in planar/transverse coordinates. The measure is
the product of planar Euclidean volume and one-dimensional Lebesgue measure.
The split Laplacian below is the sum of the three coordinate derivatives. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

abbrev SplitPosition := PlanarPosition × ℝ

def localizedMode (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) : ℝ :=
  normalizedPlanarMode (p.1 - u) * verticalMode freq p.2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Volume-preserving planar/transverse coordinates for the actual
three-dimensional Coulomb space. The intermediate product has its Euclidean
L² norm; the final ordinary product carries the same product volume. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def verticalCoordinateEquiv : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ where
  __ := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toLinearEquiv
  norm_map' := by
    intro x
    change ‖x 0‖ = ‖x‖
    simp [PiLp.norm_eq_of_L2, Real.sqrt_sq_eq_abs]

def positionSplitIsometry : Position ≃ₗᵢ[ℝ] WithLp 2 SplitPosition :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((finSumFinEquiv (m := 2) (n := 1)).symm)).trans
    ((PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ => ℝ)).trans
      (LinearIsometryEquiv.withLpProdCongr 2
        (LinearIsometryEquiv.refl ℝ PlanarPosition) verticalCoordinateEquiv))

def positionSplitCoordinates : Position ≃L[ℝ] SplitPosition :=
  positionSplitIsometry.toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ PlanarPosition ℝ)

def continuumLocalizedMode (freq : ℝ) (u : PlanarPosition) (x : Position) : ℝ :=
  localizedMode freq u (positionSplitCoordinates x)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulomb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite actual Coulomb interactions of the localized densities. Bounded
probability densities permit the existing elementary near/far Coulomb bound;
no interaction coefficient is introduced as a spectral input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedAmplitudeBound (freq : ℝ) : ℝ :=
  (1 / Real.sqrt (∫ r, planarResolventMode r ^ 2)) *
    (1 / Real.sqrt (Real.sqrt (Real.pi / freq)))

def localizedDensity (freq : ℝ) (u : PlanarPosition) (x : Position) : ℝ :=
  continuumLocalizedMode freq u x ^ 2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

/-! A literal finite Boolean-stack compiler for circuit descriptions.
Branches inspect and consume one symbol, not an entire encoded word.
Operational derivations below count actual finite-state TM2 transitions.
-/
namespace ExactQuantumFactoring.BitStackProgram
open Turing.TM2 StateTransition

inductive Program (K : Type) where
  | skip
  | push (k : K) (b : Bool)
  | seq (p q : Program K)
  | cases (k : K) (nil ff tt : Program K)
  | loop (k : K) (ff tt : Program K)

abbrev Store (K : Type) := K → List Bool

inductive Runs {K : Type} [DecidableEq K] : Program K → Store K → Store K → ℕ → Prop
  | skip (s) : Runs .skip s s 1
  | push (s) (k) (b) : Runs (.push k b) s (Function.update s k (b :: s k)) 1
  | seq {p q s t u a b} : Runs p s t a → Runs q t u b → Runs (.seq p q) s u (b+a)
  | cases_nil {k p q r s t a} : s k=[] → Runs p s t a → Runs (.cases k p q r) s t (a+1)
  | cases_false {k p q r s t xs a} : s k=false::xs →
      Runs q (Function.update s k xs) t a → Runs (.cases k p q r) s t (a+1)
  | cases_true {k p q r s t xs a} : s k=true::xs →
      Runs r (Function.update s k xs) t a → Runs (.cases k p q r) s t (a+1)
  | loop_nil {k p q s} : s k=[] → Runs (.loop k p q) s s 1
  | loop_false {k p q s t u xs a b} : s k=false::xs →
      Runs p (Function.update s k xs) t a → Runs (.loop k p q) t u b →
      Runs (.loop k p q) s u (b+a+1)
  | loop_true {k p q s t u xs a b} : s k=true::xs →
      Runs q (Function.update s k xs) t a → Runs (.loop k p q) t u b →
      Runs (.loop k p q) s u (b+a+1)

def singletonStore {K : Type} [DecidableEq K] (k : K) (v : List Bool) : Store K :=
  Function.update (fun _ => []) k v

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]

/-- Reverse one stack onto another, preserving all symbols. -/
def reverseMove (a b : K) : Program K := .loop a (.push b false) (.push b true)
def clear (a : K) : Program K := .loop a .skip .skip

def duplicateReverse (a b t : K) : Program K :=
  .seq (.loop a (.seq (.push b false) (.push t false))
    (.seq (.push b true) (.push t true))) (reverseMove t a)

lemma clear_runs (a : K) (s : Store K) :
    Runs (clear a) s (Function.update s a []) (2*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update s a []=s := by rw [←hs,Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    have ht : Function.update s a xs a=xs := by simp
    have hh := ih (Function.update s a xs) ht
    cases x
    · have hr := Runs.loop_false hs (Runs.skip (Function.update s a xs)) hh
      convert hr using 1 <;> first | rfl | simp only [Function.update_idem]
    · have hr := Runs.loop_true hs (Runs.skip (Function.update s a xs)) hh
      convert hr using 1 <;> first | rfl | simp only [Function.update_idem]

lemma reverseMove_runs (a b : K) (hab : a≠b) (s : Store K) :
    Runs (reverseMove a b) s
      (Function.update (Function.update s a []) b ((s a).reverse++s b))
      (2*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update (Function.update s a []) b ([].reverse++s b)=s := by
      rw [List.reverse_nil,List.nil_append,←hs,Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    let t := Function.update s a xs
    let u := Function.update t b (x::t b)
    have hua : u a=xs := by simp [u,t,hab]
    have htail := ih u hua
    have body : Runs (.push b x) t u 1 := Runs.push _ _ _
    have hr : Runs (reverseMove a b) s
        (Function.update (Function.update u a []) b (xs.reverse++u b)) (2*xs.length+1+1+1) := by
      cases x
      · exact Runs.loop_false (a:=1) (b:=2*xs.length+1) hs body htail
      · exact Runs.loop_true (a:=1) (b:=2*xs.length+1) hs body htail
    convert hr using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;>
      simp_all [u,t,Function.update,List.reverse_cons,List.append_assoc]

lemma duplicateReverse_loop_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : Store K) :
    Runs (.loop a (.seq (.push b false) (.push t false))
      (.seq (.push b true) (.push t true))) s
      (Function.update (Function.update (Function.update s a []) b ((s a).reverse++s b))
        t ((s a).reverse++s t)) (3*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update (Function.update (Function.update s a []) b ([].reverse++s b))
        t ([].reverse++s t)=s := by
      rw [List.reverse_nil,List.nil_append,List.nil_append,←hs,Function.update_eq_self,
        Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    let u := Function.update s a xs
    let w := Function.update u b (x::u b)
    let v := Function.update w t (x::w t)
    have hva : v a=xs := by simp [v,w,u,hab,hat]
    have htail := ih v hva
    have body : Runs (.seq (.push b x) (.push t x)) u v 2 :=
      Runs.seq (Runs.push _ _ _) (Runs.push _ _ _)
    have hr : Runs (.loop a (.seq (.push b false) (.push t false))
      (.seq (.push b true) (.push t true))) s
      (Function.update (Function.update (Function.update v a []) b (xs.reverse++v b))
        t (xs.reverse++v t)) (3*xs.length+1+2+1) := by
      cases x
      · exact Runs.loop_false (a:=2) (b:=3*xs.length+1) hs body htail
      · exact Runs.loop_true (a:=2) (b:=3*xs.length+1) hs body htail
    convert hr using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht : k=t <;>
      simp_all [v,w,u,Function.update,List.reverse_cons,List.append_assoc]

lemma duplicateReverse_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : Store K) (ht : s t=[]) :
    Runs (duplicateReverse a b t) s (Function.update s b ((s a).reverse++s b))
      (5*(s a).length+2) := by
  let v := Function.update (Function.update (Function.update s a []) b ((s a).reverse++s b))
    t ((s a).reverse++s t)
  have hr := reverseMove_runs t a hat.symm v
  have hh := Runs.seq (duplicateReverse_loop_runs a b t hab hat hbt s) hr
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht' : k=t <;>
      simp_all [v,Function.update]
  · simp only [v,Function.update_self,ht,List.append_nil,List.length_reverse]; omega

end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackProcedures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]

lemma Runs.length_le {p : Program K} {s t : Store K} {c : ℕ} (h : Runs p s t c) (k : K) :
    (t k).length ≤ (s k).length+c := by
  induction h with
  | skip s => omega
  | push s a b =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self,List.length_cons]; omega
    · simp only [Function.update_of_ne hk]; omega
  | seq hp hq ip iq => omega
  | cases_nil hs hr ih => omega
  | @cases_false a p q r s t xs c hs hr ih =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ih; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ih; omega
  | @cases_true a p q r s t xs c hs hr ih =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ih; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ih; omega
  | loop_nil hs => omega
  | @loop_false a p q s t u xs c d hs hp hq ip iq =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ip; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ip; omega
  | @loop_true a p q s t u xs c d hs hp hq ip iq =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ip; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ip; omega

/-- A completely explicit finite-state Boolean-stack subroutine, with the
same clean input/output convention as the frozen TM2 uniformity target. -/
structure Procedure {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  K : Type
  finiteK : Fintype K
  decideK : DecidableEq K
  input : K
  output : K
  program : Program K
  bound : Polynomial ℕ
  runs : ∀ a, ∃ c, c ≤ bound.eval (ea a).length ∧
    @Runs K decideK program (@singletonStore K decideK input (ea a)) (@singletonStore K decideK output (eb (f a))) c

attribute [instance] Procedure.finiteK Procedure.decideK
namespace Procedure
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

lemma output_length_le (p : Procedure ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length+p.bound.eval (ea a).length := by
  obtain ⟨c,hc,hr⟩ := p.runs a
  have h := hr.length_le p.output
  simp only [singletonStore,Function.update_self] at h
  by_cases he : p.output=p.input
  · simp only [he,Function.update_self] at h; omega
  · simp only [Function.update_of_ne he,List.length_nil,Nat.zero_add] at h; omega

end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

variable {K L : Type}
def Program.relabel (f : K → L) : Program K → Program L
  | .skip => .skip
  | .push k b => .push (f k) b
  | .seq p q => .seq (p.relabel f) (q.relabel f)
  | .cases k p q r => .cases (f k) (p.relabel f) (q.relabel f) (r.relabel f)
  | .loop k p q => .loop (f k) (p.relabel f) (q.relabel f)

/-- An extension of a small register store with arbitrary untouched registers. -/
noncomputable def overlay (f : K ↪ L) (base : Store L) (s : Store K) : Store L := by
  classical
  exact fun j => if h : ∃ i, f i=j then s (Classical.choose h) else base j

lemma overlay_at (f : K ↪ L) (base : Store L) (s : Store K) (i : K) :
    overlay f base s (f i)=s i := by
  classical
  unfold overlay
  rw [dite_eq_left ⟨i,rfl⟩]
  congr 1
  apply f.injective
  exact Classical.choose_spec (show ∃ k, f k=f i from ⟨i,rfl⟩)

lemma overlay_outside (f : K ↪ L) (base : Store L) (s : Store K) (j : L)
    (h : ∀ i, f i≠j) : overlay f base s j=base j := by
  classical
  unfold overlay
  exact dite_eq_right (by simpa only [not_exists] using h)

variable [DecidableEq K] [DecidableEq L]

lemma overlay_update (f : K ↪ L) (base : Store L) (s : Store K) (k : K) (xs : List Bool) :
    overlay f base (Function.update s k xs)=Function.update (overlay f base s) (f k) xs := by
  funext j
  by_cases hj : ∃ i,f i=j
  · rcases hj with ⟨i,rfl⟩
    rw [overlay_at]
    by_cases h : i=k
    · subst i; simp
    · have hf : f i≠f k := fun h' => h (f.injective h')
      simp only [Function.update_of_ne h,Function.update_of_ne hf,overlay_at]
  · have h : ∀ i,f i≠j := by simpa only [not_exists] using hj
    rw [overlay_outside f base _ j h,Function.update_of_ne (Ne.symm (h k)),
      overlay_outside f base s j h]

/-- Exact-cost subroutine embedding. Scratch separation is proved, not assumed
as an extra TM operation. -/
lemma Runs.relabel {p : Program K} {s t : Store K} {c : ℕ}
    (h : Runs p s t c) (f : K ↪ L) (base : Store L) :
    Runs (p.relabel f) (overlay f base s) (overlay f base t) c := by
  induction h with
  | skip s => exact Runs.skip _
  | push s k b =>
    rw [overlay_update]
    simpa only [overlay_at, Program.relabel] using Runs.push (overlay f base s) (f k) b
  | seq hp hq ip iq => exact Runs.seq ip iq
  | @cases_nil k p q r s t a hs hr ih =>
    exact Runs.cases_nil (by rw [overlay_at,hs]) ih
  | @cases_false k p q r s t xs a hs hr ih =>
    rw [overlay_update] at ih
    exact Runs.cases_false (by rw [overlay_at,hs]) ih
  | @cases_true k p q r s t xs a hs hr ih =>
    rw [overlay_update] at ih
    exact Runs.cases_true (by rw [overlay_at,hs]) ih
  | @loop_nil k p q s hs => exact Runs.loop_nil (by rw [overlay_at,hs])
  | @loop_false k p q s t u xs a b hs hp hq ip iq =>
    rw [overlay_update] at ip
    exact Runs.loop_false (by rw [overlay_at,hs]) ip iq
  | @loop_true k p q s t u xs a b hs hp hq ip iq =>
    rw [overlay_update] at ip
    exact Runs.loop_true (by rw [overlay_at,hs]) ip iq
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K L : Type} [DecidableEq K] [DecidableEq L]

omit [DecidableEq K] [DecidableEq L] in
lemma overlay_empty (f : K ↪ L) : overlay f (fun _=>[]) (fun _=>[])=fun _=>[] := by
  funext j
  by_cases h : ∃ i,f i=j
  · rcases h with ⟨i,rfl⟩; exact overlay_at f _ _ i
  · exact overlay_outside f _ _ j (by simpa only [not_exists] using h)
lemma overlay_singleton (f : K ↪ L) (k : K) (xs : List Bool) :
    overlay f (fun _=>[]) (singletonStore k xs)=singletonStore (f k) xs := by
  rw [singletonStore,overlay_update,overlay_empty]
  rfl

/-- Move an entire word without reversing its order. Each symbol is pushed
and popped twice; this is not an atomic bulk-copy instruction. -/
def moveWord (a b t : K) : Program K := .seq (reverseMove a t) (reverseMove t b)
lemma moveWord_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t) (xs : List Bool) :
    Runs (moveWord a b t) (singletonStore a xs) (singletonStore b xs) (4*xs.length+2) := by
  let s := singletonStore a xs
  let u := Function.update (Function.update s a []) t ((s a).reverse++s t)
  have hh := Runs.seq (reverseMove_runs a t hat s) (reverseMove_runs t b hbt.symm u)
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht : k=t <;>
      simp_all [u,s,singletonStore,Function.update,Ne.symm hat,Ne.symm hab,Ne.symm hbt]
  · simp only [u,Function.update_self,s,singletonStore,Function.update_self]
    simp only [Function.update_of_ne hat.symm,List.append_nil,List.length_reverse]
    omega

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
  {f : α→β} {g : β→γ}

def joinLeft (A B : Type) : A ↪ A ⊕ (B ⊕ Unit) := ⟨Sum.inl,Sum.inl_injective⟩
def joinRight (A B : Type) : B ↪ A ⊕ (B ⊕ Unit) :=
  ⟨Sum.inr ∘ Sum.inl,Sum.inr_injective.comp Sum.inl_injective⟩

lemma eval_nat_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  change p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

/-- Checked composition for actual finite Boolean-stack procedures. This
constructs the combined program and accounts for the intermediate-word copy;
it does NOT invoke Mathlib's unproved TM2 polytime-composition declaration. -/
noncomputable def comp (q : Procedure eb ec g) (p : Procedure ea eb f) :
    Procedure ea ec (g ∘ f) where
  K := p.K ⊕ (q.K ⊕ Unit)
  finiteK := inferInstance
  decideK := inferInstance
  input := Sum.inl p.input
  output := Sum.inr (Sum.inl q.output)
  program := .seq (p.program.relabel (joinLeft p.K q.K))
    (.seq (moveWord (Sum.inl p.output) (Sum.inr (Sum.inl q.input)) (Sum.inr (Sum.inr ())))
      (q.program.relabel (joinRight p.K q.K)))
  bound := p.bound+(Polynomial.C 4*(Polynomial.X+p.bound)+Polynomial.C 2)+
    q.bound.comp (Polynomial.X+p.bound)
  runs a := by
    obtain ⟨cp,hcp,hp⟩ := p.runs a
    obtain ⟨cq,hcq,hq⟩ := q.runs (f a)
    have hleft := hp.relabel (joinLeft p.K q.K) (fun _=>[])
    have hright := hq.relabel (joinRight p.K q.K) (fun _=>[])
    simp only [overlay_singleton] at hleft hright
    have hmove := moveWord_runs (K:=p.K ⊕ (q.K ⊕ Unit)) (Sum.inl p.output)
      (Sum.inr (Sum.inl q.input)) (Sum.inr (Sum.inr ()))
      (by simp) (by simp) (by simp) (eb (f a))
    refine ⟨cq+(4*(eb (f a)).length+2)+cp,?_,Runs.seq hleft (Runs.seq hmove hright)⟩
    have hlen := p.output_length_le a
    have hmono := eval_nat_mono q.bound hlen
    dsimp only at hmono
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_comp]
    omega
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K L : Type}
def sumStore (s : Store K) (t : Store L) : Store (K ⊕ L) := Sum.elim s t
@[simp] lemma sumStore_left (s : Store K) (t : Store L) (k : K) :
    sumStore s t (Sum.inl k)=s k := rfl
@[simp] lemma sumStore_right (s : Store K) (t : Store L) (l : L) :
    sumStore s t (Sum.inr l)=t l := rfl
lemma sumStore_empty : sumStore (fun _ : K=>[]) (fun _ : L=>[])=fun _=>[] := by
  funext j; cases j <;> rfl

def leftEmbed (K L : Type) : K ↪ K ⊕ L := ⟨Sum.inl,Sum.inl_injective⟩
lemma overlay_left (s : Store K) (t : Store L) :
    overlay (leftEmbed K L) (sumStore (fun _=>[]) t) s=sumStore s t := by
  funext j
  cases j with
  | inl j => exact overlay_at _ _ _ j
  | inr j => exact overlay_outside _ _ _ _ (by intro i; simp [leftEmbed])

variable [DecidableEq K] [DecidableEq L]
@[simp] lemma sumStore_update_left (s : Store K) (t : Store L) (k : K) (xs : List Bool) :
    Function.update (sumStore s t) (Sum.inl k) xs=sumStore (Function.update s k xs) t := by
  funext j; cases j <;> simp [Function.update,sumStore]
@[simp] lemma sumStore_update_right (s : Store K) (t : Store L) (k : L) (xs : List Bool) :
    Function.update (sumStore s t) (Sum.inr k) xs=sumStore s (Function.update t k xs) := by
  funext j; cases j <;> simp [Function.update,sumStore]
lemma sumStore_singleton_left (k : K) (xs : List Bool) :
    singletonStore (Sum.inl k) xs=sumStore (singletonStore k xs) (fun _ : L=>[]) := by
  rw [singletonStore,←sumStore_empty,sumStore_update_left]; rfl
lemma Runs.left {p : Program K} {s u : Store K} {c : ℕ} (h : Runs p s u c) (t : Store L) :
    Runs (p.relabel Sum.inl) (sumStore s t) (sumStore u t) c := by
  have hh := h.relabel (leftEmbed K L) (sumStore (fun _=>[]) t)
  rw [overlay_left,overlay_left] at hh
  exact hh

namespace Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {f g : α→β}
def congrFun (p : Procedure ea eb f) (h : ∀ a,f a=g a) : Procedure ea eb g where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [h a] using p.runs a

noncomputable def identity (ea : α→List Bool) : Procedure ea ea id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.skip
  bound:=1
  runs a:=⟨1,by simp,Runs.skip _⟩
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackQuotation
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_right _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

/-- Prefix-free quoting for one Boolean word. Both constructor tags and payload
bits are literal stack symbols. It is used only by the classical generator. -/
def quoteBits (xs : List Bool) : List Bool :=
  xs.flatMap (fun b=>[true,b]) ++ [false]
@[simp] lemma quoteBits_nil : quoteBits []=[false] := rfl
@[simp] lemma quoteBits_cons (b : Bool) (xs : List Bool) :
    quoteBits (b::xs)=true::b::quoteBits xs := rfl
lemma quoteBits_length (xs : List Bool) : (quoteBits xs).length=2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [quoteBits_cons,List.length_cons,ih]; omega

def pairBits (xs ys : List Bool) : List Bool := quoteBits xs++ys
lemma pairBits_length (xs ys : List Bool) :
    (pairBits xs ys).length=2*xs.length+ys.length+1 := by
  simp only [pairBits,List.length_append,quoteBits_length]; omega

variable {K : Type} [DecidableEq K]
def quoteLoop (a t : K) : Program K :=
  .loop a (.seq (.push t true) (.push t false)) (.seq (.push t true) (.push t true))
def quoteMove (a b t : K) : Program K :=
  .seq (quoteLoop a t) (.seq (.push t false) (reverseMove t b))

lemma quoteLoop_runs (a t : K) (hat : a≠t) (s : Store K) :
    Runs (quoteLoop a t) s
      (Function.update (Function.update s a []) t
        (((s a).flatMap (fun b=>[true,b])).reverse++s t)) (3*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have h : Function.update (Function.update s a []) t
        (([].flatMap (fun b=>[true,b])).reverse++s t)=s := by
      simp only [List.flatMap_nil,List.reverse_nil,List.nil_append]
      rw [←hs,Function.update_eq_self,Function.update_eq_self]
    rw [h]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    let u := Function.update s a xs
    let v := Function.update u t (x::true::u t)
    have hva : v a=xs := by simp [v,u,hat]
    have hb : Runs (.seq (.push t true) (.push t x)) u v 2 := by
      have hh := Runs.seq (Runs.push u t true)
        (Runs.push (Function.update u t (true::u t)) t x)
      simpa only [Function.update_self,Function.update_idem] using hh
    have hh : Runs (quoteLoop a t) s
        (Function.update (Function.update v a []) t
          ((xs.flatMap (fun b=>[true,b])).reverse++v t)) (3*xs.length+1+2+1) := by
      cases x
      · exact Runs.loop_false (a:=2) (b:=3*xs.length+1) hs hb (ih v hva)
      · exact Runs.loop_true (a:=2) (b:=3*xs.length+1) hs hb (ih v hva)
    convert hh using 1 <;> try (simp only [List.length_cons, List.length_nil] <;> omega)
    · funext k
      by_cases ha : k=a <;> by_cases ht : k=t <;>
        simp_all [v,u,Function.update,List.reverse_cons,List.append_assoc]

lemma quoteMove_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : Store K) (ht : s t=[]) :
    Runs (quoteMove a b t) s
      (Function.update (Function.update s a []) b (quoteBits (s a)++s b))
      (7*(s a).length+5) := by
  let u := Function.update (Function.update s a []) t
    (((s a).flatMap (fun b=>[true,b])).reverse++s t)
  let v := Function.update u t (false::u t)
  have hh := Runs.seq (quoteLoop_runs a t hat s)
    (Runs.seq (Runs.push u t false) (reverseMove_runs t b hbt.symm v))
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht' : k=t <;>
      simp_all [u,v,Function.update,quoteBits,Ne.symm hat,Ne.symm hab,Ne.symm hbt]
  · simp only [v,Function.update_self,u,Function.update_self,ht,List.append_nil,
      List.length_cons,List.length_reverse]
    have hl : ((s a).flatMap (fun b=>[true,b])).length=2*(s a).length := by
      have h:=quoteBits_length (s a)
      simp only [quoteBits,List.length_append,List.length_cons,List.length_nil] at h
      omega
    rw [hl]; omega

def unquoteBody (a t c : K) : Program K :=
  .cases a .skip .skip
    (.cases a .skip (.seq (.push t false) (.push c true))
      (.seq (.push t true) (.push c true)))
def unquoteLoop (a t c : K) : Program K :=
  .loop c (unquoteBody a t c) (unquoteBody a t c)
def unquoteMove (a b t c : K) : Program K :=
  .seq (.push c true) (.seq (unquoteLoop a t c) (reverseMove t b))

lemma unquoteLoop_runs (a t c : K) (hat : a≠t) (hac : a≠c) (htc : t≠c)
    (xs ys : List Bool) (s : Store K) (ha : s a=quoteBits xs++ys) (hc : s c=[true]) :
    Runs (unquoteLoop a t c) s
      (Function.update (Function.update (Function.update s a ys) c []) t (xs.reverse++s t))
      (5*xs.length+4) := by
  induction xs generalizing s with
  | nil =>
    let u := Function.update s c []
    let v := Function.update u a ys
    have hua : u a=false::ys := by simp [u,hac,ha]
    have hvc : v c=[] := by simp [v,u,hac.symm]
    have hb : Runs (unquoteBody a t c) u v 2 := Runs.cases_false hua (Runs.skip v)
    have hh := Runs.loop_true (p:=unquoteBody a t c) hc hb (Runs.loop_nil hvc)
    change Runs (.loop _ _ _) _ _ _
    convert hh using 1 <;> try (simp only [List.length_cons, List.length_nil] <;> omega)
    · funext k
      by_cases ha' : k=a <;> by_cases hc' : k=c <;> by_cases ht' : k=t <;>
        simp_all [v,u,Function.update,Ne.symm hat,Ne.symm hac,Ne.symm htc]
  | cons x xs ih =>
    let u := Function.update s c []
    let v := Function.update u a (x::quoteBits xs++ys)
    let w := Function.update v a (quoteBits xs++ys)
    let z := Function.update (Function.update w t (x::w t)) c [true]
    have hua : u a=true::x::quoteBits xs++ys := by simp [u,hac,ha]
    have hva : v a=x::quoteBits xs++ys := by simp [v]
    have hzc : z c=[true] := by simp [z]
    have hza : z a=quoteBits xs++ys := by simp [z,w,v,hat,hac]
    have hb : Runs (unquoteBody a t c) u z 4 := by
      apply Runs.cases_true hua
      have hh := Runs.seq (Runs.push w t x)
        (Runs.push (Function.update w t (x::w t)) c true)
      have hc0 : Function.update w t (x::w t) c=[] := by simp [w,v,u,htc.symm,hac.symm]
      rw [hc0] at hh
      cases x
      · exact Runs.cases_false hva hh
      · exact Runs.cases_true hva hh
    have hh := Runs.loop_true hc hb (ih z hza hzc)
    change Runs (.loop _ _ _) _ _ _
    convert hh using 1 <;> try (simp only [List.length_cons, List.length_nil] <;> omega)
    · funext k
      by_cases ha' : k=a <;> by_cases hc' : k=c <;> by_cases ht' : k=t <;>
        simp_all [z,w,v,u,Function.update,Ne.symm hat,Ne.symm hac,Ne.symm htc,
          List.reverse_cons,List.append_assoc]

lemma unquoteMove_runs (a b t c : K) (hab : a≠b) (hat : a≠t) (hac : a≠c)
    (hbt : b≠t) (hbc : b≠c) (htc : t≠c)
    (xs ys : List Bool) (s : Store K) (ha : s a=quoteBits xs++ys)
    (ht : s t=[]) (hc : s c=[]) :
    Runs (unquoteMove a b t c) s
      (Function.update (Function.update s a ys) b (xs++s b)) (7*xs.length+6) := by
  let u := Function.update s c [true]
  let v := Function.update (Function.update (Function.update u a ys) c []) t (xs.reverse++u t)
  have hua : u a=quoteBits xs++ys := by simp [u,hac,ha]
  have huc : u c=[true] := by simp [u]
  have hp : Runs (.push c true) s u 1 := by simpa only [hc] using Runs.push s c true
  have hh := Runs.seq hp (Runs.seq (unquoteLoop_runs a t c hat hac htc xs ys u hua huc)
    (reverseMove_runs t b hbt.symm v))
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha' : k=a <;> by_cases hb' : k=b <;> by_cases ht' : k=t <;> by_cases hc' : k=c <;>
      simp_all [v,u,Function.update,Ne.symm hab,Ne.symm hat,Ne.symm hac,Ne.symm hbt,
        Ne.symm hbc,Ne.symm htc]
  · simp only [v,Function.update_self,u,Function.update_of_ne htc,ht,List.append_nil,
      List.length_reverse]; omega
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def prodCode {α β : Type} (ea : α→List Bool) (eb : β→List Bool) (x : α×β) : List Bool :=
  pairBits (ea x.1) (eb x.2)

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool} {f : α→β}

/-- Run a procedure on the first component, keeping the second component
literally on a disjoint stack. Parsing and re-quoting are explicitly charged. -/
noncomputable def left (p : Procedure ea eb f) (ec : γ→List Bool) :
    Procedure (prodCode ea ec) (prodCode eb ec) (fun x=>(f x.1,x.2)) where
  K:=p.K ⊕ Fin 3
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.seq (unquoteMove (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1) (Sum.inr 2))
    (.seq (p.program.relabel Sum.inl)
      (quoteMove (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound:=Polynomial.C 14*Polynomial.X+Polynomial.C 8*p.bound+Polynomial.C 11
  runs x:=by
    obtain ⟨cp,hcp,hp⟩:=p.runs x.1
    let s : Store (p.K ⊕ Fin 3):=singletonStore (Sum.inr 0) (prodCode ea ec x)
    let u : Store (p.K ⊕ Fin 3):=sumStore (singletonStore p.input (ea x.1))
      (singletonStore 0 (ec x.2))
    let v : Store (p.K ⊕ Fin 3):=sumStore (singletonStore p.output (eb (f x.1)))
      (singletonStore 0 (ec x.2))
    have hparse : Runs (unquoteMove (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1) (Sum.inr 2))
        s u (7*(ea x.1).length+6) := by
      have hh:=unquoteMove_runs (Sum.inr 0 : p.K ⊕ Fin 3) (Sum.inl p.input)
        (Sum.inr 1) (Sum.inr 2) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (ea x.1) (ec x.2) s (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      funext k
      cases k with
      | inl k => by_cases hk : k=p.input <;> simp_all [s,u,singletonStore,sumStore,Function.update]
      | inr k => fin_cases k <;> simp [s,u,singletonStore,sumStore,Function.update]
    have hcall : Runs (p.program.relabel Sum.inl) u v cp := hp.left (singletonStore (0 : Fin 3) (ec x.2))
    have hquote : Runs (quoteMove (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)) v
        (singletonStore (Sum.inr 0) (pairBits (eb (f x.1)) (ec x.2)))
        (7*(eb (f x.1)).length+5) := by
      have hh:=quoteMove_runs (Sum.inl p.output : p.K ⊕ Fin 3)
        (Sum.inr 0) (Sum.inr 1) (by simp) (by simp) (by simp) v (by simp [v,singletonStore])
      convert hh using 1
      · funext k
        cases k with
        | inl k => by_cases hk : k=p.output <;>
            simp_all [v,singletonStore,sumStore,Function.update]
        | inr k => fin_cases k <;> simp [v,singletonStore,sumStore,Function.update,pairBits]
      · simp [v,singletonStore]
    refine ⟨(7*(eb (f x.1)).length+5)+cp+(7*(ea x.1).length+6),?_,
      Runs.seq hparse (Runs.seq hcall hquote)⟩
    have hlen:=p.output_length_le x.1
    have hx : (ea x.1).length≤(prodCode ea ec x).length := by
      simp only [prodCode,pairBits_length]; omega
    have hm:=eval_nat_mono p.bound hx
    dsimp only at hm
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

/-- Exchange two quoted word fields, without a unit-cost tuple operation. -/
noncomputable def swap (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) (prodCode eb ea) Prod.swap where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=.seq (unquoteMove 0 1 2 3) (quoteMove 0 1 2)
  bound:=Polynomial.C 7*Polynomial.X+Polynomial.C 11
  runs x:=by
    let s : Store (Fin 4):=singletonStore 0 (prodCode ea eb x)
    let u : Store (Fin 4):=Function.update (singletonStore 0 (eb x.2)) 1 (ea x.1)
    have h1 : Runs (unquoteMove 0 1 2 3) s u (7*(ea x.1).length+6) := by
      have hh:=unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (ea x.1) (eb x.2) s
        (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      funext k; fin_cases k <;> simp [s,u,singletonStore,Function.update]
    have h2 : Runs (quoteMove 0 1 2) u (singletonStore 1 (prodCode eb ea x.swap))
        (7*(eb x.2).length+5) := by
      have hh:=quoteMove_runs (0 : Fin 4) 1 2 (by decide) (by decide) (by decide) u
        (by simp [u,singletonStore])
      convert hh using 1
      · funext k; fin_cases k <;> simp [u,singletonStore,Function.update,prodCode,pairBits]
      · simp [u,singletonStore]
    refine ⟨(7*(eb x.2).length+5)+(7*(ea x.1).length+6),?_,Runs.seq h1 h2⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length]
    omega

/-- Two arbitrary already verified subroutines acting independently on a pair. -/
noncomputable def parallel {δ : Type} {ed : δ→List Bool} {g : γ→δ}
    (p : Procedure ea eb f) (q : Procedure ec ed g) :
    Procedure (prodCode ea ec) (prodCode eb ed) (fun x=>(f x.1,g x.2)) :=
  (((swap ed eb).comp ((q.left eb).comp ((swap eb ec).comp (p.left ec)))).congrFun
    (by intro x; rfl))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackBasicProcedures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
  {f : α→β} {g : α→γ}

/-- Duplicate the input word and quote the first copy to represent a pair. -/
noncomputable def duplicate (ea : α→List Bool) :
    Procedure ea (prodCode ea ea) (fun a=>(a,a)) where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=3
  program:=.seq (duplicateReverse 0 1 2) (.seq (reverseMove 1 3) (quoteMove 0 3 1))
  bound:=Polynomial.C 14*Polynomial.X+Polynomial.C 8
  runs a:=by
    let s : Store (Fin 4):=singletonStore 0 (ea a)
    let u : Store (Fin 4):=Function.update s 1 (ea a).reverse
    let v : Store (Fin 4):=Function.update s 3 (ea a)
    have h1 : Runs (duplicateReverse 0 1 2) s u (5*(ea a).length+2) := by
      have hh:=duplicateReverse_runs (0 : Fin 4) 1 2 (by decide) (by decide) (by decide)
        s (by simp [s,singletonStore])
      simpa only [u,s,singletonStore,Function.update_self,
        Function.update_of_ne (by decide : (1 : Fin 4)≠0),List.append_nil] using hh
    have h2 : Runs (reverseMove 1 3) u v (2*(ea a).length+1) := by
      have hh:=reverseMove_runs (1 : Fin 4) 3 (by decide) u
      convert hh using 1
      · funext k; fin_cases k <;> simp [u,v,s,singletonStore,Function.update]
      · simp [u]
    have h3 : Runs (quoteMove 0 3 1) v
        (singletonStore 3 (prodCode ea ea (a,a))) (7*(ea a).length+5) := by
      have hh:=quoteMove_runs (0 : Fin 4) 3 1 (by decide) (by decide) (by decide) v
        (by simp [v,s,singletonStore])
      convert hh using 1
      · funext k; fin_cases k <;> simp [v,s,singletonStore,Function.update,prodCode,pairBits]
      · simp [v,s,singletonStore]
    refine ⟨(7*(ea a).length+5)+(2*(ea a).length+1)+(5*(ea a).length+2),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

noncomputable def pair (p : Procedure ea eb f) (q : Procedure ea ec g) :
    Procedure ea (prodCode eb ec) (fun a=>(f a,g a)) :=
  (p.parallel q).comp (duplicate ea)

/-- Projection parses the actual prefix code and explicitly clears its tail. -/
noncomputable def first (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) ea Prod.fst where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=.seq (unquoteMove 0 1 2 3) (clear 0)
  bound:=Polynomial.C 7*Polynomial.X+Polynomial.C 7
  runs x:=by
    let s : Store (Fin 4):=singletonStore 0 (prodCode ea eb x)
    let u : Store (Fin 4):=Function.update (singletonStore 0 (eb x.2)) 1 (ea x.1)
    have h1 : Runs (unquoteMove 0 1 2 3) s u (7*(ea x.1).length+6) := by
      have hh:=unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (ea x.1) (eb x.2) s
        (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      funext k; fin_cases k <;> simp [s,u,singletonStore,Function.update]
    have h2 : Runs (clear 0) u (singletonStore 1 (ea x.1)) (2*(eb x.2).length+1) := by
      have hh:=clear_runs (0 : Fin 4) u
      convert hh using 1
      · funext k; fin_cases k <;> simp [u,singletonStore,Function.update]
      · simp [u,singletonStore]
    refine ⟨(2*(eb x.2).length+1)+(7*(ea x.1).length+6),?_,Runs.seq h1 h2⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length]
    omega

noncomputable def second (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) eb Prod.snd :=
  ((first eb ea).comp (swap ea eb)).congrFun (by intro x; rfl)

end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackConstants
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_right _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]
/-- A fixed finite list is part of the program, not a run-time oracle. -/
def pushWord (k : K) : List Bool→Program K
  | []=>.skip
  | b::bs=>.seq (pushWord k bs) (.push k b)
lemma pushWord_runs (k : K) (xs : List Bool) (s : Store K) :
    Runs (pushWord k xs) s (Function.update s k (xs++s k)) (xs.length+1) := by
  induction xs with
  | nil=>simpa [pushWord] using Runs.skip s
  | cons b bs ih=>
    have hh:=Runs.seq ih (Runs.push (Function.update s k (bs++s k)) k b)
    simpa only [pushWord,Function.update_self,Function.update_idem,List.cons_append,
      List.length_cons,Nat.add_comm] using hh
namespace Procedure
variable {α β : Type} (ea : α→List Bool) (eb : β→List Bool)
noncomputable def constant (b : β) : Procedure ea eb (fun _=>b) where
  K:=Fin 1
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=0
  program:=.seq (clear 0) (pushWord 0 (eb b))
  bound:=Polynomial.C 2*Polynomial.X+Polynomial.C ((eb b).length+2)
  runs a:=by
    let s : Store (Fin 1):=singletonStore 0 (ea a)
    let u : Store (Fin 1):=Function.update s 0 []
    have hc:=clear_runs (0 : Fin 1) s
    have hp:=pushWord_runs (0 : Fin 1) (eb b) u
    have hh:=Runs.seq hc hp
    refine ⟨((eb b).length+1)+(2*(ea a).length+1),by simp;omega,?_⟩
    convert hh using 1
    · funext k;fin_cases k;simp [u,s,singletonStore]
    · simp [s,singletonStore]

/-- Count each actual symbol, returning a unary length. -/
noncomputable def length : Procedure (id : List Bool→List Bool)
    (fun n=>List.replicate n true) List.length where
  K:=Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=.loop 0 (.push 1 true) (.push 1 true)
  bound:=Polynomial.C 2*Polynomial.X+1
  runs xs:=by
    have h : ∀ xs (s : Store (Fin 2)),s 0=xs→
        Runs (.loop 0 (.push 1 true) (.push 1 true)) s
          (Function.update (Function.update s 0 []) 1 (List.replicate xs.length true++s 1))
          (2*xs.length+1) := by
      intro ys; induction ys with
      | nil=>
        intro s hs
        have he : Function.update (Function.update s 0 []) 1
            (List.replicate ([] : List Bool).length true++s 1)=s := by
          simp only [List.length_nil,List.replicate_zero,List.nil_append]
          rw [←hs,Function.update_eq_self,Function.update_eq_self]
        rw [he];exact Runs.loop_nil hs
      | cons y ys ih=>
        intro s hs
        let u:=Function.update s 0 ys
        let v:=Function.update u 1 (true::u 1)
        have hv : v 0=ys:=by simp [v,u]
        have htail:=ih v hv
        have hh : Runs (.loop 0 (.push 1 true) (.push 1 true)) s
            (Function.update (Function.update v 0 []) 1 (List.replicate ys.length true++v 1))
            (2*ys.length+1+1+1) := by
          cases y
          · exact Runs.loop_false (a:=1) (b:=2*ys.length+1) hs (Runs.push u 1 true) htail
          · exact Runs.loop_true (a:=1) (b:=2*ys.length+1) hs (Runs.push u 1 true) htail
        convert hh using 1 <;> try (simp only [List.length_cons, List.length_nil] <;> omega)
        · funext k;fin_cases k <;> simp [u,v,Function.update,List.replicate_succ]
          rw [←List.cons_append,←List.replicate_succ,List.replicate_succ',List.append_assoc]
          rfl
    refine ⟨2*xs.length+1,by simp,?_⟩
    convert h xs (singletonStore 0 xs) (by simp [singletonStore]) using 1 <;>
      (funext k;fin_cases k <;> simp [singletonStore,Function.update])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def leftPublic (K L : Type) : (K ⊕ Fin 2) ↪ ((K ⊕ L) ⊕ Fin 2) where
  toFun := fun k=>match k with | .inl i=>.inl (.inl i) | .inr i=>.inr i
  inj' := by intro i j h; cases i <;> cases j <;> simp_all

def rightPublic (K L : Type) : (L ⊕ Fin 2) ↪ ((K ⊕ L) ⊕ Fin 2) where
  toFun := fun k=>match k with | .inl i=>.inl (.inr i) | .inr i=>.inr i
  inj' := by intro i j h; cases i <;> cases j <;> simp_all

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {f g : α→β}
/-- A same-wire interface, even when the input and output word encodings differ. -/
noncomputable abbrev shared (p : Procedure ea eb f) : Procedure ea eb f where
  K:=p.K ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.seq (moveWord (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1))
    (.seq (p.program.relabel Sum.inl)
      (moveWord (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound:=Polynomial.C 8*Polynomial.X+Polynomial.C 5*p.bound+Polynomial.C 4
  runs a:=by
    obtain ⟨cp,hcp,hp⟩:=p.runs a
    have h1:=moveWord_runs (Sum.inr 0 : p.K ⊕ Fin 2) (Sum.inl p.input) (Sum.inr 1)
      (by simp) (by simp) (by simp) (ea a)
    have h2:=hp.relabel (leftEmbed p.K (Fin 2)) (fun _=>[])
    simp only [overlay_singleton] at h2
    have h3:=moveWord_runs (Sum.inl p.output : p.K ⊕ Fin 2) (Sum.inr 0) (Sum.inr 1)
      (by simp) (by simp) (by simp) (eb (f a))
    refine ⟨(4*(eb (f a)).length+2)+cp+(4*(ea a).length+2),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    have hl:=p.output_length_le a
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

/-- Reinterpret the domain, with its entire previous encoding still on tape. -/
def precompose (p : Procedure ea eb f) (h : γ→α) :
    Procedure (fun a=>ea (h a)) eb (fun a=>f (h a)) where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=p.runs (h a)

def congrEncoding (p : Procedure ea eb f) {ec : α→List Bool} {ed : β→List Bool}
    (ha : ∀a,ea a=ec a) (hb : ∀b,eb b=ed b) : Procedure ec ed f where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [ha,hb] using p.runs a

/-- Change the mathematical output only when its *actual encoded word* agrees. -/
def result (p : Procedure ea eb f) {ec : γ→List Bool} {h : α→γ}
    (hr : ∀a,eb (f a)=ec (h a)) : Procedure ea ec h where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [hr a] using p.runs a

noncomputable def unprefix (ea : α→List Bool) (b : Bool) :
    Procedure (fun a=>b::ea a) ea id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () .skip .skip .skip
  bound:=Polynomial.C 2
  runs a:=by
    refine ⟨2,by simp,?_⟩
    have hu : Function.update (singletonStore () (b::ea a)) () (ea a)=
        singletonStore () (ea a):=by simp [singletonStore]
    cases b
    · exact hu ▸ Runs.cases_false (by simp [singletonStore]) (Runs.skip _)
    · exact hu ▸ Runs.cases_true (by simp [singletonStore]) (Runs.skip _)

noncomputable def chooseBit (p : Procedure ea eb f) (q : Procedure ea eb g) :
    Procedure (fun x : Bool×α=>x.1::ea x.2) eb (fun x=>if x.1 then g x.2 else f x.2) where
  K:=(p.K ⊕ q.K) ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.cases (Sum.inr 0) .skip
    (p.shared.program.relabel (leftPublic p.K q.K))
    (q.shared.program.relabel (rightPublic p.K q.K))
  bound:=p.shared.bound+q.shared.bound+1
  runs x:=by
    rcases x with ⟨b,a⟩
    have hpmono:=eval_nat_mono p.shared.bound (Nat.le_succ (ea a).length)
    have hqmono:=eval_nat_mono q.shared.bound (Nat.le_succ (ea a).length)
    cases b
    · obtain ⟨c,hc,hd⟩:=p.shared.runs a
      have hh:=hd.relabel (leftPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : leftPublic p.K q.K p.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hpmono).trans (Nat.le_add_right _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (false::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_false (p:=Program.skip)
          (r:=q.shared.program.relabel (rightPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (false::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
    · obtain ⟨c,hc,hd⟩:=q.shared.runs a
      have hh:=hd.relabel (rightPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : rightPublic p.K q.K q.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hqmono).trans (Nat.le_add_left _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (true::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_true (p:=Program.skip)
          (q:=p.shared.program.relabel (leftPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (true::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)

abbrev boolCode (b : Bool) : List Bool := [b]
noncomputable def choose (p : Procedure ea eb f) (q : Procedure ea eb g) :
    Procedure (prodCode boolCode ea) eb (fun x=>if x.1 then g x.2 else f x.2) := by
  let pp:=p.comp (unprefix ea false)
  let qq:=q.comp (unprefix ea false)
  exact ((chooseBit pp qq).comp
    (unprefix (fun x : Bool×α=>x.1::false::ea x.2) true)).congrEncoding
      (by intro x;rfl) (by intro b;rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α : Type}
noncomputable def prepend (ea : α→List Bool) (xs : List Bool) :
    Procedure ea (fun a=>xs++ea a) id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=pushWord () xs
  bound:=Polynomial.C (xs.length+1)
  runs a:=by
    refine ⟨xs.length+1,by simp,?_⟩
    simpa [singletonStore] using pushWord_runs () xs (singletonStore () (ea a))

noncomputable def reverse : Procedure (id : List Bool→List Bool) id List.reverse where
  K:=Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=reverseMove 0 1
  bound:=Polynomial.C 2*Polynomial.X+1
  runs xs:=by
    have hh:=reverseMove_runs (0 : Fin 2) 1 (by decide) (singletonStore 0 xs)
    refine ⟨2*xs.length+1,by simp,?_⟩
    convert hh using 1
    · funext k;fin_cases k <;> simp [singletonStore,Function.update]
    · simp [singletonStore]
    · simp [singletonStore]

noncomputable def tail : Procedure (id : List Bool→List Bool) id List.tail where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () .skip .skip .skip
  bound:=Polynomial.C 2
  runs xs:=by
    refine ⟨2,by simp,?_⟩
    cases xs with
    | nil=>exact Runs.cases_nil (by simp [singletonStore]) (Runs.skip _)
    | cons b bs=>
      have hu : Function.update (singletonStore () (b::bs)) () bs=singletonStore () bs:=by
        simp [singletonStore]
      cases b
      · exact hu ▸ Runs.cases_false (by simp [singletonStore]) (Runs.skip _)
      · exact hu ▸ Runs.cases_true (by simp [singletonStore]) (Runs.skip _)

noncomputable def isEmpty : Procedure (id : List Bool→List Bool) boolCode List.isEmpty where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () (.push () true)
    (.seq (clear ()) (.push () false)) (.seq (clear ()) (.push () false))
  bound:=Polynomial.C 2*Polynomial.X+Polynomial.C 3
  runs xs:=by
    cases xs with
    | nil=>
      refine ⟨2,by simp,?_⟩
      exact Runs.cases_nil (by simp [singletonStore]) (by
        simpa [singletonStore,boolCode] using Runs.push (singletonStore () []) () true)
    | cons b bs=>
      let s:=singletonStore () bs
      let u:=Function.update s () []
      have hc:=clear_runs () s
      have hp:=Runs.push u () false
      have hh:=Runs.seq hc hp
      have hu : Function.update (singletonStore () (b::bs)) () bs=s:=by simp [s,singletonStore]
      have hv : Function.update u () (false::u ())=singletonStore () [false]:=by
        funext k;cases k;simp [u,s,singletonStore]
      rw [hv] at hh
      have ht : 1+(2*(s ()).length+1)=2*bs.length+2:=by simp [s,singletonStore];omega
      rw [ht] at hh
      refine ⟨2*bs.length+3,by simp,?_⟩
      cases b
      · exact Runs.cases_false (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)
      · exact Runs.cases_true (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)

noncomputable def head : Procedure (id : List Bool→List Bool) boolCode (fun xs=>xs.headD false) where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () (.push () false)
    (.seq (clear ()) (.push () false)) (.seq (clear ()) (.push () true))
  bound:=Polynomial.C 2*Polynomial.X+Polynomial.C 3
  runs xs:=by
    cases xs with
    | nil=>
      refine ⟨2,by simp,?_⟩
      exact Runs.cases_nil (by simp [singletonStore]) (by
        simpa [singletonStore,boolCode] using Runs.push (singletonStore () []) () false)
    | cons b bs=>
      let s:=singletonStore () bs
      let u:=Function.update s () []
      have hc:=clear_runs () s
      have hp:=Runs.push u () b
      have hh:=Runs.seq hc hp
      have hu : Function.update (singletonStore () (b::bs)) () bs=s:=by simp [s,singletonStore]
      have hv : Function.update u () (b::u ())=singletonStore () [b]:=by
        funext k;cases k;simp [u,s,singletonStore]
      rw [hv] at hh
      have ht : 1+(2*(s ()).length+1)=2*bs.length+2:=by simp [s,singletonStore];omega
      rw [ht] at hh
      refine ⟨2*bs.length+3,by simp,?_⟩
      cases b
      · exact Runs.cases_false (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)
      · exact Runs.cases_true (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)

end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackBooleans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
variable {β : Type}

/-- A truth table on one Boolean has two literal finite output words. This
performs no run-time computation in its Boolean branch labels. -/
noncomputable def ofBool (eb : β→List Bool) (f : Bool→β) :
    Procedure boolCode eb f := by
  let p:=constant (fun _ : Unit=>[]) eb (f false)
  let q:=constant (fun _ : Unit=>[]) eb (f true)
  exact ((chooseBit p q).precompose (fun b=>(b,()))).congrFun
    (by intro b;cases b <;> rfl)

noncomputable def ofBool₂ (eb : β→List Bool) (f : Bool→Bool→β) :
    Procedure (prodCode boolCode boolCode) eb (fun x=>f x.1 x.2) :=
  (choose (ofBool eb (f false)) (ofBool eb (f true))).congrFun
    (by rintro ⟨b,c⟩;cases b <;> rfl)

noncomputable def ofBool₃ (eb : β→List Bool) (f : Bool→Bool→Bool→β) :
    Procedure (prodCode boolCode (prodCode boolCode boolCode)) eb
      (fun x=>f x.1 x.2.1 x.2.2) :=
  (choose (ofBool₂ eb (f false)) (ofBool₂ eb (f true))).congrFun
    (by rintro ⟨b,c,d⟩;cases b <;> rfl)

noncomputable def boolNot : Procedure boolCode boolCode not := ofBool boolCode not
noncomputable def boolAnd : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>x.1 && x.2) := ofBool₂ boolCode and

noncomputable def cons : Procedure (prodCode boolCode (id : List Bool→List Bool)) id
    (fun x=>x.1::x.2) := by
  let pp : Procedure (id : List Bool→List Bool) id (fun xs=>false::xs):=
    (prepend id [false]).result (by intro xs;rfl)
  let qq : Procedure (id : List Bool→List Bool) id (fun xs=>true::xs):=
    (prepend id [true]).result (by intro xs;rfl)
  exact (choose pp qq).congrFun (by rintro ⟨b,xs⟩;cases b <;> rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α : Type} {ea : α→List Bool} {f : α→α}

/-- Return the result to one fixed public register. Both word movements are
implemented by two reversals; no output-to-input renaming is a TM operation. -/
noncomputable def inplace (p : Procedure ea ea f) : Procedure ea ea f where
  K:=p.K ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.seq (moveWord (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1))
    (.seq (p.program.relabel Sum.inl)
      (moveWord (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound:=Polynomial.C 8*Polynomial.X+Polynomial.C 5*p.bound+Polynomial.C 4
  runs a:=by
    obtain ⟨cp,hcp,hp⟩:=p.runs a
    have h1:=moveWord_runs (Sum.inr 0 : p.K ⊕ Fin 2) (Sum.inl p.input) (Sum.inr 1)
      (by simp) (by simp) (by simp) (ea a)
    have h2:=hp.relabel (leftEmbed p.K (Fin 2)) (fun _=>[])
    simp only [overlay_singleton] at h2
    have h3:=moveWord_runs (Sum.inl p.output : p.K ⊕ Fin 2) (Sum.inr 0) (Sum.inr 1)
      (by simp) (by simp) (by simp) (ea (f a))
    refine ⟨(4*(ea (f a)).length+2)+cp+(4*(ea a).length+2),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    have hl:=p.output_length_le a
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

/-- Literal repetition of an in-place subroutine by a unary counter. Each
iteration consumes one control token; the bound charges every subroutine step. -/
lemma iterate_loop_runs {L : Type} [DecidableEq L] (p : Procedure ea ea f)
    (he : p.output=p.input) (k : L) (n : ℕ) (a : α) (B : ℕ)
    (hm : ∀ i≤n,(ea ((f^[i]) a)).length≤B) (s : Store L)
    (hs : s k=List.replicate n true) :
    ∃ c,c≤n*(p.bound.eval B+1)+1 ∧
      Runs (.loop (Sum.inr k) (p.program.relabel Sum.inl) (p.program.relabel Sum.inl))
        (sumStore (singletonStore p.input (ea a)) s)
        (sumStore (singletonStore p.input (ea ((f^[n]) a))) (Function.update s k [])) c := by
  induction n generalizing a s with
  | zero =>
    have hk : Function.update s k []=s := by
      simp only [List.replicate_zero] at hs
      rw [←hs,Function.update_eq_self]
    refine ⟨1,by simp,?_⟩
    rw [Function.iterate_zero_apply,hk]
    apply Runs.loop_nil
    exact hs
  | succ n ih =>
    let t:=Function.update s k (List.replicate n true)
    have ht : t k=List.replicate n true:=by simp [t]
    have hm' : ∀ i≤n,(ea ((f^[i]) (f a))).length≤B := by
      intro i hi
      simpa only [Function.iterate_succ_apply] using hm (i+1) (by omega)
    obtain ⟨ct,hct,hrt⟩:=ih (f a) hm' t ht
    obtain ⟨cp,hcp,hrp⟩:=p.runs a
    rw [he] at hrp
    have hcall:=hrp.left t
    have hcpB : cp≤p.bound.eval B:=
      hcp.trans (eval_nat_mono p.bound (by simpa using hm 0 (by omega)))
    have hhead : sumStore (singletonStore p.input (ea a)) s (Sum.inr k)=
        true::List.replicate n true := by simpa only [sumStore_right,List.replicate_succ] using hs
    have hbody : Runs (p.program.relabel Sum.inl)
        (Function.update (sumStore (singletonStore p.input (ea a)) s)
          (Sum.inr k) (List.replicate n true))
        (sumStore (singletonStore p.input (ea (f a))) t) cp := by
      simpa only [sumStore_update_right] using hcall
    have hh:=Runs.loop_true hhead hbody hrt
    refine ⟨ct+cp+1,?_,?_⟩
    · nlinarith
    · simpa only [t,Function.update_idem,Function.iterate_succ_apply] using hh

/-- Input-length-bounded iteration. The extra hypothesis is solely a size
invariant along the already implemented iteration, not a computability oracle. -/
noncomputable def iterate (p : Procedure ea ea f) (q : Polynomial ℕ)
    (hgrowth : ∀ n a i,i≤n→(ea ((f^[i]) a)).length≤q.eval (n+(ea a).length)) :
    Procedure (prodCode (fun n=>List.replicate n true) ea) ea (fun x=>(f^[x.1]) x.2) where
  K:=p.inplace.K ⊕ Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inl p.inplace.input
  program:=.seq (unquoteMove (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3))
    (.seq (moveWord (Sum.inr 0) (Sum.inl p.inplace.input) (Sum.inr 2))
      (.loop (Sum.inr 1) (p.inplace.program.relabel Sum.inl) (p.inplace.program.relabel Sum.inl)))
  bound:=Polynomial.C 11*Polynomial.X+
    Polynomial.X*(p.inplace.bound.comp q+1)+Polynomial.C 9
  runs x:=by
    let r:=p.inplace
    let s : Store (r.K ⊕ Fin 4):=singletonStore (Sum.inr 0)
      (prodCode (fun n=>List.replicate n true) ea x)
    let u : Store (r.K ⊕ Fin 4):=Function.update (singletonStore (Sum.inr 0) (ea x.2))
      (Sum.inr 1) (List.replicate x.1 true)
    let v : Store (r.K ⊕ Fin 4):=sumStore (singletonStore r.input (ea x.2))
      (singletonStore 1 (List.replicate x.1 true))
    have hparse : Runs (unquoteMove (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)) s u
        (7*x.1+6) := by
      have hh:=unquoteMove_runs (Sum.inr 0 : r.K ⊕ Fin 4) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (List.replicate x.1 true) (ea x.2) s (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      · funext k; cases k with
        | inl k => simp [s,u,singletonStore,Function.update]
        | inr k => fin_cases k <;> simp [s,u,singletonStore,Function.update]
      · simp
    have hmove : Runs (moveWord (Sum.inr 0) (Sum.inl r.input) (Sum.inr 2)) u v
        (4*(ea x.2).length+2) := by
      let emb : Fin 3 ↪ r.K ⊕ Fin 4 :=
        ⟨fun k=>if k=0 then Sum.inr 0 else if k=1 then Sum.inl r.input else Sum.inr 2,
          by intro a b; fin_cases a <;> fin_cases b <;> simp⟩
      have emb0 : emb 0=Sum.inr 0 := rfl
      have emb1 : emb 1=Sum.inl r.input := rfl
      have emb2 : emb 2=Sum.inr 2 := rfl
      have hh:=(moveWord_runs (0 : Fin 3) 1 2 (by decide) (by decide) (by decide) (ea x.2)).relabel
        emb (singletonStore (Sum.inr 1) (List.replicate x.1 true))
      -- A framed move has the counter outside its three touched registers.
      have hs' : overlay emb (singletonStore (Sum.inr 1) (List.replicate x.1 true))
          (singletonStore 0 (ea x.2))=u := by
        funext k
        cases k with
        | inl k =>
          by_cases hk : k=r.input
          · subst k
            have h:=overlay_at emb (singletonStore (Sum.inr 1) (List.replicate x.1 true))
              (singletonStore 0 (ea x.2)) 1
            simpa [emb0,emb1,emb2,u,singletonStore] using h
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2,Ne.symm hk])]
            simp [u,singletonStore]
        | inr k =>
          fin_cases k
          · simpa [emb0,emb1,emb2,u,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 0 (ea x.2)) 0
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2])]
            simp [u,singletonStore]
          · simpa [emb0,emb1,emb2,u,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 0 (ea x.2)) 2
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2])]
            simp [u,singletonStore]
      have ht' : overlay emb (singletonStore (Sum.inr 1) (List.replicate x.1 true))
          (singletonStore 1 (ea x.2))=v := by
        funext k
        cases k with
        | inl k =>
          by_cases hk : k=r.input
          · subst k
            simpa [emb0,emb1,emb2,v,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 1 (ea x.2)) 1
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2,Ne.symm hk])]
            simp [v,singletonStore,hk]
        | inr k =>
          fin_cases k
          · simpa [emb0,emb1,emb2,v,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 1 (ea x.2)) 0
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2])]
            simp [v,singletonStore]
          · simpa [emb0,emb1,emb2,v,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 1 (ea x.2)) 2
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2])]
            simp [v,singletonStore]
      rw [hs',ht'] at hh
      simpa [moveWord,reverseMove,Program.relabel,emb0,emb1,emb2] using hh
    obtain ⟨cl,hcl,hl⟩:=iterate_loop_runs r rfl (1 : Fin 4) x.1 x.2
      (q.eval (x.1+(ea x.2).length)) (hgrowth x.1 x.2)
      (singletonStore 1 (List.replicate x.1 true)) (by simp [singletonStore])
    have hfinal : sumStore (singletonStore r.input (ea ((f^[x.1]) x.2)))
        (Function.update (singletonStore (1 : Fin 4) (List.replicate x.1 true)) 1 [])=
        singletonStore (Sum.inl r.input) (ea ((f^[x.1]) x.2)) := by
      rw [sumStore_singleton_left]
      congr 1
      funext k; fin_cases k <;> simp [singletonStore,Function.update]
    rw [hfinal] at hl
    refine ⟨cl+(4*(ea x.2).length+2)+(7*x.1+6),?_,
      Runs.seq hparse (Runs.seq hmove hl)⟩
    let L:=(prodCode (fun n=>List.replicate n true) ea x).length
    have hx : x.1+(ea x.2).length≤L:=by simp only [L,prodCode,pairBits_length,List.length_replicate]; omega
    have hm:=eval_nat_mono r.bound (eval_nat_mono q hx)
    dsimp only at hm
    have hmul:=Nat.mul_le_mul (by omega : x.1≤L) (Nat.add_le_add_right hm 1)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      Polynomial.eval_one,Polynomial.eval_comp]
    change cl+(4*(ea x.2).length+2)+(7*x.1+6)≤11*L+L*(r.bound.eval (q.eval L)+1)+9
    omega
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
def scanStep (f g : α→α) : List Bool×α→List Bool×α
  | ([],a)=>([],a)
  | (b::bs,a)=>(bs,if b then g a else f a)

def bitAction (f g : α→α) (a : α) (b : Bool) : α := if b then g a else f a

lemma scanStep_iterate (f g : α→α) (i : ℕ) (xs : List Bool) (a : α) :
    (scanStep f g)^[i] (xs,a)=(xs.drop i,(xs.take i).foldl (bitAction f g) a) := by
  induction i generalizing xs a with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil=>simpa [scanStep] using ih [] a
    | cons b bs=>simpa [scanStep,bitAction] using ih bs (if b then g a else f a)

lemma foldl_measure {m : α→ℕ} {f g : α→α} {c : ℕ}
    (hf : ∀a,m (f a)≤ m a+c) (hg : ∀a,m (g a)≤ m a+c) (xs : List Bool) (a : α) :
    m (xs.foldl (bitAction f g) a)≤ m a+xs.length*c := by
  induction xs generalizing a with
  | nil=>simp
  | cons b bs ih=>
    simp only [List.foldl_cons,List.length_cons]
    have hh : m (bitAction f g a b)≤ m a+c:=by cases b <;> simp [bitAction,hf,hg]
    have hi:=ih (bitAction f g a b)
    nlinarith

namespace Procedure
variable {ea : α→List Bool} {f g : α→α}
noncomputable def scan (p : Procedure ea ea f) (q : Procedure ea ea g) :
    Procedure (prodCode id ea) (prodCode id ea) (scanStep f g) := by
  let fst:=first (id : List Bool→List Bool) ea
  let snd:=second (id : List Bool→List Bool) ea
  let upd:=(choose p q).comp ((head.comp fst).pair snd)
  let body:=(tail.comp fst).pair upd
  let pp:=(choose body (identity (prodCode id ea))).comp
    ((isEmpty.comp fst).pair (identity (prodCode id ea)))
  exact pp.congrFun (by
    rintro ⟨xs,a⟩
    cases xs <;> rfl)

/-- Fold a variable Boolean word. The bound covers every actual intermediate
state; all pairing, data movement and loop iterations are charged. -/
noncomputable def foldBits (p : Procedure ea ea f) (q : Procedure ea ea g)
    (bound : Polynomial ℕ)
    (hsize : ∀ (xs : List Bool) a i,(ea ((xs.take i).foldl (bitAction f g) a)).length≤
      bound.eval (xs.length+(ea a).length)) :
    Procedure (prodCode id ea) ea (fun x=>x.1.foldl (bitAction f g) x.2) := by
  let s:=scan p q
  let rep:=s.iterate (Polynomial.C 2*Polynomial.X+1+bound) (by
    intro n x i _
    rw [scanStep_iterate]
    simp only [prodCode,pairBits_length,id_eq,List.length_drop]
    have hs:=hsize x.1 x.2 i
    have hm:=eval_nat_mono bound (by omega :
      x.1.length+(ea x.2).length≤n+(2*x.1.length+(ea x.2).length+1))
    dsimp only at hm
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let start:=(length.comp (first (id : List Bool→List Bool) ea)).pair (identity (prodCode id ea))
  exact ((second (id : List Bool→List Bool) ea).comp (rep.comp start)).congrFun (by
    rintro ⟨xs,a⟩
    change ((scanStep f g)^[xs.length] (xs,a)).2=xs.foldl (bitAction f g) a
    rw [scanStep_iterate,List.take_length])

noncomputable def foldBitsLinear (p : Procedure ea ea f) (q : Procedure ea ea g) (c : ℕ)
    (hf : ∀a,(ea (f a)).length≤(ea a).length+c)
    (hg : ∀a,(ea (g a)).length≤(ea a).length+c) :
    Procedure (prodCode id ea) ea (fun x=>x.1.foldl (bitAction f g) x.2) :=
  foldBits p q (Polynomial.C (c+1)*Polynomial.X) (by
    intro xs a i
    have hh:=foldl_measure (m:=fun a=>(ea a).length) (f:=f) (g:=g) (c:=c) hf hg (xs.take i) a
    have hl : (xs.take i).length≤xs.length:=by simp only [List.length_take];omega
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    nlinarith)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackIncrement
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_right _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

/-- Little-endian evaluation; leading zeroes at the high end are allowed. -/
def binaryValue : List Bool → ℕ
  | [] => 0
  | b::xs => b.toNat+2*binaryValue xs

def incrementWord : List Bool → List Bool
  | [] => [true]
  | false::xs => true::xs
  | true::xs => false::incrementWord xs

def carryTail : List Bool → List Bool
  | [] => [true]
  | false::xs => true::xs
  | true::xs => carryTail xs

def carryCount : List Bool → ℕ
  | [] => 0
  | false::_ => 0
  | true::xs => carryCount xs+1

lemma carryCount_le_length (xs : List Bool) : carryCount xs≤xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [carryCount,List.length_cons]; omega
lemma incrementWord_eq (xs : List Bool) :
    incrementWord xs=List.replicate (carryCount xs) false++carryTail xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [incrementWord,carryCount,carryTail,ih,List.replicate_succ]
lemma incrementWord_length (xs : List Bool) : (incrementWord xs).length≤xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [incrementWord,List.length_cons]; omega

variable {K : Type} [DecidableEq K]
def rippleBody (a t c : K) : Program K :=
  .cases a (.push a true) (.push a true) (.seq (.push t false) (.push c true))
def ripple (a t c : K) : Program K := .loop c (rippleBody a t c) (rippleBody a t c)
def increment (a t c : K) : Program K :=
  .seq (.push c true) (.seq (ripple a t c) (reverseMove t a))

lemma ripple_runs (a t c : K) (hat : a≠t) (hac : a≠c) (htc : t≠c)
    (s : Store K) (hc : s c=[true]) :
    Runs (ripple a t c) s
      (Function.update (Function.update (Function.update s c []) a (carryTail (s a)))
        t (List.replicate (carryCount (s a)) false++s t))
      (4*(carryCount (s a)+1)) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    let u := Function.update s c []
    let v := Function.update u a [true]
    have hua : u a=[] := by simp [u,hac,hs]
    have hvc : v c=[] := by simp [v,u,hac.symm]
    have body : Runs (rippleBody a t c) u v 2 :=
      Runs.cases_nil hua (by simpa only [hua] using Runs.push u a true)
    have hh := Runs.loop_true (p:=rippleBody a t c) (a:=2) (b:=1) hc body (Runs.loop_nil hvc)
    change Runs (.loop _ _ _) _ _ _
    convert hh using 1
    · simp only [carryCount,carryTail,List.replicate_zero,List.nil_append]
      change Function.update v t (s t)=v
      rw [← show v t=s t by simp [v,u,hat.symm,htc],Function.update_eq_self]
    · rfl
  | cons x xs ih =>
    cases x
    · let u := Function.update s c []
      let w := Function.update u a xs
      let v := Function.update w a (true::xs)
      have hua : u a=false::xs := by simp [u,hac,hs]
      have hvc : v c=[] := by simp [v,w,u,hac.symm]
      have body : Runs (rippleBody a t c) u v 2 :=
        Runs.cases_false hua (by simpa only [w,Function.update_self] using Runs.push w a true)
      have hh := Runs.loop_true (p:=rippleBody a t c) (a:=2) (b:=1) hc body (Runs.loop_nil hvc)
      change Runs (.loop _ _ _) _ _ _
      convert hh using 1
      · funext k
        by_cases ha : k=a <;> by_cases ht : k=t <;> by_cases hcc : k=c <;>
          simp_all [v,w,u,Function.update,carryCount,carryTail]
      · rfl
    · let u := Function.update s c []
      let w := Function.update u a xs
      let z := Function.update w t (false::w t)
      let v := Function.update z c (true::z c)
      have hua : u a=true::xs := by simp [u,hac,hs]
      have hva : v a=xs := by simp [v,z,w,hac,hat]
      have hvc : v c=[true] := by simp [v,z,w,u,htc.symm,hac.symm]
      have body : Runs (rippleBody a t c) u v 3 :=
        Runs.cases_true (a:=2) hua (Runs.seq (Runs.push w t false) (Runs.push z c true))
      have hh := Runs.loop_true (p:=rippleBody a t c) (a:=3) (b:=4*(carryCount xs+1)) hc body (ih v hvc hva)
      change Runs (.loop _ _ _) _ _ _
      convert hh using 1
      · funext k
        by_cases ha : k=a <;> by_cases ht : k=t <;> by_cases hcc : k=c <;>
          simp_all [v,z,w,u,Function.update,carryCount,carryTail,List.replicate_succ]
        rw [← List.cons_append, ← List.replicate_succ, List.replicate_succ',List.append_assoc]
        rfl
      · simp only [carryCount]; omega

lemma increment_runs (a t c : K) (hat : a≠t) (hac : a≠c) (htc : t≠c)
    (s : Store K) (ht : s t=[]) (hc : s c=[]) :
    Runs (increment a t c) s (Function.update s a (incrementWord (s a)))
      (6*carryCount (s a)+6) := by
  let u := Function.update s c [true]
  have hua : u a=s a := by simp [u,hac]
  have hut : u t=[] := by simp [u,ht,htc]
  have huc : u c=[true] := by simp [u]
  let v := Function.update (Function.update (Function.update u c []) a (carryTail (u a)))
    t (List.replicate (carryCount (u a)) false++u t)
  have hp : Runs (.push c true) s u 1 := by simpa only [hc] using Runs.push s c true
  have hh := Runs.seq hp
    (Runs.seq (ripple_runs a t c hat hac htc u huc) (reverseMove_runs t a hat.symm v))
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases htk : k=t <;> by_cases hck : k=c <;>
      simp_all [v,u,Function.update,incrementWord_eq]
  · simp only [v,Function.update_self,hut,List.append_nil,List.length_replicate,hua]
    omega

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackNaturals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma binaryValue_bits (n : ℕ) : binaryValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [binaryValue,ih,Nat.bit,Nat.add_comm]

lemma incrementWord_bits (n : ℕ) : incrementWord n.bits=(n+1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b
    · simp only [incrementWord,Nat.bit_false,Nat.bit1_bits]
    · simp only [incrementWord,ih,Nat.bit_true]
      rw [show 2*n+1+1=2*(n+1) by omega,Nat.bit0_bits (n+1) (by omega)]

abbrev unaryCode (n : ℕ) := List.replicate n true
namespace Procedure
noncomputable def successor : Procedure Nat.bits Nat.bits Nat.succ where
  K:=Fin 3
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=0
  program:=increment 0 1 2
  bound:=Polynomial.C 6*Polynomial.X+Polynomial.C 6
  runs n:=by
    have hh:=increment_runs (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
      (singletonStore 0 n.bits) (by simp [singletonStore]) (by simp [singletonStore])
    refine ⟨6*carryCount n.bits+6,?_,?_⟩
    · have hl:=carryCount_le_length n.bits
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
      omega
    · simpa [singletonStore,incrementWord_bits] using hh

noncomputable def unarySuccessor : Procedure unaryCode unaryCode Nat.succ where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.push () true
  bound:=1
  runs n:=by
    refine ⟨1,by simp,?_⟩
    simpa [singletonStore,unaryCode,List.replicate_succ] using
      Runs.push (singletonStore () (unaryCode n)) () true

/-- Unary-to-binary conversion charges every carry and all word moves. -/
noncomputable def unaryToBits : Procedure unaryCode Nat.bits id := by
  let p:=successor.iterate (Polynomial.X+1) (by
    intro n a i hi
    have hlen : (a+i).bits.length≤a.bits.length+i := by
      clear hi
      induction i with
      | zero => simp
      | succ i ih =>
        have h:=incrementWord_length (a+i).bits
        rw [incrementWord_bits] at h
        simpa only [Nat.add_assoc] using (h.trans (Nat.add_le_add_right ih 1))
    simpa only [Function.iterate_succ_apply',Function.iterate_succ_apply,
      Nat.succ_iterate,Nat.size_eq_bits_len,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one] using (hlen.trans (by omega : a.bits.length+i≤n+a.bits.length+1)))
  exact (p.comp ((identity unaryCode).pair (constant unaryCode Nat.bits 0))).congrFun
    (by intro n; simp [Nat.succ_iterate])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackBinaryBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma binaryValue_append (xs ys : List Bool) :
    binaryValue (xs++ys)=binaryValue xs+2^xs.length*binaryValue ys := by
  induction xs with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    simp only [List.cons_append,List.length_cons,binaryValue,ih,pow_succ]
    ring

lemma bigEndian_value (xs : List Bool) (a : ℕ) :
    xs.foldl (bitAction (fun n=>2*n) (fun n=>2*n+1)) a=
      binaryValue xs.reverse+2^xs.length*a := by
  induction xs generalizing a with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    simp only [List.foldl_cons,ih,List.reverse_cons,binaryValue_append,
      List.length_reverse,List.length_cons,pow_succ]
    cases b <;> simp [bitAction,binaryValue] <;> ring

lemma double_bits_length (n : ℕ) : (2*n).bits.length≤n.bits.length+1 := by
  by_cases h : n=0
  · subst n;simp
  · rw [Nat.bit0_bits n h,List.length_cons]
lemma doubleOne_bits_length (n : ℕ) : (2*n+1).bits.length≤n.bits.length+1 := by
  rw [Nat.bit1_bits,List.length_cons]

namespace Procedure
noncomputable def double : Procedure Nat.bits Nat.bits (fun n=>2*n) where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () .skip (.seq (.push () false) (.push () false))
    (.seq (.push () true) (.push () false))
  bound:=Polynomial.C 3
  runs n:=by
    by_cases hn : n=0
    · subst n
      refine ⟨2,by simp,?_⟩
      exact Runs.cases_nil (by simp [singletonStore]) (Runs.skip _)
    · have he : n.bits≠[]:=by
        intro h
        have hv:=binaryValue_bits n
        rw [h] at hv
        exact hn hv.symm
      cases hb : n.bits with
      | nil=>exact (he hb).elim
      | cons b bs=>
        have hout : (2*n).bits=false::b::bs:=by rw [Nat.bit0_bits n hn,hb]
        have hbody : Runs (.seq (.push () b) (.push () false))
            (singletonStore () bs) (singletonStore () (false::b::bs)) 2:=by
          have hh:=Runs.seq (Runs.push (singletonStore () bs) () b)
            (Runs.push (singletonStore () (b::bs)) () false)
          simpa only [singletonStore,Function.update_self,Function.update_idem] using hh
        refine ⟨3,by simp,?_⟩
        rw [hout]
        cases b
        · exact Runs.cases_false (xs:=bs) (by simp [singletonStore]) (by simpa [singletonStore] using hbody)
        · exact Runs.cases_true (xs:=bs) (by simp [singletonStore]) (by simpa [singletonStore] using hbody)

noncomputable def doubleOne : Procedure Nat.bits Nat.bits (fun n=>2*n+1) :=
  (prepend Nat.bits [true]).result (by intro n;simp only [List.singleton_append,Nat.bit1_bits,id_eq])

/-- Canonicalize a binary word, charging a linear-growth bit fold. -/
noncomputable def normalize : Procedure (id : List Bool→List Bool) Nat.bits binaryValue := by
  let p:=foldBitsLinear double doubleOne 1 double_bits_length doubleOne_bits_length
  let start:=reverse.pair (constant (id : List Bool→List Bool) Nat.bits 0)
  exact (p.comp start).congrFun (by intro xs;simp [bigEndian_value])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def addCounter (x : ℕ×ℕ) := (x.1,x.1+x.2)
lemma addCounter_iterate (i : ℕ) (x : ℕ×ℕ) :
    addCounter^[i] x=(x.1,i*x.1+x.2) := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply',ih]
    simp only [addCounter,Prod.mk.injEq,true_and,Nat.succ_mul]
    omega

namespace Procedure
noncomputable def unaryAdd : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x=>x.1+x.2) :=
  (unarySuccessor.iterate Polynomial.X (by
    intro n a i hi
    simp only [Nat.succ_iterate,unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)).congrFun (by intro x;simp [Nat.succ_iterate,Nat.add_comm])

noncomputable def unaryMul : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x=>x.1*x.2) := by
  let step : Procedure (prodCode unaryCode unaryCode) (prodCode unaryCode unaryCode) addCounter:=
    ((first unaryCode unaryCode).pair unaryAdd).congrFun (by intro x;rfl)
  let rep:=step.iterate (Polynomial.X^2+Polynomial.X) (by
    intro n x i hi
    rw [addCounter_iterate]
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate,
      Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X]
    have hm : x.1≤n+(2*x.1+1+x.2):=by omega
    have hii : i≤n+(2*x.1+1+x.2):=by omega
    have hh:=Nat.mul_le_mul hii hm
    nlinarith)
  let fst:=first unaryCode unaryCode
  let snd:=second unaryCode unaryCode
  let start:=fst.pair (snd.pair (constant (prodCode unaryCode unaryCode) unaryCode 0))
  exact ((second unaryCode unaryCode).comp (rep.comp start)).congrFun (by
    intro x
    change (addCounter^[x.1] (x.2,0)).2=x.1*x.2
    simp [addCounter_iterate])

end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackAdder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

/-- Literal full-adder truth tables, not an arithmetic oracle. -/
def sumBit (a b c : Bool) : Bool := xor a (xor b c)
def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

lemma sum_carry (a b c : Bool) :
    a.toNat+b.toNat+c.toNat=(sumBit a b c).toNat+2*(carryBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

abbrev AddState := List Bool × List Bool × Bool × List Bool
abbrev addStateCode : AddState→List Bool :=
  prodCode id (prodCode id (prodCode Procedure.boolCode id))

def addStep (s : AddState) : AddState :=
  (s.1.tail,s.2.1.tail,
    carryBit (s.1.headD false) (s.2.1.headD false) s.2.2.1,
    sumBit (s.1.headD false) (s.2.1.headD false) s.2.2.1 :: s.2.2.2)

def addMeasure (s : AddState) : ℕ := s.1.length+s.2.1.length+s.2.2.1.toNat

def residual (s : AddState) : ℕ := binaryValue s.1+binaryValue s.2.1+s.2.2.1.toNat

def addInvariant (s : AddState) : ℕ :=
  binaryValue s.2.2.2.reverse+2^s.2.2.2.length*residual s

lemma binaryValue_head_tail (xs : List Bool) :
    binaryValue xs=(xs.headD false).toNat+2*binaryValue xs.tail := by
  cases xs <;> rfl

lemma addInvariant_step (s : AddState) : addInvariant (addStep s)=addInvariant s := by
  have hx:=binaryValue_head_tail s.1
  have hy:=binaryValue_head_tail s.2.1
  have hh:=sum_carry (s.1.headD false) (s.2.1.headD false) s.2.2.1
  simp only [addInvariant,addStep,List.reverse_cons,binaryValue_append,List.length_reverse,
    binaryValue,List.length_cons,pow_succ,residual]
  rw [hx,hy]
  nlinarith [congrArg (fun n : ℕ=>2^s.2.2.2.length*n) hh]

lemma addInvariant_iterate (i : ℕ) (s : AddState) :
    addInvariant (addStep^[i] s)=addInvariant s := by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',addInvariant_step,ih]

def wordAdd (x : List Bool×List Bool) : List Bool :=
  (addStep^[x.1.length+x.2.length+1] (x.1,x.2,false,[])).2.2.2.reverse

lemma addStep_size (s : AddState) :
    (addStateCode (addStep s)).length≤(addStateCode s).length+1 := by
  simp only [addStateCode,addStep,prodCode,pairBits_length,id_eq,Procedure.boolCode,
    List.length_cons,List.length_tail]
  omega

namespace Procedure
variable {α : Type} {ea : α→List Bool} {f : α→α}

noncomputable def iterateLinear (p : Procedure ea ea f) (c : ℕ)
    (hg : ∀a,(ea (f a)).length≤(ea a).length+c) :
    Procedure (prodCode unaryCode ea) ea (fun x=>f^[x.1] x.2) := by
  have hh : ∀ i a,(ea (f^[i] a)).length≤(ea a).length+i*c:=by
    intro i a
    induction i with
    | zero=>simp
    | succ i ih=>
      rw [Function.iterate_succ_apply']
      have h:=hg (f^[i] a)
      nlinarith
  exact p.iterate (Polynomial.C (c+1)*Polynomial.X) (by
    intro n a i hi
    have h:=hh i a
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    nlinarith)

noncomputable def addStepP : Procedure addStateCode addStateCode addStep := by
  let x:=first (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let rem:=second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let y:=(first (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let c:=(first boolCode (id : List Bool→List Bool)).comp co
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  let bits:=(head.comp x).pair ((head.comp y).pair c)
  let newc:=(ofBool₃ boolCode carryBit).comp bits
  let newb:=(ofBool₃ boolCode sumBit).comp bits
  exact ((tail.comp x).pair ((tail.comp y).pair
    (newc.pair (cons.comp (newb.pair zs))))).congrFun (by intro s;rfl)

noncomputable def wordAddP : Procedure (prodCode (id : List Bool→List Bool) id) id wordAdd := by
  let x:=first (id : List Bool→List Bool) (id : List Bool→List Bool)
  let y:=second (id : List Bool→List Bool) (id : List Bool→List Bool)
  let len:=unarySuccessor.comp (unaryAdd.comp ((length.comp x).pair (length.comp y)))
  let start:=x.pair (y.pair ((constant (prodCode id id) boolCode false).pair
    (constant (prodCode id id) (id : List Bool→List Bool) [])))
  let rep:=addStepP.iterateLinear 1 addStep_size
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp
    (second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id)))
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  exact (reverse.comp (zs.comp (rep.comp (len.pair start)))).congrFun (by intro x;rfl)

end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackSubtractor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def borrowBit (a b c : Bool) : Bool := (!a && b) || (!a && c) || (b && c)

lemma difference_borrow (a b c : Bool) :
    (a.toNat : ℤ)-b.toNat-c.toNat=(sumBit a b c).toNat-2*(borrowBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

lemma binaryValue_lt (xs : List Bool) : binaryValue xs<2^xs.length := by
  induction xs with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    simp only [List.length_cons,binaryValue,pow_succ]
    cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

abbrev SubState := AddState
abbrev subStateCode := addStateCode

def subStep (s : SubState) : SubState :=
  (s.1.tail,s.2.1.tail,
    borrowBit (s.1.headD false) (s.2.1.headD false) s.2.2.1,
    sumBit (s.1.headD false) (s.2.1.headD false) s.2.2.1 :: s.2.2.2)

def subInvariant (s : SubState) : ℤ :=
  (binaryValue s.2.2.2.reverse : ℤ)+2^s.2.2.2.length*
    ((binaryValue s.1 : ℤ)-binaryValue s.2.1-s.2.2.1.toNat)

lemma subInvariant_step (s : SubState) : subInvariant (subStep s)=subInvariant s := by
  have hx:=binaryValue_head_tail s.1
  have hy:=binaryValue_head_tail s.2.1
  have hh:=difference_borrow (s.1.headD false) (s.2.1.headD false) s.2.2.1
  simp only [subInvariant,subStep,List.reverse_cons,binaryValue_append,List.length_reverse,
    binaryValue,List.length_cons,pow_succ]
  push_cast
  have hx' : (binaryValue s.1 : ℤ)=(s.1.headD false).toNat+2*binaryValue s.1.tail:=by
    exact_mod_cast hx
  have hy' : (binaryValue s.2.1 : ℤ)=(s.2.1.headD false).toNat+2*binaryValue s.2.1.tail:=by
    exact_mod_cast hy
  rw [hx',hy']
  nlinarith [congrArg (fun n : ℤ=>2^s.2.2.2.length*n) hh]

lemma subInvariant_iterate (i : ℕ) (s : SubState) :
    subInvariant (subStep^[i] s)=subInvariant s := by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',subInvariant_step,ih]

lemma subStep_tapes (i : ℕ) (s : SubState) :
    (subStep^[i] s).1=s.1.drop i ∧ (subStep^[i] s).2.1=s.2.1.drop i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    simp only [subStep,ih.1,ih.2,List.tail_drop]
    trivial

def wordSubtract (x : List Bool×List Bool) : Bool×List Bool :=
  let s:=subStep^[x.1.length+x.2.length+1] (x.1,x.2,false,[])
  (s.2.2.1,s.2.2.2.reverse)

lemma wordSubtract_spec (x : List Bool×List Bool) :
    (binaryValue (wordSubtract x).2 : ℤ) -
      2^(wordSubtract x).2.length*((wordSubtract x).1.toNat : ℤ)=
      (binaryValue x.1 : ℤ)-binaryValue x.2 := by
  let s : SubState:=(x.1,x.2,false,[])
  let i:=x.1.length+x.2.length+1
  have hx : (subStep^[i] s).1=[]:=by
    rw [(subStep_tapes i s).1]
    exact List.drop_eq_nil_iff.mpr (by dsimp [s,i];omega)
  have hy : (subStep^[i] s).2.1=[]:=by
    rw [(subStep_tapes i s).2]
    exact List.drop_eq_nil_iff.mpr (by dsimp [s,i];omega)
  have hh:=subInvariant_iterate i s
  simp only [subInvariant,hx,hy,binaryValue,Int.natCast_zero,zero_sub] at hh
  simpa [wordSubtract,s,i,List.length_reverse,subInvariant,binaryValue,sub_eq_add_neg] using hh

lemma wordSubtract_borrow (x : List Bool×List Bool) :
    (wordSubtract x).1=decide (binaryValue x.1<binaryValue x.2) := by
  have hh:=wordSubtract_spec x
  have hl:=binaryValue_lt (wordSubtract x).2
  have hl' : (binaryValue (wordSubtract x).2 : ℤ)<2^(wordSubtract x).2.length:=by
    exact_mod_cast hl
  cases hb : (wordSubtract x).1 <;> simp only [hb,Bool.toNat_false,Bool.toNat_true,
    Int.natCast_zero,Int.natCast_one,mul_zero,mul_one,sub_zero] at hh
  · symm;apply decide_eq_false;omega
  · symm;apply decide_eq_true;omega

lemma wordSubtract_value (x : List Bool×List Bool) :
    (if (wordSubtract x).1 then 0 else binaryValue (wordSubtract x).2)=
      binaryValue x.1-binaryValue x.2 := by
  have hh:=wordSubtract_spec x
  have hb:=wordSubtract_borrow x
  cases hc : (wordSubtract x).1
  · simp only [hc,Bool.false_eq_true,ite_false, if_false,Bool.toNat_false,Int.natCast_zero,mul_zero,sub_zero] at *
    omega
  · simp only [hc,ite_true, if_true,true_eq_decide_iff] at *
    omega

lemma subStep_size (s : SubState) :
    (subStateCode (subStep s)).length≤(subStateCode s).length+1 := by
  simp only [subStateCode,addStateCode,subStep,prodCode,pairBits_length,id_eq,Procedure.boolCode,
    List.length_cons,List.length_tail]
  omega


end ExactQuantumFactoring.BitStackProgram
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

lemma bits_length_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_Procedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure
noncomputable def subStepP : Procedure subStateCode subStateCode subStep := by
  let x:=first (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let rem:=second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let y:=(first (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let c:=(first boolCode (id : List Bool→List Bool)).comp co
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  let bits:=(head.comp x).pair ((head.comp y).pair c)
  let newc:=(ofBool₃ boolCode borrowBit).comp bits
  let newb:=(ofBool₃ boolCode sumBit).comp bits
  exact ((tail.comp x).pair ((tail.comp y).pair
    (newc.pair (cons.comp (newb.pair zs))))).congrFun (by intro s;rfl)

noncomputable def wordSubtractP :
    Procedure (prodCode (id : List Bool→List Bool) id) (prodCode boolCode id) wordSubtract := by
  let x:=first (id : List Bool→List Bool) (id : List Bool→List Bool)
  let y:=second (id : List Bool→List Bool) (id : List Bool→List Bool)
  let len:=unarySuccessor.comp (unaryAdd.comp ((length.comp x).pair (length.comp y)))
  let start:=x.pair (y.pair ((constant (prodCode id id) boolCode false).pair
    (constant (prodCode id id) (id : List Bool→List Bool) [])))
  let rep:=subStepP.iterateLinear 1 subStep_size
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp
    (second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id)))
  let c:=(first boolCode (id : List Bool→List Bool)).comp co
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  exact ((c.pair (reverse.comp zs)).comp (rep.comp (len.pair start))).congrFun (by intro x;rfl)

noncomputable def binaryLt : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x=>decide (x.1<x.2)) :=
  (((first boolCode (id : List Bool→List Bool)).comp wordSubtractP).precompose
    (fun x : ℕ×ℕ=>(x.1.bits,x.2.bits))).congrFun
      (by
        intro x
        change (wordSubtract (x.1.bits,x.2.bits)).1=decide (x.1<x.2)
        rw [wordSubtract_borrow,binaryValue_bits,binaryValue_bits])

noncomputable def binaryLe : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x=>decide (x.1≤x.2)) :=
  (boolNot.comp (binaryLt.comp (swap Nat.bits Nat.bits))).congrFun (by
    intro x
    change (!(decide (x.2<x.1)))=decide (x.1≤x.2)
    simp only [← decide_not,Nat.not_lt])

noncomputable def binarySub : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1-x.2) :=
  (((choose normalize (constant (id : List Bool→List Bool) Nat.bits 0)).comp
    wordSubtractP).precompose (fun x : ℕ×ℕ=>(x.1.bits,x.2.bits))).congrFun
      (by
        intro x
        change (if (wordSubtract (x.1.bits,x.2.bits)).1 then 0 else
          binaryValue (wordSubtract (x.1.bits,x.2.bits)).2)=x.1-x.2
        rw [wordSubtract_value,binaryValue_bits,binaryValue_bits])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
    {c : α→Bool} {f g : α→β}
noncomputable def conditional (test : Procedure ea boolCode c)
    (yes : Procedure ea eb f) (no : Procedure ea eb g) :
    Procedure ea eb (fun x=>if c x then f x else g x) :=
  (choose no yes).comp (test.pair (identity ea))

noncomputable def binaryZero : Procedure Nat.bits boolCode (fun n=>decide (n=0)) :=
  (isEmpty.precompose Nat.bits).congrFun (by
    intro n
    by_cases hn : n=0
    · subst n;rfl
    · have hh : n.bits≠[]:=by
        intro h
        have hy:=binaryValue_bits n
        rw [h] at hy
        exact hn hy.symm
      simp [hh,hn])
end Procedure

abbrev DivState := ℕ×ℕ×ℕ
abbrev divStateCode := prodCode Nat.bits (prodCode Nat.bits Nat.bits)

def divStep (b : Bool) (x : DivState) : DivState :=
  let t:=2*x.2.2+b.toNat
  if x.1≤t then (x.1,2*x.2.1+1,t-x.1) else (x.1,2*x.2.1,t)

lemma divStep_fst (b : Bool) (x : DivState) : (divStep b x).1=x.1 := by
  dsimp only [divStep];split <;> rfl

lemma divStep_size (b : Bool) (x : DivState) :
    (divStateCode (divStep b x)).length≤(divStateCode x).length+3 := by
  have hq : (2*x.2.1+1).bits.length≤x.2.1.bits.length+1:=doubleOne_bits_length _
  have hq0:=double_bits_length x.2.1
  have hr : (2*x.2.2+b.toNat).bits.length≤x.2.2.bits.length+1:=by
    cases b
    · simpa using double_bits_length x.2.2
    · exact doubleOne_bits_length x.2.2
  have hs : (2*x.2.2+b.toNat-x.1).bits.length≤(2*x.2.2+b.toNat).bits.length:=
    bits_length_mono (Nat.sub_le _ _)
  simp only [divStateCode,divStep,prodCode,pairBits_length]
  split <;> dsimp only <;> omega

lemma divStep_spec (b : Bool) (x : DivState) (hr : x.2.2<x.1) :
    (divStep b x).2.2<x.1 ∧
      (divStep b x).2.1*x.1+(divStep b x).2.2=
        2*(x.2.1*x.1+x.2.2)+b.toNat := by
  have hb : b.toNat≤1:=by cases b <;> decide
  dsimp only [divStep]
  split
  · rename_i h
    have ht:=Nat.sub_add_cancel h
    dsimp only
    constructor <;> nlinarith
  · rename_i h
    dsimp only
    constructor <;> nlinarith

lemma div_fold_spec (xs : List Bool) (x : DivState) (hr : x.2.2<x.1) :
    let y:=xs.foldl (bitAction (divStep false) (divStep true)) x
    y.1=x.1 ∧ y.2.2<x.1 ∧
      y.2.1*x.1+y.2.2=binaryValue xs.reverse+2^xs.length*(x.2.1*x.1+x.2.2) := by
  induction xs generalizing x with
  | nil=>simp [binaryValue,hr]
  | cons b bs ih=>
    have he : bitAction (divStep false) (divStep true) x b=divStep b x:=by cases b <;> rfl
    rw [List.foldl_cons,he]
    have H:=divStep_spec b x hr
    have hi:=ih (divStep b x) (by rw [divStep_fst];exact H.1)
    simp only [divStep_fst] at hi
    refine ⟨hi.1,hi.2.1,?_⟩
    rw [hi.2.2,H.2]
    simp only [List.reverse_cons,binaryValue_append,List.length_reverse,List.length_cons,
      binaryValue,pow_succ]
    ring

def divideRaw (x : List Bool×ℕ) : ℕ×ℕ :=
  (x.1.reverse.foldl (bitAction (divStep false) (divStep true)) (x.2,0,0)).2

lemma divideRaw_spec (x : List Bool×ℕ) (hp : 0<x.2) :
    divideRaw x=(binaryValue x.1/x.2,binaryValue x.1%x.2) := by
  have hh:=div_fold_spec x.1.reverse (x.2,0,0) hp
  simp only [List.reverse_reverse,zero_mul,mul_zero,Nat.add_zero] at hh
  have hq : binaryValue x.1/x.2=(divideRaw x).1:=by
    apply Nat.div_eq_of_lt_le <;> dsimp [divideRaw] <;> nlinarith [hh.2.1,hh.2.2]
  have hm:=Nat.mod_add_div (binaryValue x.1) x.2
  rw [hq] at hm
  apply Prod.ext
  · exact hq.symm
  · dsimp [divideRaw] at hm ⊢;nlinarith [hh.2.2]

namespace Procedure
noncomputable def divStepP (b : Bool) : Procedure divStateCode divStateCode (divStep b) := by
  let d:=first Nat.bits (prodCode Nat.bits Nat.bits)
  let qr:=second Nat.bits (prodCode Nat.bits Nat.bits)
  let q:=(first Nat.bits Nat.bits).comp qr
  let r:=(second Nat.bits Nat.bits).comp qr
  let db : Procedure Nat.bits Nat.bits (fun n=>2*n+b.toNat):=by
    cases b
    · exact double.congrFun (by intro n;simp)
    · exact doubleOne
  let t:=db.comp r
  let test:=binaryLe.comp (d.pair t)
  let yes:=d.pair ((doubleOne.comp q).pair (binarySub.comp (t.pair d)))
  let no:=d.pair ((double.comp q).pair t)
  exact (conditional test yes no).congrFun (by intro x;simp only [Function.comp_apply,divStep,decide_eq_true_eq])

noncomputable def divideRawP : Procedure (prodCode (id : List Bool→List Bool) Nat.bits)
    (prodCode Nat.bits Nat.bits) divideRaw := by
  let x:=first (id : List Bool→List Bool) Nat.bits
  let d:=second (id : List Bool→List Bool) Nat.bits
  let zero:=constant (prodCode (id : List Bool→List Bool) Nat.bits) Nat.bits 0
  let start:=(reverse.comp x).pair (d.pair (zero.pair zero))
  let fold:=foldBitsLinear (divStepP false) (divStepP true) 3 (divStep_size false) (divStep_size true)
  exact ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp (fold.comp start)).congrFun (by intro x;rfl)

noncomputable def binaryDivMod : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) (fun x=>(x.1/x.2,x.1%x.2)) := by
  let raw:=(divideRawP.precompose (fun x : ℕ×ℕ=>(x.1.bits,x.2)))
  let test:=binaryZero.comp (second Nat.bits Nat.bits)
  let zerocase:=(constant (prodCode Nat.bits Nat.bits) Nat.bits 0).pair (first Nat.bits Nat.bits)
  exact (conditional test zerocase raw).congrFun (by
    intro x
    change (if decide (x.2=0) then (0,x.1) else divideRaw (x.1.bits,x.2))=(x.1/x.2,x.1%x.2)
    by_cases hz : x.2=0
    · simp [hz]
    · simp only [hz,decide_false,Bool.false_eq_true,ite_false, if_false]
      simpa only [binaryValue_bits] using divideRaw_spec (x.1.bits,x.2) (by omega))

noncomputable def binaryDiv : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1/x.2) := (first Nat.bits Nat.bits).comp binaryDivMod
noncomputable def binaryMod : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1%x.2) := (second Nat.bits Nat.bits).comp binaryDivMod
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackIntegers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def intData (z : ℤ) : Bool×ℕ := (decide (z<0),z.natAbs)
def intCode (z : ℤ) : List Bool := prodCode Procedure.boolCode Nat.bits (intData z)
def intOfSign (x : Bool×ℕ) : ℤ := if x.1 then -(x.2 : ℤ) else (x.2 : ℤ)

lemma intData_ofSign (x : Bool×ℕ) :
    intData (intOfSign x)=(x.1 && decide (x.2≠0),x.2) := by
  rcases x with ⟨s,n⟩
  cases s <;> simp [intData,intOfSign,Nat.pos_iff_ne_zero]

namespace Procedure
noncomputable def intSign : Procedure intCode boolCode (fun z=>decide (z<0)) :=
  (first boolCode Nat.bits).precompose intData
noncomputable def intAbs : Procedure intCode Nat.bits Int.natAbs :=
  (second boolCode Nat.bits).precompose intData

noncomputable def signedInt : Procedure (prodCode boolCode Nat.bits) intCode intOfSign := by
  let s:=first boolCode Nat.bits
  let a:=second boolCode Nat.bits
  let nz:=boolNot.comp (binaryZero.comp a)
  exact ((boolAnd.comp (s.pair nz)).pair a).result (by
    intro x
    change prodCode boolCode Nat.bits (x.1 && !decide (x.2=0),x.2)=intCode (intOfSign x)
    rw [intCode,intData_ofSign]
    simp only [decide_not])

noncomputable def natToInt : Procedure Nat.bits intCode (fun n=>(n : ℤ)) :=
  (signedInt.comp ((constant Nat.bits boolCode false).pair (identity Nat.bits))).congrFun (by intro n;rfl)

end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackGCD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def gcdStep (x : ℕ×ℕ) : ℕ×ℕ := if x.2=0 then x else (x.2,x.1%x.2)
def gcdRound (x : ℕ×ℕ) : ℕ×ℕ := gcdStep (gcdStep x)

lemma gcdStep_value (x : ℕ×ℕ) : (gcdStep x).1.gcd (gcdStep x).2=x.1.gcd x.2 := by
  unfold gcdStep
  split
  · rfl
  · dsimp only
    rw [Nat.gcd_comm x.2]
    exact (Nat.gcd_rec x.2 x.1).symm.trans (Nat.gcd_comm x.2 x.1)

lemma mod_half {b r : ℕ} (hr : 0 < r) (hlt : r<b) : b%r≤b/2 := by
  by_cases h : 2*r≤b
  · have ht:=Nat.mod_lt b hr
    omega
  · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega : b-r < r)]
    omega

lemma gcdRound_half (x : ℕ×ℕ) : (gcdRound x).2≤x.2/2 := by
  by_cases hb : x.2=0
  · simp [gcdRound,gcdStep,hb]
  · have hp : 0<x.2:=by omega
    have hr:=Nat.mod_lt x.1 hp
    by_cases hz : x.1%x.2=0
    · simp [gcdRound,gcdStep,hb,hz]
    · simp only [gcdRound,gcdStep,hb,ite_false, if_false,hz]
      exact mod_half (by omega) hr

lemma gcdRound_value (x : ℕ×ℕ) : (gcdRound x).1.gcd (gcdRound x).2=x.1.gcd x.2 := by
  rw [gcdRound,gcdStep_value,gcdStep_value]

lemma gcdRound_iterate_bound (i : ℕ) (x : ℕ×ℕ) :
    (gcdRound^[i] x).2≤x.2/2^i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    calc
      (gcdRound (gcdRound^[i] x)).2≤(gcdRound^[i] x).2/2:=gcdRound_half _
      _≤(x.2/2^i)/2:=Nat.div_le_div_right ih
      _=x.2/2^(i+1):=by rw [Nat.div_div_eq_div_mul,pow_succ]

lemma gcdRound_iterate_value (i : ℕ) (x : ℕ×ℕ) :
    (gcdRound^[i] x).1.gcd (gcdRound^[i] x).2=x.1.gcd x.2 := by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',gcdRound_value,ih]

lemma gcdRound_result (x : ℕ×ℕ) : (gcdRound^[x.2.bits.length] x).1=x.1.gcd x.2 := by
  have hz : (gcdRound^[x.2.bits.length] x).2=0:=by
    have hh:=gcdRound_iterate_bound x.2.bits.length x
    have hzdiv : x.2/2^x.2.bits.length=0:=by
      rw [Nat.size_eq_bits_len];exact Nat.div_eq_of_lt (Nat.lt_size_self x.2)
    rw [hzdiv] at hh
    omega
  simpa only [hz,Nat.gcd_zero_right] using gcdRound_iterate_value x.2.bits.length x

lemma gcdStep_sizeSum (x : ℕ×ℕ) :
    (gcdStep x).1.bits.length+(gcdStep x).2.bits.length≤x.1.bits.length+x.2.bits.length := by
  have hm:=bits_length_mono (Nat.mod_le x.1 x.2)
  unfold gcdStep
  split
  · exact le_rfl
  · change x.2.bits.length+(x.1%x.2).bits.length≤x.1.bits.length+x.2.bits.length
    omega

lemma gcdRound_iterate_sizeSum (i : ℕ) (x : ℕ×ℕ) :
    (gcdRound^[i] x).1.bits.length+(gcdRound^[i] x).2.bits.length≤
      x.1.bits.length+x.2.bits.length := by
  induction i with
  | zero=>rfl
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    exact ((gcdStep_sizeSum _).trans (gcdStep_sizeSum _)).trans ih


end ExactQuantumFactoring.BitStackProgram
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_ProcedureFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure
noncomputable def gcdStepP : Procedure (prodCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits) gcdStep :=
  (conditional (binaryZero.comp (second Nat.bits Nat.bits))
    (identity (prodCode Nat.bits Nat.bits)) ((second Nat.bits Nat.bits).pair binaryMod)).congrFun
      (by intro x;simp only [gcdStep,Function.comp_apply,id_eq,decide_eq_true_eq])

noncomputable def binaryGcd : Procedure (prodCode Nat.bits Nat.bits) Nat.bits (fun x=>x.1.gcd x.2) := by
  let p:=(gcdStepP.comp gcdStepP).congrFun (g:=gcdRound) (by intro x;rfl)
  let rep:=p.iterate (Polynomial.C 2*Polynomial.X+1) (by
    intro n x i _
    have hh:=gcdRound_iterate_sizeSum i x
    simp only [prodCode,pairBits_length,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let len:=(length.precompose Nat.bits).comp (second Nat.bits Nat.bits)
  exact ((first Nat.bits Nat.bits).comp (rep.comp (len.pair (identity (prodCode Nat.bits Nat.bits))))).congrFun
    (by intro x;exact gcdRound_result x)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackRationals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def ratCode (q : ℚ) : List Bool := prodCode intCode Nat.bits (q.num,q.den)

def ratData (x : ℤ×ℕ) : ℤ×ℕ :=
  if x.2=0 then (0,1) else
    (intOfSign (decide (x.1<0),x.1.natAbs/(x.2.gcd x.1.natAbs)),
      x.2/(x.2.gcd x.1.natAbs))

lemma intOfSign_div (z : ℤ) (d : ℕ) (hd : d∣z.natAbs) :
    intOfSign (decide (z<0),z.natAbs/d)=z/(d : ℤ) := by
  by_cases h : z<0
  · have hz := Int.eq_neg_natAbs_of_nonpos (le_of_lt h)
    have hdiv : (d : ℤ) ∣ (z.natAbs : ℤ) := Int.ofNat_dvd.mpr hd
    simp only [h,decide_true,intOfSign,ite_true, if_true]
    conv_rhs => rw [hz,Int.neg_ediv_of_dvd hdiv]
    rw [Int.natCast_ediv]
  · simp only [h,decide_false,intOfSign,Bool.false_eq_true,ite_false, if_false]
    conv_rhs => rw [←Int.natAbs_of_nonneg (le_of_not_gt h)]
    rw [Int.natCast_ediv]

lemma ratData_spec (x : ℤ×ℕ) : ratData x=((mkRat x.1 x.2).num,(mkRat x.1 x.2).den) := by
  rw [Rat.num_mkRat,Rat.den_mkRat]
  unfold ratData
  split
  · rfl
  · rw [intOfSign_div _ _ (Nat.gcd_dvd_right _ _)]

namespace Procedure
noncomputable def ratNum : Procedure ratCode intCode Rat.num :=
  (first intCode Nat.bits).precompose (fun q : ℚ=>(q.num,q.den))
noncomputable def ratDen : Procedure ratCode Nat.bits Rat.den :=
  (second intCode Nat.bits).precompose (fun q : ℚ=>(q.num,q.den))

noncomputable def makeRat : Procedure (prodCode intCode Nat.bits) ratCode
    (fun x=>mkRat x.1 x.2) := by
  let n:=first intCode Nat.bits
  let d:=second intCode Nat.bits
  let a:=intAbs.comp n
  let g:=binaryGcd.comp (d.pair a)
  let num:=signedInt.comp ((intSign.comp n).pair (binaryDiv.comp (a.pair g)))
  let den:=binaryDiv.comp (d.pair g)
  let zero:=constant (prodCode intCode Nat.bits) (prodCode intCode Nat.bits) (0,1)
  let p:=conditional (binaryZero.comp d) zero (num.pair den)
  exact p.result (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq]
    change prodCode intCode Nat.bits (ratData x)=ratCode (mkRat x.1 x.2)
    rw [ratData_spec];rfl)

noncomputable def intToRat : Procedure intCode ratCode (fun z=>(z : ℚ)) :=
  (makeRat.comp ((identity intCode).pair (constant intCode Nat.bits 1))).congrFun (by
    intro z; simp [Rat.mkRat_eq_div])
noncomputable def natToRat : Procedure Nat.bits ratCode (fun n=>(n : ℚ)) :=
  (intToRat.comp natToInt).congrFun (by intro n;simp)

end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackRationalDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def ratInv : Procedure ratCode ratCode (fun q=>q⁻¹):=by
  let num:=signedInt.comp ((intSign.comp ratNum).pair ratDen)
  let den:=intAbs.comp ratNum
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro q
    change mkRat (intOfSign (decide (q.num<0),q.den)) q.num.natAbs=q⁻¹
    rw [Rat.mkRat_eq_div]
    by_cases h:q.num<0
    · have hz:=Int.eq_neg_natAbs_of_nonpos h.le
      simp only [h,decide_true,intOfSign,ite_true, if_true,Int.cast_neg,Int.cast_natCast]
      conv_rhs=>rw [←Rat.num_div_den q,hz]
      simp only [Int.cast_neg,Int.cast_natCast,neg_div,inv_neg,inv_div]
    · have hz:=Int.natAbs_of_nonneg (le_of_not_gt h)
      simp only [h,decide_false,intOfSign,Bool.false_eq_true,ite_false, if_false,Int.cast_natCast]
      conv_rhs=>rw [←Rat.num_div_den q,←hz]
      simp only [inv_div,Int.cast_natCast])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BinaryRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded binary-root search required by the appendix's perfect-power check.
The search uses only comparisons and powers with exponent at most the input
bit bound; no unbounded Nat.nthRoot primitive is used by the algorithm. -/
namespace ExactQuantumFactoring.Primality

def rootSearch (m e : ℕ) : (k guess : ℕ) → ℕ
  | 0, guess => guess
  | k+1, guess =>
      let next := guess+2^k
      rootSearch m e k (if next^e ≤ m then next else guess)

def boundedRoot (m e n : ℕ) : ℕ := rootSearch m e n 0

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def sumCode {α β : Type} (ea : α→List Bool) (eb : β→List Bool) : α⊕β→List Bool
  | .inl a=>false::ea a
  | .inr b=>true::eb b

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
    {f : α→γ} {g : β→γ}
noncomputable def casesSum (p : Procedure ea ec f) (q : Procedure eb ec g) :
    Procedure (sumCode ea eb) ec (Sum.elim f g) where
  K:=(p.K ⊕ q.K) ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.cases (Sum.inr 0) .skip
    (p.shared.program.relabel (leftPublic p.K q.K))
    (q.shared.program.relabel (rightPublic p.K q.K))
  bound:=p.shared.bound+q.shared.bound+1
  runs x:=by
    cases x with
    | inl a=>
      have hpmono:=eval_nat_mono p.shared.bound (Nat.le_succ (ea a).length)
      obtain ⟨c,hc,hd⟩:=p.shared.runs a
      have hh:=hd.relabel (leftPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : leftPublic p.K q.K p.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hpmono).trans (Nat.le_add_right _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (false::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu,sumCode] using Runs.cases_false (p:=Program.skip)
          (r:=q.shared.program.relabel (rightPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (false::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
    | inr b=>
      have hqmono:=eval_nat_mono q.shared.bound (Nat.le_succ (eb b).length)
      obtain ⟨c,hc,hd⟩:=q.shared.runs b
      have hh:=hd.relabel (rightPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : rightPublic p.K q.K q.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hqmono).trans (Nat.le_add_left _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (true::eb b)) (Sum.inr 0) (eb b)=singletonStore (Sum.inr 0) (eb b):=by
          simp [singletonStore]
        simpa only [hu,sumCode] using Runs.cases_true (p:=Program.skip)
          (q:=p.shared.program.relabel (leftPublic p.K q.K))
          (xs:=eb b) (s:=singletonStore (Sum.inr 0) (true::eb b)) (by simp [singletonStore])
          (by rw [hu];exact hh)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackListCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}
def listCode (ea : α→List Bool) : List α→List Bool
  | []=>[false]
  | a::as=>true::pairBits (ea a) (listCode ea as)

def emptyCode (_ : Unit) : List Bool := []

def listView : List α→Unit⊕(α×List α)
  | []=>.inl ()
  | a::as=>.inr (a,as)

lemma listCode_length_cons (ea : α→List Bool) (a : α) (as : List α) :
    (listCode ea (a::as)).length=2*(ea a).length+2+(listCode ea as).length := by
  simp [listCode,pairBits_length];omega

lemma listCode_length_append (ea : α→List Bool) (xs ys : List α) :
    (listCode ea (xs++ys)).length+1=(listCode ea xs).length+(listCode ea ys).length := by
  induction xs with
  | nil=>simp [listCode,Nat.add_comm]
  | cons a as ih=>simp only [List.cons_append,listCode_length_cons];omega

lemma listCode_length_pos (ea : α→List Bool) (xs : List α) : 0<(listCode ea xs).length := by
  cases xs <;> simp [listCode]

lemma list_length_le_code (ea : α→List Bool) (xs : List α) : xs.length≤(listCode ea xs).length := by
  induction xs with
  | nil=>simp
  | cons a as ih=>simp only [List.length_cons,listCode_length_cons];omega

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listUncons : Procedure (listCode ea)
    (sumCode emptyCode (prodCode ea (listCode ea))) listView :=
  (identity (listCode ea)).result (by intro xs;cases xs <;> rfl)

noncomputable def listHead (d : α) : Procedure (listCode ea) ea (fun xs=>xs.headD d) :=
  ((casesSum (constant emptyCode ea d) (first ea (listCode ea))).comp (listUncons ea)).congrFun
    (by intro xs;cases xs <;> rfl)

noncomputable def listTail : Procedure (listCode ea) (listCode ea) List.tail :=
  ((casesSum (constant emptyCode (listCode ea) []) (second ea (listCode ea))).comp
    (listUncons ea)).congrFun (by intro xs;cases xs <;> rfl)

noncomputable def listEmpty : Procedure (listCode ea) boolCode List.isEmpty :=
  ((casesSum (constant emptyCode boolCode true) (constant (prodCode ea (listCode ea)) boolCode false)).comp
    (listUncons ea)).congrFun (by intro xs;cases xs <;> rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackListFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

def listScan (f : α×β→β) : List α×β→List α×β
  | ([],b)=>([],b)
  | (a::as,b)=>(as,f (a,b))

lemma listScan_iterate (f : α×β→β) (i : ℕ) (xs : List α) (b : β) :
    (listScan f)^[i] (xs,b)=(xs.drop i,(xs.take i).foldl (fun b a=>f (a,b)) b) := by
  induction i generalizing xs b with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil=>simpa [listScan] using ih [] b
    | cons a as=>simpa [listScan] using ih as (f (a,b))

lemma listCode_length_drop_le (ea : α→List Bool) (i : ℕ) (xs : List α) :
    (listCode ea (xs.drop i)).length≤(listCode ea xs).length := by
  have hh:=listCode_length_append ea (xs.take i) (xs.drop i)
  rw [List.take_append_drop] at hh
  have hp:=listCode_length_pos ea (xs.take i)
  omega

namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {f : α×β→β}
noncomputable def listScanP (d : α) (p : Procedure (prodCode ea eb) eb f) :
    Procedure (prodCode (listCode ea) eb) (prodCode (listCode ea) eb) (listScan f) := by
  let xs:=first (listCode ea) eb
  let b:=second (listCode ea) eb
  let upd:=((listTail ea).comp xs).pair (p.comp (((listHead ea d).comp xs).pair b))
  exact ((choose upd (identity (prodCode (listCode ea) eb))).comp
    (((listEmpty ea).comp xs).pair (identity (prodCode (listCode ea) eb)))).congrFun
      (by rintro ⟨xs,b⟩;cases xs <;> rfl)

noncomputable def foldList (d : α) (p : Procedure (prodCode ea eb) eb f)
    (bound : Polynomial ℕ)
    (hsize : ∀ (xs : List α) b i,
      (eb ((xs.take i).foldl (fun b a=>f (a,b)) b)).length≤
        bound.eval ((listCode ea xs).length+(eb b).length)) :
    Procedure (prodCode (listCode ea) eb) eb (fun x=>x.1.foldl (fun b a=>f (a,b)) x.2) := by
  let s:=listScanP d p
  let rep:=s.iterate (Polynomial.C 2*Polynomial.X+1+bound) (by
    intro n x i _
    rw [listScan_iterate]
    simp only [prodCode,pairBits_length]
    have hs:=hsize x.1 x.2 i
    have hl:=listCode_length_drop_le ea i x.1
    have hm:=eval_nat_mono bound (by omega :
      (listCode ea x.1).length+(eb x.2).length≤n+(2*(listCode ea x.1).length+(eb x.2).length+1))
    dsimp only at hm
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let wc:=(length.precompose (listCode ea)).comp (first (listCode ea) eb)
  exact ((second (listCode ea) eb).comp (rep.comp (wc.pair (identity (prodCode (listCode ea) eb))))).congrFun
    (by
      rintro ⟨xs,b⟩
      change ((listScan f)^[(listCode ea xs).length] (xs,b)).2=xs.foldl (fun b a=>f (a,b)) b
      rw [listScan_iterate,List.take_of_length_le (list_length_le_code ea xs)])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackListLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
lemma fold_count (xs : List α) (n : ℕ) : xs.foldl (fun n _=>n+1) n=n+xs.length := by
  induction xs generalizing n with
  | nil=>simp
  | cons a as ih=>simp only [List.foldl_cons,ih,List.length_cons];omega
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_NativeAIGAddWrapper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

namespace Emission
noncomputable def listUnaryLength {α : Type} (ea : α→List Bool) (d : α) :
    Procedure (listCode ea) unaryCode List.length := by
  let step:=unarySuccessor.comp (second ea unaryCode)
  let rep:=foldList d step Polynomial.X (by
    intro xs n i
    change (unaryCode ((xs.take i).foldl (fun n _=>n+1) n)).length≤_
    rw [fold_count]
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X,List.length_take]
    have hh:=list_length_le_code ea xs
    omega)
  let start:=(identity (listCode ea)).pair (Procedure.constant (listCode ea) unaryCode 0)
  exact (rep.comp start).congrFun (by
    intro xs;simpa only [Function.comp_apply,id_eq,Nat.zero_add] using fold_count xs 0)
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SquareRootProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bitwise integer square-root search and its actual polynomial-time
Boolean-stack implementation. This supplies arithmetic for finite-precision
geometric constants and mediator amplitudes without a real square-root oracle. -/

namespace ContinuumCoulomb.SquareRootProgram
open ExactQuantumFactoring.BitStackProgram

def root (m : ℕ) : ℕ :=
  ExactQuantumFactoring.Primality.boundedRoot m 2 m.bits.length

end ContinuumCoulomb.SquareRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_DyadicRootProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computed dyadic square root of a nonnegative rational, with strict
error below one unit in the requested binary precision. Precision is unary;
numerator, denominator, and result are binary. -/

namespace ContinuumCoulomb.DyadicRootProgram
open ExactQuantumFactoring.BitStackProgram

def value (b N F : ℕ) : ℚ :=
  (SquareRootProgram.root (N * (2 ^ b) ^ 2 / F) : ℚ) / (2 : ℚ) ^ b

end ContinuumCoulomb.DyadicRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RationalQuadratureProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal tabulation and summation of rational quadrature samples.
The sample count is unary; bounds, spacing and evaluator data are encoded
as ordinary inputs to the machine. -/

namespace ContinuumCoulomb.RationalQuadratureProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators

variable {E : Type}

abbrev Environment (E : Type) := E × (ℚ × ℚ)
abbrev Input (E : Type) := ℕ × Environment E

def environmentCode (ce : E → List Bool) : Environment E → List Bool :=
  prodCode ce (prodCode ratCode ratCode)

def inputCode (ce : E → List Bool) : Input E → List Bool :=
  prodCode unaryCode (environmentCode ce)

def node (a h : ℚ) (i : ℕ) : ℚ := a + (i : ℚ) * h

def sample (evaluate : E → ℚ → ℚ) (e : Environment E) (i : ℕ) : ℚ :=
  evaluate e.1 (node e.2.1 e.2.2 i)

def value (evaluate : E → ℚ → ℚ) (x : Input E) : ℚ :=
  x.2.2.2 * ∑ i ∈ Finset.range x.1, sample evaluate x.2 i

theorem range_sum (f : ℕ → ℚ) (N : ℕ) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, Finset.sum_range_succ, ih]

end ContinuumCoulomb.RationalQuadratureProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RationalRectangleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal two-coordinate rational quadrature. The same mesh in both
coordinates is enough for the normalization and compact contact integrals. -/

namespace ContinuumCoulomb.RationalRectangleProgram
open ExactQuantumFactoring.BitStackProgram

variable {E : Type}
abbrev Input (E : Type) := RationalQuadratureProgram.Input E

def inputCode (ce : E → List Bool) : Input E → List Bool :=
  RationalQuadratureProgram.inputCode ce

def lineInput (x : Input E × ℚ) : RationalQuadratureProgram.Input (E × ℚ) :=
  (x.1.1, ((x.1.2.1, x.2), x.1.2.2))

def line (evaluate : E → ℚ → ℚ → ℚ) (e : Input E) (x : ℚ) : ℚ :=
  RationalQuadratureProgram.value (fun q y => evaluate q.1 q.2 y) (lineInput (e, x))

def outerInput (x : Input E) : RationalQuadratureProgram.Input (Input E) :=
  (x.1, (x, x.2.2))

def value (evaluate : E → ℚ → ℚ → ℚ) (x : Input E) : ℚ :=
  RationalQuadratureProgram.value (line evaluate) (outerInput x)

end ContinuumCoulomb.RationalRectangleProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalTripleQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three-coordinate rational cubature, using the already proved literal
one- and two-coordinate summation programs. -/

namespace ContinuumCoulomb.RationalTripleQuadrature
open ExactQuantumFactoring.BitStackProgram

variable {E : Type}
abbrev Input (E : Type) := RationalQuadratureProgram.Input E
abbrev Evaluator (E : Type) := E → ℚ → ℚ → ℚ → ℚ

def augment (x : Input E) (a : ℚ) : Input (E×ℚ) :=
  (x.1,((x.2.1,a),x.2.2))

def remember (x : Input E) : Input (Input E) := (x.1,(x,x.2.2))

def inner (f : Evaluator E) (e : E×ℚ) (b c : ℚ) : ℚ := f e.1 e.2 b c

def outer (f : Evaluator E) (x : Input E) (a : ℚ) : ℚ :=
  RationalRectangleProgram.value (inner f) (augment x a)

def value (f : Evaluator E) (x : Input E) : ℚ :=
  RationalQuadratureProgram.value (outer f) (remember x)

end ContinuumCoulomb.RationalTripleQuadrature

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalSquareRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified evaluation of square roots of nonnegative rational samples.
The same finite dyadic procedure serves the fixed Gaussian constants and
softened Coulomb distances. -/

namespace ContinuumCoulomb.RationalSquareRoot
open ExactQuantumFactoring.BitStackProgram

def value (x : ℕ × ℚ) : ℚ :=
  DyadicRootProgram.value x.1 x.2.num.toNat x.2.den

end ContinuumCoulomb.RationalSquareRoot

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CappedKernelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal rational approximation of the bounded three-dimensional
Coulomb kernel. Only a dyadic square root and rational arithmetic occur. -/

noncomputable section
namespace ContinuumCoulomb.CappedKernelProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Triple := ℚ × (ℚ × ℚ)
abbrev Input := (ℕ × ℚ) × Triple

def normSquare (q : Triple) : ℚ := q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2

def approximate (x : Input) : ℚ :=
  (max x.1.2 (RationalSquareRoot.value (x.1.1, normSquare x.2)))⁻¹

def tripleCode : Triple → List Bool := prodCode ratCode (prodCode ratCode ratCode)

end ContinuumCoulomb.CappedKernelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabOriginValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual rational cubature of the scalar slab shift. -/

noncomputable section
namespace ContinuumCoulomb.SlabOriginValue
open ExactQuantumFactoring.BitStackProgram

abbrev Parameters := (ℕ × ℚ) × (ℚ × ℚ)
abbrev Input := RationalTripleQuadrature.Input Parameters

def sample (e : Parameters) (x y z : ℚ) : ℚ :=
  CappedKernelProgram.approximate (e.1,(e.2.1*x,(e.2.1*y,e.2.2*z)))

def value (rho : ℚ) (x : Input) : ℚ :=
  -rho*x.2.1.2.1^2*x.2.1.2.2*RationalTripleQuadrature.value sample x

end ContinuumCoulomb.SlabOriginValue

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PiProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational polynomial-time approximation to π from the integral of
`4 / (1+x²)` on `[0,1]`. The unary sample count gives absolute error `8/N`.
This supplies the normalizing constant in the heat-kernel evaluator. -/

namespace ContinuumCoulomb.PiProgram
open ExactQuantumFactoring.BitStackProgram
open RationalQuadratureProgram

def evaluate (_ : ℚ) (q : ℚ) : ℚ := (1 + q ^ 2)⁻¹

def input (N : ℕ) : Input ℚ := (N, 0, 0, (N : ℚ)⁻¹)

def approximate (N : ℕ) : ℚ := 4 * value evaluate (input N)

end ContinuumCoulomb.PiProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PlanarForcingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational evaluation of the actual compact planar forcing.
Only rational arithmetic and a sign test occur. -/

namespace ContinuumCoulomb.PlanarForcingProgram
open ExactQuantumFactoring.BitStackProgram

def value (q : ℚ × ℚ) : ℚ := max (1 - (q.1 ^ 2 + q.2 ^ 2)) 0 ^ 16

end ContinuumCoulomb.PlanarForcingProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational Taylor approximation with an explicit magnitude and binary
precision parameter. This applies to the negative rational exponents in
the Gaussian heat kernel as well as to positive arguments. -/

open scoped BigOperators
namespace ContinuumCoulomb.RationalExponential

def order (M p : ℕ) : ℕ := 2 * (2 * M ^ 2 + p + 2)

def taylorSum (q : ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, q ^ j / (j.factorial : ℚ)

def approximate (M p : ℕ) (q : ℚ) : ℚ := taylorSum q (order M p)

end ContinuumCoulomb.RationalExponential

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RationalExponentialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial-time rational exponential evaluator. Magnitude and
precision bounds are supplied in unary; the rational argument and result
are encoded in binary. Every arithmetic operation is an actual stack
program, including the shared-denominator Taylor recurrence. -/

namespace ContinuumCoulomb.RationalExponentialProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ℕ × (ℕ × ℚ)

def approximate (x : Input) : ℚ := RationalExponential.approximate x.1 x.2.1 x.2.2

end ContinuumCoulomb.RationalExponentialProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalHeatSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual rational evaluation of the heat-resolvent integrand. Both π and
the exponential are computed by rational approximation programs.
Clamping the computed π below by one keeps every denominator quantitative. -/

namespace ContinuumCoulomb.RationalHeatSample
open ExactQuantumFactoring.BitStackProgram

def safePi (N : ℕ) : ℚ := max 1 (PiProgram.approximate N)

abbrev Point := ℚ × ℚ
abbrev Arguments := ℚ × (Point × Point)
abbrev Settings := ℕ × (ℕ × ℕ)
abbrev Input := Settings × Arguments

def exponent (a : Arguments) : ℚ :=
  -a.1 - ((a.2.1.1 - a.2.2.1) ^ 2 + (a.2.1.2 - a.2.2.2) ^ 2) / (4 * a.1)

def value (x : Input) : ℚ :=
  RationalExponential.approximate x.1.1 x.1.2.1 (exponent x.2) *
    PlanarForcingProgram.value x.2.2.2 / (4 * safePi x.1.2.2 * x.2.1)

end ContinuumCoulomb.RationalHeatSample

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalHeatBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three literal nested quadratures for the heat representation of the
planar resolvent. The two spatial integrals run over `[-1,1]`, which
contains the support of the forcing. All sample counts are unary. -/

namespace ContinuumCoulomb.RationalHeatBox
open ExactQuantumFactoring.BitStackProgram
open RationalHeatSample

abbrev Settings := RationalHeatSample.Settings × (Point × ℕ)
abbrev PlaneEnvironment := Settings × ℚ
abbrev LineEnvironment := PlaneEnvironment × ℚ

def sample (e : LineEnvironment) (y₂ : ℚ) : ℚ :=
  RationalHeatSample.value (e.1.1.1, e.1.2, e.1.1.2.1, e.2, y₂)

def lineInput (e : PlaneEnvironment) (y₁ : ℚ) : RationalQuadratureProgram.Input LineEnvironment :=
  (e.1.2.2, (e, y₁), -1, 2 / (e.1.2.2 : ℚ))

def line (e : PlaneEnvironment) (y₁ : ℚ) : ℚ :=
  RationalQuadratureProgram.value sample (lineInput e y₁)

def planeInput (e : Settings) (t : ℚ) : RationalQuadratureProgram.Input PlaneEnvironment :=
  (e.2.2, (e, t), -1, 2 / (e.2.2 : ℚ))

def plane (e : Settings) (t : ℚ) : ℚ :=
  RationalQuadratureProgram.value line (planeInput e t)

abbrev Input := RationalQuadratureProgram.Input Settings

def value (x : Input) : ℚ := RationalQuadratureProgram.value plane x

end ContinuumCoulomb.RationalHeatBox

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ResolventSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-sized mesh and precision choices for the resolvent
quadrature. The radius and requested inverse accuracy are unary inputs. -/

namespace ContinuumCoulomb.ResolventSchedule
open ExactQuantumFactoring.BitStackProgram

def scale (P : ℕ) : ℕ := 16 * (P + 1)
def countPrefix (R : ℕ) : ℕ := 4096 * (R + 3) ^ 4
def count (R P : ℕ) : ℕ := countPrefix R * scale P ^ 8
def magnitude (R P : ℕ) : ℕ := (R + 3) ^ 2 * scale P
def precision (P : ℕ) : ℕ := 4 * scale P

abbrev Input := (ℕ × ℕ) × RationalHeatSample.Point

def argument (x : Input) : RationalHeatBox.Input :=
  let R := x.1.1
  let P := x.1.2
  let N := count R P
  let Q := (scale P : ℚ)
  (N, (((magnitude R P, (precision P, N)), (x.2, N)), (Q⁻¹, (Q - Q⁻¹) / N)))

def approximate (x : Input) : ℚ := RationalHeatBox.value (argument x)

noncomputable opaque mulProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => x.1 * x.2) := Procedure.unaryMul

noncomputable opaque addProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => x.1 + x.2) := Procedure.unaryAdd

noncomputable opaque squareProgram : Procedure unaryCode unaryCode (fun n => n ^ 2) :=
  (mulProgram.comp ((Procedure.identity unaryCode).pair (Procedure.identity unaryCode))).congrFun
    (by intro n; exact (pow_two n).symm)

end ContinuumCoulomb.ResolventSchedule

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabOriginSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial unary precision choices for the finite-slab scalar. -/

namespace ContinuumCoulomb.SlabOriginSchedule

abbrev Input := ℕ × (ℕ × ℕ)

def capDenominator (rho P : ℕ) : ℕ := 16*(rho+1)*(P+1)
def boxWeight (rho H S : ℕ) : ℕ := (rho+1)*(H+1)^2*(S+1)*(H+S+1)
def count (rho : ℕ) (x : Input) : ℕ :=
  128*boxWeight rho x.2.1 x.2.2*(x.1+1)*(capDenominator rho x.1)^2

end ContinuumCoulomb.SlabOriginSchedule

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabBoxSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational slab dimensions with separate unary magnitude bounds. This
covers exactly the half-cell boundary of the odd centered grid. -/

noncomputable section
namespace ContinuumCoulomb.SlabBoxSchedule

abbrev Input := SlabOriginSchedule.Input × (ℚ×ℚ)

def input (rho : ℕ) (x : Input) : SlabOriginValue.Input :=
  (SlabOriginSchedule.count rho x.1,
    (((SlabOriginSchedule.count rho x.1,
      (SlabOriginSchedule.capDenominator rho x.1.1:ℚ)⁻¹),x.2),
      (-1,2/(SlabOriginSchedule.count rho x.1:ℚ))))

def value (rho : ℕ) (x : Input) : ℚ := SlabOriginValue.value (rho:ℚ) (input rho x)

/-- Exact half-width of the slab covered by centered indices from -q to q. -/
def centeredWidth (q N : ℕ) : ℚ := ((q:ℚ)+1/2)/N

def centered (P N H S : ℕ) : Input :=
  ((P,(H+1,S+1)),(centeredWidth H N,centeredWidth S N))

end ContinuumCoulomb.SlabBoxSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GaussianFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified approximation of the manuscript's actual transverse frequency
`sqrt (4*pi*rho)`. The integer density is fixed once for the construction;
it is not assumed that the resulting frequency is rational. -/

noncomputable section
namespace ContinuumCoulomb.GaussianFrequency
open scoped BigOperators

def frequency (rho : ℕ) : ℝ := Real.sqrt (4 * Real.pi * (rho : ℝ))

def count (rho P : ℕ) : ℕ := 512 * (rho + 1) * (P + 1) ^ 2

def precision (P : ℕ) : ℕ := 8 * (P + 1)

def radicand (rho P : ℕ) : ℚ := 4 * (rho : ℚ) * PiProgram.approximate (count rho P)

def approximate (rho P : ℕ) : ℚ := RationalSquareRoot.value (precision P, radicand rho P)

end ContinuumCoulomb.GaussianFrequency

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredPhysicalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical threshold reference for the exact half-cell boundary of the
centered grid. The finite threshold is scaled by lambda and the true rational
slab reference by lambda squared times the electron count. -/

noncomputable section
namespace ContinuumCoulomb.CenteredPhysicalThreshold

abbrev Geometry := ℕ × (ℕ × ℕ)
abbrev Input := Geometry × (ℕ × (ℕ × (ℚ × ℚ)))

def amplification (rho mesh : ℕ) : ℚ := 8*(mesh:ℚ)^3/rho

def precision (x : Input) : ℕ :=
  8*(8*x.1.1^3+1)^2*(x.2.1+1)*(x.2.2.1+1)

def reference (rho : ℕ) (x : Input) : ℚ :=
  SlabBoxSchedule.value rho (SlabBoxSchedule.centered (precision x) x.1.1 x.1.2.1 x.1.2.2)+
    (GaussianFrequency.approximate rho (precision x)-1)/2

def offset (rho : ℕ) (x : Input) : ℚ :=
  amplification rho x.1.1^2*x.2.1*reference rho x

def value (rho : ℕ) (x : Input) : ℚ×ℚ :=
  (offset rho x+amplification rho x.1.1*x.2.2.2.1,
   offset rho x+amplification rho x.1.1*x.2.2.2.2)

end ContinuumCoulomb.CenteredPhysicalThreshold

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CenteredPhysicalThresholdProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time arithmetic for the complete physical threshold pair. -/

namespace ContinuumCoulomb.CenteredPhysicalThreshold
open ExactQuantumFactoring.BitStackProgram

def geometryCode : Geometry → List Bool := prodCode unaryCode (prodCode unaryCode unaryCode)
def metadataCode : (ℕ×(ℕ×(ℚ×ℚ))) → List Bool :=
  prodCode unaryCode (prodCode unaryCode (prodCode ratCode ratCode))
def inputCode : Input → List Bool := prodCode geometryCode metadataCode

noncomputable opaque geometryProgram : Procedure inputCode geometryCode Prod.fst := Procedure.first _ _
noncomputable opaque metadataProgram : Procedure inputCode metadataCode Prod.snd := Procedure.second _ _
noncomputable opaque meshProgram : Procedure inputCode unaryCode (fun x => x.1.1) :=
  (Procedure.first _ _).comp geometryProgram
noncomputable opaque electronsProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp metadataProgram
noncomputable opaque restProgram : Procedure inputCode (prodCode unaryCode (prodCode ratCode ratCode))
    (fun x => x.2.2) := (Procedure.second _ _).comp metadataProgram
noncomputable opaque errorProgram : Procedure inputCode unaryCode (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp restProgram

noncomputable opaque meshCubeProgram : Procedure inputCode unaryCode (fun x => x.1.1^3) :=
  (ResolventSchedule.mulProgram.comp
    ((ResolventSchedule.squareProgram.comp meshProgram).pair meshProgram)).congrFun
      (by intro x; dsimp; ring)

end ContinuumCoulomb.CenteredPhysicalThreshold

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform Lipschitz estimate for the actual direct-Coulomb profile. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedCoulombLipschitzConstant (freq : ℝ) : ℝ :=
  localizedAmplitudeBound freq ^ 2 *
    (∫ y in Metric.ball (0 : Position) 1, NeutralAtom.coulombKernel y ^ 2) + 1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedDensityMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite second moment of the actual localized probability density.
It supplies a polynomial finite-box truncation radius, uniformly in the
relative displacement appearing in a direct Coulomb coefficient. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedDensitySecondMoment (freq : ℝ) : ℝ :=
  ∫ x : Position, ‖x‖ ^ 2 * localizedDensity freq 0 x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedRawDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unnormalized packets used by the literal Coulomb quadrature. Squaring
the normalization cancels the Gaussian square root, so the final quotient
uses only the already certified planar mass, frequency and pi evaluators. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedRawMass (freq : ℝ) : ℝ :=
  (∫ r, planarResolventMode r ^ 2) * Real.sqrt (Real.pi / freq)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalSixQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Six-coordinate rational cubature, as three literal rectangle programs.
The same finite mesh is retained in each register environment. -/

namespace ContinuumCoulomb.RationalSixQuadrature
open ExactQuantumFactoring.BitStackProgram

variable {E : Type}
abbrev Pair := ℚ × ℚ
abbrev Input (E : Type) := RationalRectangleProgram.Input E
abbrev Evaluator (E : Type) := E → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ

def pairCode : Pair → List Bool := prodCode ratCode ratCode

def augment (x : Input E) (a b : ℚ) : Input (E × Pair) :=
  (x.1, ((x.2.1, (a, b)), x.2.2))

def remember (x : Input E) : Input (Input E) := (x.1, (x, x.2.2))

def inner (f : Evaluator E) (e : (E × Pair) × Pair) (a b : ℚ) : ℚ :=
  f e.1.1 e.1.2.1 e.1.2.2 e.2.1 e.2.2 a b

def middle (f : Evaluator E) (x : Input (E × Pair)) (a b : ℚ) : ℚ :=
  RationalRectangleProgram.value (inner f) (augment x a b)

def outer (f : Evaluator E) (x : Input E) (a b : ℚ) : ℚ :=
  RationalRectangleProgram.value (middle f) (remember (augment x a b))

def value (f : Evaluator E) (x : Input E) : ℚ :=
  RationalRectangleProgram.value (outer f) (remember x)

noncomputable opaque rememberProgram (ce : E → List Bool) :
    Procedure (RationalRectangleProgram.inputCode ce)
      (RationalRectangleProgram.inputCode (RationalRectangleProgram.inputCode ce)) remember := by
  let n := Procedure.first unaryCode (RationalQuadratureProgram.environmentCode ce)
  let env := Procedure.second unaryCode (RationalQuadratureProgram.environmentCode ce)
  let mesh := (Procedure.second ce pairCode).comp env
  exact (n.pair ((Procedure.identity (RationalRectangleProgram.inputCode ce)).pair mesh)).congrFun
    (by intro q; rfl)

end ContinuumCoulomb.RationalSixQuadrature

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalClamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal rational clamp preserves approximation error to values in
[0,1]. It keeps numerical density samples nonnegative and bounded. -/

namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram

def rationalUnitClamp (q : ℚ) : ℚ := max 0 (min 1 q)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GaussianPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A certified rational sample of the actual transverse Gaussian. The
frequency is sqrt(4*pi*rho), with rho fixed, and is evaluated internally. -/

noncomputable section
namespace ContinuumCoulomb.GaussianPacket

abbrev Input := (ℕ × ℕ) × ℚ

def frequencyPrecision (R P : ℕ) : ℕ := 16 * (R + 1) ^ 2 * (P + 1)
def exponentialPrecision (P : ℕ) : ℕ := 8 * (P + 1)
def magnitude (rho R : ℕ) : ℕ := (4 * rho + 4) * (R + 1) ^ 2

def exponent (rho : ℕ) (x : Input) : ℚ :=
  -GaussianFrequency.approximate rho (frequencyPrecision x.1.1 x.1.2) * x.2 ^ 2

def argument (rho : ℕ) (x : Input) : RationalExponentialProgram.Input :=
  (magnitude rho x.1.1, (exponentialPrecision x.1.2, exponent rho x))

def approximate (rho : ℕ) (x : Input) : ℚ :=
  rationalUnitClamp (RationalExponentialProgram.approximate (argument rho x))

end ContinuumCoulomb.GaussianPacket

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RawDensitySample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal bounded samples of the actual unnormalized three-dimensional
localized density, including the irrational fixed transverse frequency. -/

noncomputable section
namespace ContinuumCoulomb.RawDensitySample
open ExactQuantumFactoring.BitStackProgram

abbrev Input := (ℕ × ℕ) × CappedKernelProgram.Triple

def planarArgument (x : Input) : ResolventSchedule.Input :=
  ((2 * x.1.1, x.1.2), (x.2.1, x.2.2.1))

def verticalArgument (x : Input) : GaussianPacket.Input := (x.1, x.2.2.2)

def value (rho : ℕ) (x : Input) : ℚ :=
  rationalUnitClamp (ResolventSchedule.approximate (planarArgument x)) ^ 2 *
    GaussianPacket.approximate rho (verticalArgument x)

end ContinuumCoulomb.RawDensitySample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RawCoulombSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal rational sample of the six-coordinate Coulomb integrand.
Both density factors and the capped kernel use the certified programs. -/

noncomputable section
namespace ContinuumCoulomb.RawCoulombSample
open CappedKernelProgram

def difference (x y s : Triple) : Triple :=
  (x.1 - y.1 - s.1, x.2.1 - y.2.1 - s.2.1, x.2.2 - y.2.2 - s.2.2)

def value (rho R P b : ℕ) (ε : ℚ) (s x y : Triple) : ℚ :=
  RawDensitySample.value rho ((R, P), x) * RawDensitySample.value rho ((R, P), y) *
    approximate ((b, ε), difference x y s)

end ContinuumCoulomb.RawCoulombSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_RawCoulombSampleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial programs for the Coulomb samples and their
six-coordinate summation. -/

namespace ContinuumCoulomb.RawCoulombSample
open ExactQuantumFactoring.BitStackProgram CappedKernelProgram

abbrev Settings := (ℕ × ℕ) × ((ℕ × ℚ) × Triple)
abbrev Input := Settings × (Triple × Triple)
abbrev DifferenceInput := (Triple × Triple) × Triple

def settingsCode : Settings → List Bool :=
  prodCode (prodCode unaryCode unaryCode) (prodCode (prodCode unaryCode ratCode) tripleCode)
def inputCode : Input → List Bool := prodCode settingsCode (prodCode tripleCode tripleCode)
def differenceCode : DifferenceInput → List Bool := prodCode (prodCode tripleCode tripleCode) tripleCode

def evaluate (rho : ℕ) (z : Input) : ℚ :=
  value rho z.1.1.1 z.1.1.2 z.1.2.1.1 z.1.2.1.2 z.1.2.2 z.2.1 z.2.2

def sixEvaluator (rho : ℕ) : RationalSixQuadrature.Evaluator Settings :=
  fun e a b c d f g => evaluate rho (e, ((a, b, c), (d, f, g)))

abbrev SixInput := (((Settings × RationalSixQuadrature.Pair) × RationalSixQuadrature.Pair) × ℚ) × ℚ

end ContinuumCoulomb.RawCoulombSample

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual six-coordinate cubature of the finite Coulomb integral. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.RawCoulombSample

def quadratureInput (R P b : ℕ) (ε : ℚ) (s : CappedKernelProgram.Triple) (N : ℕ) :
    RationalSixQuadrature.Input Settings :=
  (N, (((R, P), ((b, ε), s)), (-(R : ℚ), 2 * (R : ℚ) / (N : ℚ))))

end ContinuumCoulomb.RawCoulombSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombQuadratureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial mesh and precision budgets for the six-coordinate
Coulomb quadrature. All varying parameters below are unary naturals. -/

noncomputable section
namespace ContinuumCoulomb.CoulombQuadratureSchedule

def volume (R : ℕ) : ℕ := (2 * R) ^ 6
def lipschitz (F R D : ℕ) : ℕ := (64 + 2 * F * R) * D + D ^ 2
def mesh (F R D S : ℕ) : ℕ := 48 * R * lipschitz F R D * volume R * S
def accuracy (R D S : ℕ) : ℕ := 32 * D * volume R * S
def kernelPrecision (R D S : ℕ) : ℕ := 4 * D ^ 2 * volume R * S

end ContinuumCoulomb.CoulombQuadratureSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombTruncationSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial cap and box schedules. The single natural guard
is fixed by the fixed one-well density; it is not an input or an oracle. -/

noncomputable section
namespace ContinuumCoulomb.CoulombTruncationSchedule

def guard (freq : ℝ) : ℕ := Nat.ceil (max 1
  (max (2 * Real.pi * localizedAmplitudeBound freq ^ 2)
    (2 * localizedDensitySecondMoment freq))) + 1

def scale (P : ℕ) : ℕ := 8 * (P + 1)
def radius (freq : ℝ) (P : ℕ) : ℕ := guard freq * scale P ^ 2

end ContinuumCoulomb.CoulombTruncationSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_NormalizationQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal quadrature of the actual squared resolvent. Each sample is
computed by the fixed Taylor/heat program, with its proved error. -/

namespace ContinuumCoulomb.NormalizationQuadrature
open ExactQuantumFactoring.BitStackProgram

abbrev Settings := ℕ × ℕ
abbrev Input := RationalRectangleProgram.Input Settings

def sample (e : Settings) (a b : ℚ) : ℚ :=
  ResolventSchedule.approximate (e, (a, b)) ^ 2

def value (x : Input) : ℚ := RationalRectangleProgram.value sample x

end ContinuumCoulomb.NormalizationQuadrature

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_NormalizationSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial schedule for the actual normalization integral.
The outer square grows linearly with inverse accuracy; both nested mesh
counts and the inner resolvent accuracy are explicit natural polynomials. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.NormalizationSchedule

irreducible_def radius (P : ℕ) : ℕ := 8192 * (P + 1)
def meshPrefix (P : ℕ) : ℕ := 4096 * radius P ^ 3
def mesh (P : ℕ) : ℕ := meshPrefix P * (P + 1)
def accuracyPrefix (P : ℕ) : ℕ := 48 * radius P ^ 2
def accuracy (P : ℕ) : ℕ := accuracyPrefix P * (P + 1)

def input (P : ℕ) : NormalizationQuadrature.Input :=
  (mesh P, ((2 * radius P, accuracy P),
    (-(radius P : ℚ), (2 * (radius P : ℚ)) / (mesh P : ℚ))))

def approximate (P : ℕ) : ℚ := NormalizationQuadrature.value (input P)

end ContinuumCoulomb.NormalizationSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_NormalizationArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary arithmetic for the explicit normalization quadrature schedule. -/

namespace ContinuumCoulomb.NormalizationSchedule
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque cubeProgram : Procedure unaryCode unaryCode (fun n => n ^ 3) :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.identity unaryCode).pair ResolventSchedule.squareProgram)).congrFun
      (by intro n; dsimp; ring)

end ContinuumCoulomb.NormalizationSchedule

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CoulombNormalizationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A certified rational evaluator for the fixed Coulomb normalization
factor. The natural guard depends only on the fixed one-well model. -/

noncomputable section
namespace ContinuumCoulomb.CoulombNormalization
open ExactQuantumFactoring.BitStackProgram

def guard (freq : ℝ) : ℕ := Nat.ceil (max 1 (max |freq|
  (max (2 / (∫ r, planarResolventMode r ^ 2)) (2 / Real.pi)))) + 1

def coefficient (freq : ℝ) : ℝ := freq / ((∫ r, planarResolventMode r ^ 2) ^ 2 * Real.pi)
def factorBound (C : ℕ) : ℕ := C ^ 3 + 3 * C ^ 5
def precision (rho P : ℕ) : ℕ :=
  (guard (GaussianFrequency.frequency rho) + factorBound (guard (GaussianFrequency.frequency rho))) * (P + 1)

def approximate (rho P : ℕ) : ℚ :=
  GaussianFrequency.approximate rho (precision rho P) /
    (NormalizationSchedule.approximate (precision rho P) ^ 2 *
      PiProgram.approximate (8 * (precision rho P + 1)))

end ContinuumCoulomb.CoulombNormalization

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombEvaluationParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One fixed set of polynomial precision parameters for the actual
localized Coulomb coefficient. Only the requested accuracy varies. -/

noncomputable section
namespace ContinuumCoulomb.CoulombEvaluation

def frequencyBound (rho : ℕ) : ℕ := ⌈GaussianFrequency.frequency rho⌉₊ + 1
def normalizationBound (rho : ℕ) : ℕ :=
  ⌈max 1 (CoulombNormalization.coefficient (GaussianFrequency.frequency rho))⌉₊ + 1
def rawMassBound (rho : ℕ) : ℕ :=
  ⌈localizedRawMass (GaussianFrequency.frequency rho) ^ 2 + 1⌉₊ + 1

def truncationPrecision (P : ℕ) : ℕ := 4 * (P + 1)
def denominator (rho P : ℕ) : ℕ :=
  CoulombTruncationSchedule.guard (GaussianFrequency.frequency rho) *
    CoulombTruncationSchedule.scale (truncationPrecision P)
def radius (rho P : ℕ) : ℕ :=
  CoulombTruncationSchedule.radius (GaussianFrequency.frequency rho) (truncationPrecision P)
def rawPrecision (rho P : ℕ) : ℕ := 4 * normalizationBound rho * (P + 1)
def mesh (rho P : ℕ) : ℕ := CoulombQuadratureSchedule.mesh
  (frequencyBound rho) (radius rho P) (denominator rho P) (rawPrecision rho P)
def samplePrecision (rho P : ℕ) : ℕ := CoulombQuadratureSchedule.accuracy
  (radius rho P) (denominator rho P) (rawPrecision rho P)
def kernelPrecision (rho P : ℕ) : ℕ := CoulombQuadratureSchedule.kernelPrecision
  (radius rho P) (denominator rho P) (rawPrecision rho P)
def normalizationPrecision (rho P : ℕ) : ℕ := 8 * rawMassBound rho * denominator rho P * (P + 1)

def input (rho P : ℕ) (d : ℚ) : RationalSixQuadrature.Input RawCoulombSample.Settings :=
  RawCoulombSample.quadratureInput (radius rho P) (samplePrecision rho P) (kernelPrecision rho P)
    (1 / (denominator rho P : ℚ)) (d, 0, 0) (mesh rho P)

def rawApproximate (rho P : ℕ) (d : ℚ) : ℚ :=
  RationalSixQuadrature.value (RawCoulombSample.sixEvaluator rho) (input rho P d)

def approximate (rho P : ℕ) (d : ℚ) : ℚ :=
  CoulombNormalization.approximate rho (normalizationPrecision rho P) * rawApproximate rho P d

end ContinuumCoulomb.CoulombEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CoulombEvaluationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single polynomial-time TM2 program for the actual localized
Coulomb coefficient at every rational separation and unary precision. -/

namespace ContinuumCoulomb.CoulombEvaluation
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ℕ × ℚ
def inputCode : Input → List Bool := prodCode unaryCode ratCode

noncomputable opaque scaleProgram (k : ℕ) : Procedure unaryCode unaryCode (fun P => k * P) :=
  ResolventSchedule.mulProgram.comp
    ((Procedure.constant unaryCode unaryCode k).pair (Procedure.identity unaryCode))

noncomputable opaque sixthProgram : Procedure unaryCode unaryCode (fun P => P ^ 6) :=
  (ResolventSchedule.squareProgram.comp NormalizationSchedule.cubeProgram).congrFun
    (by intro P; simp only [Function.comp_apply]; ring)

noncomputable opaque truncationPrecisionProgram : Procedure unaryCode unaryCode truncationPrecision :=
  (scaleProgram 4).comp Procedure.unarySuccessor

noncomputable opaque capScaleProgram : Procedure unaryCode unaryCode
    (fun P => CoulombTruncationSchedule.scale (truncationPrecision P)) :=
  ((scaleProgram 8).comp (Procedure.unarySuccessor.comp truncationPrecisionProgram)).congrFun
    (by intro P; rfl)

noncomputable opaque denominatorProgram (rho : ℕ) : Procedure unaryCode unaryCode (denominator rho) :=
  (scaleProgram (CoulombTruncationSchedule.guard (GaussianFrequency.frequency rho))).comp capScaleProgram

noncomputable opaque radiusProgram (rho : ℕ) : Procedure unaryCode unaryCode (radius rho) :=
  ((scaleProgram (CoulombTruncationSchedule.guard (GaussianFrequency.frequency rho))).comp
    (ResolventSchedule.squareProgram.comp capScaleProgram)).congrFun (by intro P; rfl)

noncomputable opaque rawPrecisionProgram (rho : ℕ) : Procedure unaryCode unaryCode (rawPrecision rho) :=
  ((scaleProgram (4 * normalizationBound rho)).comp Procedure.unarySuccessor).congrFun
    (by intro P; rfl)

noncomputable opaque volumeProgram (rho : ℕ) : Procedure unaryCode unaryCode
    (fun P => CoulombQuadratureSchedule.volume (radius rho P)) :=
  (sixthProgram.comp ((scaleProgram 2).comp (radiusProgram rho))).congrFun (by intro P; rfl)

noncomputable opaque lipschitzProgram (rho : ℕ) : Procedure unaryCode unaryCode
    (fun P => CoulombQuadratureSchedule.lipschitz (frequencyBound rho) (radius rho P) (denominator rho P)) := by
  let r := radiusProgram rho
  let d := denominatorProgram rho
  let t := (scaleProgram (2 * frequencyBound rho)).comp r
  let k := ResolventSchedule.addProgram.comp ((Procedure.constant unaryCode unaryCode 64).pair t)
  let kd := ResolventSchedule.mulProgram.comp (k.pair d)
  let dsq := ResolventSchedule.squareProgram.comp d
  exact (ResolventSchedule.addProgram.comp (kd.pair dsq)).congrFun (by intro P; rfl)

noncomputable opaque meshProgram (rho : ℕ) : Procedure unaryCode unaryCode (mesh rho) := by
  let r := (scaleProgram 48).comp (radiusProgram rho)
  let rl := ResolventSchedule.mulProgram.comp (r.pair (lipschitzProgram rho))
  let rlv := ResolventSchedule.mulProgram.comp (rl.pair (volumeProgram rho))
  exact (ResolventSchedule.mulProgram.comp (rlv.pair (rawPrecisionProgram rho))).congrFun
    (by intro P; rfl)

noncomputable opaque samplePrecisionProgram (rho : ℕ) :
    Procedure unaryCode unaryCode (samplePrecision rho) := by
  let d := (scaleProgram 32).comp (denominatorProgram rho)
  let dv := ResolventSchedule.mulProgram.comp (d.pair (volumeProgram rho))
  exact (ResolventSchedule.mulProgram.comp (dv.pair (rawPrecisionProgram rho))).congrFun
    (by intro P; rfl)

noncomputable opaque kernelPrecisionProgram (rho : ℕ) :
    Procedure unaryCode unaryCode (kernelPrecision rho) := by
  let d := (scaleProgram 4).comp (ResolventSchedule.squareProgram.comp (denominatorProgram rho))
  let dv := ResolventSchedule.mulProgram.comp (d.pair (volumeProgram rho))
  exact (ResolventSchedule.mulProgram.comp (dv.pair (rawPrecisionProgram rho))).congrFun
    (by intro P; rfl)

noncomputable opaque normalizationPrecisionProgram (rho : ℕ) :
    Procedure unaryCode unaryCode (normalizationPrecision rho) := by
  let d := (scaleProgram (8 * rawMassBound rho)).comp (denominatorProgram rho)
  exact (ResolventSchedule.mulProgram.comp (d.pair Procedure.unarySuccessor)).congrFun
    (by intro P; rfl)

noncomputable opaque radiusRationalProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => (radius rho x.1 : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp
    ((radiusProgram rho).comp (Procedure.first unaryCode ratCode)))

noncomputable opaque meshRationalProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => (mesh rho x.1 : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp
    ((meshProgram rho).comp (Procedure.first unaryCode ratCode)))

noncomputable opaque epsilonProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => 1 / (denominator rho x.1 : ℚ)) :=
  (Procedure.ratInv.comp (Procedure.natToRat.comp (Procedure.unaryToBits.comp
    ((denominatorProgram rho).comp (Procedure.first unaryCode ratCode))))).congrFun
      (by intro x; simp only [one_div]; rfl)

end ContinuumCoulomb.CoulombEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPairEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual direct Coulomb coefficients at arbitrary rational planar sites.
The distance is computed by the certified dyadic square-root program. -/

noncomputable section
namespace ContinuumCoulomb.CoulombPairEvaluation

def lipschitzGuard (rho : ℕ) : ℕ :=
  ⌈localizedCoulombLipschitzConstant (GaussianFrequency.frequency rho)⌉₊+1

def precision (P : ℕ) : ℕ := 2*(P+1)
def rootPrecision (rho P : ℕ) : ℕ := 4*lipschitzGuard rho*(P+1)
def squaredDistance (a b : ℚ×ℚ) : ℚ := (a.1-b.1)^2+(a.2-b.2)^2
def distance (rho P : ℕ) (a b : ℚ×ℚ) : ℚ :=
  RationalSquareRoot.value (rootPrecision rho P,squaredDistance a b)
def approximate (rho P : ℕ) (a b : ℚ×ℚ) : ℚ :=
  CoulombEvaluation.approximate rho (precision P) (distance rho P a b)

end ContinuumCoulomb.CoulombPairEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CoulombPairProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time rational evaluation of direct Coulomb matrix entries
from their two rational planar coordinates. -/

namespace ContinuumCoulomb.CoulombPairEvaluation
open ExactQuantumFactoring.BitStackProgram

def pointCode : (ℚ×ℚ) → List Bool := prodCode ratCode ratCode
def pairCode : ((ℚ×ℚ)×(ℚ×ℚ)) → List Bool := prodCode pointCode pointCode
abbrev Input := ℕ×((ℚ×ℚ)×(ℚ×ℚ))
def inputCode : Input → List Bool := prodCode unaryCode pairCode

end ContinuumCoulomb.CoulombPairEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPairSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scalar direct-interaction offset is one half of the
ordered off-diagonal Coulomb sum. The finite list evaluator excludes only
identical coordinates; injectivity identifies that test with the diagonal. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.CoulombPairSum

abbrev Point := ℚ×ℚ
abbrev Input := ℕ×List Point

def offsite (rho p : ℕ) (a b : Point) : ℚ :=
  if CoulombPairEvaluation.squaredDistance a b = 0 then 0
  else CoulombPairEvaluation.approximate rho p a b

def row (rho p : ℕ) (a : Point) (sites : List Point) : ℚ :=
  (sites.map (offsite rho p a)).sum

def total (rho p : ℕ) (sites : List Point) : ℚ :=
  (sites.map (fun a => row rho p a sites)).sum/2

def precision (m P : ℕ) : ℕ := (m+1)^2*(P+1)
def value (rho : ℕ) (x : Input) : ℚ := total rho (precision x.2.length x.1) x.2

end ContinuumCoulomb.CoulombPairSum

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CoulombPairSumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The direct-interaction scalar uses two literal finite list traversals;
its precision increases only polynomially with the number of sites. -/

namespace ContinuumCoulomb.CoulombPairSum
open ExactQuantumFactoring.BitStackProgram

def pointCode : Point → List Bool := CoulombPairEvaluation.pointCode
def inputCode : Input → List Bool := prodCode unaryCode (listCode pointCode)
def rowCode : (ℕ×(Point×List Point)) → List Bool :=
  prodCode unaryCode (prodCode pointCode (listCode pointCode))

noncomputable opaque lengthProgram : Procedure inputCode unaryCode (fun x => x.2.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pointCode (0,0)).comp
    (Procedure.second unaryCode (listCode pointCode))

noncomputable opaque precisionProgram : Procedure inputCode unaryCode
    (fun x => precision x.2.length x.1) := by
  let msq := ResolventSchedule.squareProgram.comp (Procedure.unarySuccessor.comp lengthProgram)
  let pp := Procedure.unarySuccessor.comp (Procedure.first unaryCode (listCode pointCode))
  exact (ResolventSchedule.mulProgram.comp (msq.pair pp)).congrFun (by intro x; rfl)

noncomputable opaque argumentProgram : Procedure inputCode inputCode
    (fun x => (precision x.2.length x.1,x.2)) :=
  precisionProgram.pair (Procedure.second unaryCode (listCode pointCode))

end ContinuumCoulomb.CoulombPairSum

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_AffinePhysicalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete scalar shift in the unit-charge construction. Input endpoints
already contain the exact mediator offset. The remaining finite shift is the
sum of edge weights and the off-site Coulomb energy; only the latter and the
one-particle reference require numerical approximation. -/

noncomputable section
namespace ContinuumCoulomb.AffinePhysicalThreshold

abbrev Input := CenteredPhysicalThreshold.Input × (ℚ × (List CoulombPairSum.Point × List ℚ))

def pairPrecision (x : Input) : ℕ :=
  (8*x.1.1.1^3+1)*(2*(x.1.2.2.1+1))

def pairValue (rho : ℕ) (x : Input) : ℚ :=
  CoulombPairSum.value rho (pairPrecision x,x.2.2.1)

def finiteValue (rho : ℕ) (x : Input) : ℚ×ℚ :=
  (x.2.1^2*(x.1.2.2.2.1-x.2.2.2.sum)-pairValue rho x,
   x.2.1^2*(x.1.2.2.2.2-x.2.2.2.sum)-pairValue rho x)

def argument (rho : ℕ) (x : Input) : CenteredPhysicalThreshold.Input :=
  (x.1.1,(x.1.2.1,(2*(x.1.2.2.1+1),finiteValue rho x)))

def value (rho : ℕ) (x : Input) : ℚ×ℚ :=
  CenteredPhysicalThreshold.value rho (argument rho x)

end ContinuumCoulomb.AffinePhysicalThreshold

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_AffinePhysicalThresholdProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-time evaluation of the complete affine threshold shift.
Every precision and loop bound is computed in unary from polynomial metadata. -/

namespace ContinuumCoulomb.AffinePhysicalThreshold
open ExactQuantumFactoring.BitStackProgram

def dataCode : (ℚ×(List CoulombPairSum.Point×List ℚ)) → List Bool :=
  prodCode ratCode (prodCode (listCode CoulombPairSum.pointCode) (listCode ratCode))
def inputCode : Input → List Bool := prodCode CenteredPhysicalThreshold.inputCode dataCode

noncomputable opaque numbersProgram : Procedure inputCode CenteredPhysicalThreshold.inputCode Prod.fst :=
  Procedure.first _ _
noncomputable opaque dataProgram : Procedure inputCode dataCode Prod.snd := Procedure.second _ _
noncomputable opaque listsProgram : Procedure inputCode
    (prodCode (listCode CoulombPairSum.pointCode) (listCode ratCode)) (fun x => x.2.2) :=
  (Procedure.second _ _).comp dataProgram
noncomputable opaque sitesProgram : Procedure inputCode (listCode CoulombPairSum.pointCode)
    (fun x => x.2.2.1) := (Procedure.first _ _).comp listsProgram
noncomputable opaque errorProgram : Procedure inputCode unaryCode (fun x => x.1.2.2.1) :=
  CenteredPhysicalThreshold.errorProgram.comp numbersProgram
noncomputable opaque electronsProgram : Procedure inputCode unaryCode (fun x => x.1.2.1) :=
  CenteredPhysicalThreshold.electronsProgram.comp numbersProgram
noncomputable opaque precisionProgram : Procedure inputCode unaryCode
    (fun x => 2*(x.1.2.2.1+1)) :=
  ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode 2).pair
      (Procedure.unarySuccessor.comp errorProgram))

noncomputable opaque pairPrecisionProgram : Procedure inputCode unaryCode pairPrecision := by
  let cube := CenteredPhysicalThreshold.meshCubeProgram.comp numbersProgram
  let base := Procedure.unarySuccessor.comp (ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode 8).pair cube))
  exact (ResolventSchedule.mulProgram.comp (base.pair precisionProgram)).congrFun
    (by intro x; rfl)

end ContinuumCoulomb.AffinePhysicalThreshold

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalSmoothTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational approximation of the explicit smooth transition. Exponents
near the flat junction are truncated before Taylor evaluation, keeping
both the magnitude parameter and the error polynomial in the precision. -/

namespace ContinuumCoulomb.RationalSmoothTransition

def clip (q : ℚ) : ℚ := max 0 (min 1 q)

def precision (p : ℕ) : ℕ := 1000*(p+1)

end ContinuumCoulomb.RationalSmoothTransition

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_ManufacturedFieldProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial TM2 scalar evaluator for the actual manufactured
three-dimensional well field. All sites, widths and scales are input data. -/

namespace ContinuumCoulomb.ManufacturedFieldEvaluation
open ExactQuantumFactoring.BitStackProgram

def pointCode := CoulombPairEvaluation.pointCode
def sitesCode := listCode pointCode

end ContinuumCoulomb.ManufacturedFieldEvaluation

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_TransformedGaussList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same certified node program is applied to the whole finite list of
Gauss labels. It preserves the nucleus count and, at the proved precision,
pairwise distinctness. -/

open scoped NNReal
namespace ContinuumCoulomb.TransformedGauss
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode )

abbrev Environment := (ℕ×ℕ)×((ℚ×ℚ)×List (ℚ×ℚ))
def environmentCode : Environment → List Bool :=
  prodCode (prodCode unaryCode Nat.bits)
    (prodCode (prodCode ratCode ratCode) ManufacturedFieldEvaluation.sitesCode)

end ContinuumCoulomb.TransformedGauss

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredGaussLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete duplicate-free list of all eight Gauss labels in each cell
of the centered rectangular grid, with the exact polynomial count. -/

namespace ContinuumCoulomb.CenteredGaussLabels

abbrev Radii := ℕ×(ℕ×ℕ)

end ContinuumCoulomb.CenteredGaussLabels

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CenteredGaussProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial generation of the complete rectangular Gauss-label
list. The three integer radii are unary, so the cubic number of output cells
is polynomial in the encoded input size. -/

namespace ContinuumCoulomb.CenteredGaussLabels
open ExactQuantumFactoring.BitStackProgram

def radiiCode : Radii → List Bool := prodCode unaryCode (prodCode unaryCode unaryCode)

end ContinuumCoulomb.CenteredGaussLabels

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_CenteredNuclearProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete finite rational nucleus list, generated from the actual
rectangular cell bounds, numerically transported, and serialized using the
continuum promise's own position codec. -/

open scoped NNReal
namespace ContinuumCoulomb.CenteredNuclearProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := TransformedGauss.Environment×CenteredGaussLabels.Radii
def inputCode : Input → List Bool :=
  prodCode TransformedGauss.environmentCode CenteredGaussLabels.radiiCode

end ContinuumCoulomb.CenteredNuclearProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PhysicalNuclearProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical nuclear coordinates for h=1/N. The exact rational factor is
1/λ=rho/(8N^3), matching the manuscript's y=λx convention. -/

namespace ContinuumCoulomb.PhysicalNuclearProgram
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode )

abbrev Input := CenteredNuclearProgram.Input
def inputCode : Input → List Bool := CenteredNuclearProgram.inputCode

end ContinuumCoulomb.PhysicalNuclearProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_UnitCoulombProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal output codec for a complete unit-charge Coulomb instance.
The electron count is unary, and both rational thresholds are emitted in
canonical numerator/positive-denominator form. -/

namespace ContinuumCoulomb.UnitCoulombProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := PhysicalNuclearProgram.Input×(ℕ×(ℚ×ℚ))

end ContinuumCoulomb.UnitCoulombProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_AffinePhysicalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A canonical unit-charge instance with the complete physical scalar offset.
The coordinate and threshold metadata remain explicit until the source program
supplies the same fixed polynomial scales to both components. -/

namespace ContinuumCoulomb.AffinePhysicalOutput
open ExactQuantumFactoring.BitStackProgram

abbrev Input := PhysicalNuclearProgram.Input × AffinePhysicalThreshold.Input

def inputCode : Input → List Bool :=
  prodCode PhysicalNuclearProgram.inputCode AffinePhysicalThreshold.inputCode

noncomputable def argument (rho : ℕ) (x : Input) : UnitCoulombProgram.Input :=
  (x.1,(x.2.1.2.1,AffinePhysicalThreshold.value rho x.2))

end ContinuumCoulomb.AffinePhysicalOutput

end OAI
end


