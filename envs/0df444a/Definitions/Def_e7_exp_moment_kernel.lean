-- Prove2me | Definitions.Def_e7_exp_moment_kernel
-- name    : e7_exp_moment_kernel
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-06T06:54:14.258496+00:00
-- url     : https://prove2.me/theorems/c6f85edb-cd93-48ff-bbb0-2a3453d94cc4
-- title:
--   e7_exp_moment_kernel
-- statement:
--   Automatically extracted helper definition e7_exp_moment_kernel from oversized parent candidate dcd953a23f725a070ac191cef4ddb58557fddc058de13b87b62b5edcb2f71a48.
-- source:
--   candidate-decomposition:e7f29b55-7342-4ff0-afdb-be23ceaf9cb9:dcd953a23f725a070ac191cef4ddb58557fddc058de13b87b62b5edcb2f71a48

import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem
import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformEmbedding
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

/-!
Truncated exponential substitution for the Laplace moments. The two
integrability premises are local to this change-of-variables bridge; the
target application must discharge them from boundedness of the scalar
forward difference. This remains a research fragment, not an elaborated
candidate.
-/

noncomputable def e7_exp_moment_kernel (d : ℝ → ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  if 0 < y ∧ y ≤ 1 then y ^ k * d (-Real.log y) else 0


