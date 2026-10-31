-- Prove2me | Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
-- name    : MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:45:46.293615+00:00
-- url     : https://prove2.me/theorems/256399fd-114e-49e2-9998-ae7277d2fbb8
-- title:
--   MarkovProcess: MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_Integral_2b459584
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
import Definitions.Def_MarkovProcess_V3H_Kernel_Resolvent_f63a7282
import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Definitions.Def_MarkovProcess_V3H_Semigroup_ContractiveResolvent_4e63c9ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generation_6c19e644
import Definitions.Def_MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
import Definitions.Def_MarkovProcess_V3H_Semigroup_ResolventGeneration_96f24647
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Metrizable.Urysohn

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The resolvent of a Feller kernel semigroup

The resolvent of the `C₀` semigroup of a Feller kernel semigroup `P`, evaluated at a point, is
the Laplace transform of the transition integrals,

  `R_μ f (x) = ∫₀^∞ e^{-μ t} (∫ f d(P t x)) dt`   (`IsFellerKernelSemigroup.resolvent_apply_apply`),

and the generator domain of the `C₀` semigroup is the range of this resolvent
(`IsFellerKernelSemigroup.mem_generatorDomain_iff_exists_resolvent`), the kernel-side reading of
`Semigroup/Resolvent.lean`.  The shared bounded evaluation functional `c0EvalCLM` commutes with
Bochner integrals in `C₀(α, ℝ)`.  For the Feller kernel
semigroup represented by a positive contractive resolvent `R` (`Kernel/PositiveC0Resolvent.lean`),
the resolvent of its `C₀` semigroup is `R` itself
(`PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup`).

Conversely, the kernel semigroup represented by that resolvent is the original one
(`IsFellerKernelSemigroup.kernelSemigroup_positiveC0ContractiveResolvent`).

Main results: `IsFellerKernelSemigroup.resolvent_apply_apply`,
`IsFellerKernelSemigroup.positiveC0ContractiveResolvent`,
`IsFellerKernelSemigroup.kernelResolvent_ofReal_eq_resolvent`,
`IsFellerKernelSemigroup.mem_generatorDomain_iff_exists_resolvent`,
`PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup`.

The bridge to `SubMarkovKernelSemigroup.kernelResolvent` is pointwise on nonnegative observables;
no kernel-valued resolvent is constructed.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ZeroAtInfty

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [LocallyCompactSpace α] [T2Space α]
variable {P : SubMarkovKernelSemigroup α} (hP : P.IsFellerKernelSemigroup)

/-- **The resolvent of the `C₀` semigroup, evaluated at a point**: the Laplace transform of the
transition integrals. -/
theorem IsFellerKernelSemigroup.resolvent_apply_apply (μ : Semigroup.PositiveShift)
    (f : C₀(α, ℝ)) (x : α) :
    hP.c0Semigroup.resolvent μ f x =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(μ : ℝ) * t) * kernelIntegral (P (Real.toNNReal t)) f x := by
  rw [← c0EvalCLM_apply x (hP.c0Semigroup.resolvent μ f),
    Semigroup.StronglyContinuousContractionSemigroup.resolvent_apply,
    ← ContinuousLinearMap.integral_comp_comm _
      (hP.c0Semigroup.integrableOn_laplaceIntegrand μ.2 f)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp only [Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, map_smul,
    c0EvalCLM_apply, smul_eq_mul, IsFellerKernelSemigroup.c0Semigroup_apply_apply]

/-- The resolvent of a Feller kernel semigroup, packaged as a positive contractive resolvent on
`C₀`. Positivity follows directly from the nonnegative Laplace-transform integrand. -/
noncomputable def IsFellerKernelSemigroup.positiveC0ContractiveResolvent :
    PositiveC0ContractiveResolvent α where
  toContractiveResolvent := hP.c0Semigroup.toContractiveResolvent
  isPositive := fun μ f hf x ↦ by
    rw [Semigroup.StronglyContinuousContractionSemigroup.toContractiveResolvent_operator,
      hP.resolvent_apply_apply]
    exact integral_nonneg fun t ↦ mul_nonneg (Real.exp_pos _).le (integral_nonneg hf)

/-- Generating a semigroup from the positive resolvent of a Feller semigroup recovers its
original `C₀` semigroup. -/
theorem IsFellerKernelSemigroup.generatedSemigroup_positiveC0ContractiveResolvent :
    hP.positiveC0ContractiveResolvent.toContractiveResolvent.generatedSemigroup =
      hP.c0Semigroup :=
  hP.c0Semigroup.generatedSemigroup_toContractiveResolvent





/-- **The kernel semigroup represented by the resolvent of a Feller kernel semigroup is that
semigroup.**  Both transition laws are finite Borel measures with the same integral on every
compactly supported continuous observable. -/
theorem IsFellerKernelSemigroup.p2m_embedded_7a36add020ed9fda
    [SecondCountableTopology α] (hP : P.IsFellerKernelSemigroup) :
    hP.positiveC0ContractiveResolvent.kernelSemigroup = P := by
  refine SubMarkovKernelSemigroup.ext fun t ↦ ?_
  refine Kernel.ext fun x ↦ ?_
  have : IsFiniteMeasure (P t x) :=
    ⟨lt_of_le_of_lt (P.measure_univ_le_one t x) ENNReal.one_lt_top⟩
  have : IsFiniteMeasure (hP.positiveC0ContractiveResolvent.kernelSemigroup t x) :=
    ⟨lt_of_le_of_lt
      (hP.positiveC0ContractiveResolvent.kernelSemigroup.measure_univ_le_one t x)
      ENNReal.one_lt_top⟩
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
  set g : C₀(α, ℝ) := PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f with hg
  have hgf : ∀ y, g y = f y := fun y ↦
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply f y
  have hleft : ∫ y, f y ∂hP.positiveC0ContractiveResolvent.kernelSemigroup t x =
      ∫ y, g y ∂hP.positiveC0ContractiveResolvent.kernelSemigroup t x := by
    simp only [hgf]
  have hright : ∫ y, f y ∂P t x = ∫ y, g y ∂P t x := by
    simp only [hgf]
  rw [hleft, hright, hP.positiveC0ContractiveResolvent.integral_kernelSemigroup t g x,
    hP.generatedSemigroup_positiveC0ContractiveResolvent, hP.c0Semigroup_apply_apply t g x]
  rfl



end SubMarkovKernelSemigroup

namespace PositiveC0ContractiveResolvent

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (R : PositiveC0ContractiveResolvent X)



end PositiveC0ContractiveResolvent

end MarkovProcess


