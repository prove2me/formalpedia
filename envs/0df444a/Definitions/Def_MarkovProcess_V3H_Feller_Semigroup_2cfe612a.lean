-- Prove2me | Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
-- name    : MarkovProcess_V3H_Feller_Semigroup_2cfe612a
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:34:50.069208+00:00
-- url     : https://prove2.me/theorems/db3a0e8b-bbc8-4841-8ee8-2a1bceaa8545
-- title:
--   MarkovProcess: MarkovProcess_V3H_Feller_Semigroup_2cfe612a
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_C0_dfad2e28
import Definitions.Def_MarkovProcess_V3H_Kernel_Integral_2b459584
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strongly continuous `C₀` semigroups from kernels

This file isolates continuity in time as an explicit hypothesis on the `C₀` kernel operators and
packages those operators as a strongly continuous contraction semigroup. Spatial preservation of
`C₀`, continuity of its time orbits, and conservativity of the kernels remain separate properties.
No stochastic process or Hunt process is constructed here.
-/

open Topology
open scoped ZeroAtInfty

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]

/-- The `C₀` kernel operators have continuous time orbits in the `C₀` norm. This is an
additional hypothesis beyond the spatial `MapsC0` property. -/
def HasContinuousC0Orbits (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0) : Prop :=
  ∀ f : C₀(α, ℝ), Continuous fun t : NNReal ↦ P.c0Operator hC0 t f

/-- A sub-Markov kernel semigroup on a locally compact Hausdorff space has the `C₀`
Feller-semigroup properties when it maps `C₀` into itself and its resulting `C₀` operator orbits
are continuous in time. Conservativity is not part of this predicate. -/
def IsFellerKernelSemigroup (P : SubMarkovKernelSemigroup α)
    [LocallyCompactSpace α] [T2Space α] : Prop :=
  ∃ hC0 : P.MapsC0, P.HasContinuousC0Orbits hC0

variable (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0)

/-- Package the kernel action on `C₀` as a strongly continuous contraction semigroup. -/
noncomputable def c0Semigroup (hTime : P.HasContinuousC0Orbits hC0) :
    Semigroup.StronglyContinuousContractionSemigroup C₀(α, ℝ) where
  operator := P.c0Operator hC0
  operator_zero := P.c0Operator_zero hC0
  operator_add := P.c0Operator_add hC0
  opNorm_le_one := P.norm_c0Operator_le hC0
  continuous_orbit := hTime

@[simp]
theorem p2m_embedded_e0fbc9691c0c167e (hTime : P.HasContinuousC0Orbits hC0) (t : NNReal) :
    (P.c0Semigroup hC0 hTime) t = P.c0Operator hC0 t :=
  rfl

@[simp]
theorem p2m_embedded_1d809baf24e54444 (hTime : P.HasContinuousC0Orbits hC0)
    (t : NNReal) (f : C₀(α, ℝ)) :
    (P.c0Semigroup hC0 hTime) t f = P.c0KernelIntegral hC0 t f :=
  rfl

/-- Evaluation of the packaged semigroup is exactly the raw kernel integral. -/
@[simp]
theorem p2m_embedded_f8f361cc977a6554 (hTime : P.HasContinuousC0Orbits hC0)
    (t : NNReal) (f : C₀(α, ℝ)) (x : α) :
    (P.c0Semigroup hC0 hTime) t f x = kernelIntegral (P t) f x :=
  rfl

section Feller

variable [LocallyCompactSpace α] [T2Space α]

/-- A combined Feller predicate supplies its spatial `C₀` property. -/
theorem IsFellerKernelSemigroup.mapsC0 {P : SubMarkovKernelSemigroup α}
    (hP : P.IsFellerKernelSemigroup) : P.MapsC0 :=
  hP.choose

/-- A combined Feller predicate supplies continuity of the corresponding `C₀` orbits. -/
theorem IsFellerKernelSemigroup.hasContinuousC0Orbits {P : SubMarkovKernelSemigroup α}
    (hP : P.IsFellerKernelSemigroup) : P.HasContinuousC0Orbits hP.mapsC0 :=
  hP.choose_spec

/-- The strongly continuous contraction semigroup selected by the combined Feller predicate. -/
noncomputable def IsFellerKernelSemigroup.c0Semigroup {P : SubMarkovKernelSemigroup α}
    (hP : P.IsFellerKernelSemigroup) :
    Semigroup.StronglyContinuousContractionSemigroup C₀(α, ℝ) :=
  P.c0Semigroup hP.mapsC0 hP.hasContinuousC0Orbits

@[simp]
theorem IsFellerKernelSemigroup.c0Semigroup_apply_apply
    {P : SubMarkovKernelSemigroup α} (hP : P.IsFellerKernelSemigroup)
    (t : NNReal) (f : C₀(α, ℝ)) (x : α) :
    hP.c0Semigroup t f x = kernelIntegral (P t) f x :=
  rfl

end Feller

end SubMarkovKernelSemigroup

end MarkovProcess


