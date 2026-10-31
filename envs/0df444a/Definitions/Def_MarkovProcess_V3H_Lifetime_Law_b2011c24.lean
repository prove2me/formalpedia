-- Prove2me | Definitions.Def_MarkovProcess_V3H_Lifetime_Law_b2011c24
-- name    : MarkovProcess_V3H_Lifetime_Law_b2011c24
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:34:53.37378+00:00
-- url     : https://prove2.me/theorems/9e618604-b9e7-4a07-ab9a-051ce23e80a2
-- title:
--   MarkovProcess: MarkovProcess_V3H_Lifetime_Law_b2011c24
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous laws as nonexplosive lifetime-path laws

This file transports kernels on ordinary continuous paths through the infinite-lifetime
embedding. It records the resulting nonexplosion and coordinate identities without asserting
that any particular dense-time or PDE law has continuous paths.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

/-- A kernel on lifetime paths is nonexplosive when its lifetime is almost surely infinite
from every starting point. -/
def IsNonexplosive (kappa : Kernel beta (LifetimePath alpha)) : Prop :=
  ∀ x, ∀ᵐ omega ∂kappa x, omega.lifetime = ∞

/-- Regard a kernel on ordinary continuous paths as a kernel on infinite-lifetime paths. -/
def toLifetimePathKernel (kappa : Kernel beta (ContinuousPath alpha)) :
    Kernel beta (LifetimePath alpha) :=
  Kernel.mapOfMeasurable kappa LifetimePath.ofContinuousPath
    LifetimePath.measurable_ofContinuousPath

/-- The lifetime-path transport agrees with ordinary kernel mapping. -/
theorem toLifetimePathKernel_eq_map (kappa : Kernel beta (ContinuousPath alpha)) :
    toLifetimePathKernel kappa = kappa.map LifetimePath.ofContinuousPath :=
  Kernel.mapOfMeasurable_eq_map _ LifetimePath.measurable_ofContinuousPath







end Kernel
end
end MarkovProcess


