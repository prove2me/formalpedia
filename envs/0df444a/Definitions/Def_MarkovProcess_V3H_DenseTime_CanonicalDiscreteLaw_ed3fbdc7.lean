-- Prove2me | Definitions.Def_MarkovProcess_V3H_DenseTime_CanonicalDiscreteLaw_ed3fbdc7
-- name    : MarkovProcess_V3H_DenseTime_CanonicalDiscreteLaw_ed3fbdc7
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:34:52.049811+00:00
-- url     : https://prove2.me/theorems/8b879208-14f7-47fb-b57d-7e2b9c782560
-- title:
--   MarkovProcess: MarkovProcess_V3H_DenseTime_CanonicalDiscreteLaw_ed3fbdc7
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_CanonicalDiscretePath_a2b715fb
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Time_OrderedGrid_1c9977ee
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Canonical discrete trajectory laws

This file equips the canonical discrete path space with the trajectory law of
a conservative transition-kernel semigroup along one fixed ordered grid.  It
records exact finite-prefix and coordinate marginal identities.  No
conditional-expectation Markov property is asserted here.
-/

open MeasureTheory
open ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)

/-- The canonical discrete path law started from `x` along `grid`. -/
noncomputable def canonicalDiscreteLaw
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) :
    Measure (DiscretePath α) :=
  orderedGridTrajectoryLaw P hP grid x









end SubMarkovKernelSemigroup

end MarkovProcess


