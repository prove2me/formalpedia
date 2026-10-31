-- Prove2me | Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
-- name    : MarkovProcess_V3H_Path_OptionalStopping_4dea182f
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:27:53.232766+00:00
-- url     : https://prove2.me/theorems/4c6df677-4e73-434e-8500-417323aabeb2
-- title:
--   MarkovProcess: MarkovProcess_V3H_Path_OptionalStopping_4dea182f
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Instances.NNReal.Lemmas

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Optional stopping in continuous time, at a bounded finite stopping time

Mathlib's optional stopping theorem is discrete-time.  This file proves the continuous-time
statement the library consumes: if `M` is a real-valued martingale for a filtration indexed by
`ℝ≥0`, bounded on bounded time intervals and right continuous in time along every sample point,
and `T` is a finite stopping time bounded by a deterministic horizon `K`, then

  `∫ omega, M (T omega) omega ∂mu = ∫ omega, M 0 omega ∂mu`

(`integral_stoppedValue_eq_of_locallyBounded`, with the uniformly bounded case
`integral_stoppedValue_eq_of_le`).

For a supermartingale the corresponding expectation is at most its initial expectation
(`integral_stoppedValue_le_of_locallyBounded` and `integral_stoppedValue_le_of_le`).

The proof samples a supermartingale on the dyadic grid and applies Mathlib's
`Submartingale.expected_stoppedValue_mono` after negation.  The dyadic ceilings `T_n` of a finite
stopping time are stopping times with finite range that decrease to `T`
(`Path/StoppingTimeDyadicCeiling.lean`), so dominated convergence and right continuity give the
supermartingale inequality.  Applying that inequality to a martingale and its negation gives the
martingale equality.

Nothing here is specific to path space: the statements are for an arbitrary measurable space with
a filtration indexed by `ℝ≥0`.  No optional-stopping result for unbounded stopping times is
asserted.
-/

open Filter MeasureTheory Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section

variable {Omega : Type*} {m : MeasurableSpace Omega} {mu : Measure Omega}
  {ℱ : Filtration NNReal m} {M : NNReal → Omega → ℝ}

section FiniteRange

variable [IsFiniteMeasure mu]









end FiniteRange

section DyadicApproximation

/-- Sampling an `NNReal` filtration on a dyadic grid gives a discrete filtration. -/
private def dyadicFiltration (n : ℕ) (ℱ : Filtration NNReal m) : Filtration ℕ m where
  seq k := ℱ (dyadicGrid n k)
  mono' _ _ hkl := ℱ.mono (monotone_dyadicGrid n hkl)
  le' k := ℱ.le (dyadicGrid n k)











end DyadicApproximation

section OptionalStopping

variable [IsFiniteMeasure mu]









end OptionalStopping

end

end MarkovProcess


