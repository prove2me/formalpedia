-- Prove2me | Definitions.Def_MarkovProcess_V3H_Continuity_PathTightness_ad16da33
-- name    : MarkovProcess_V3H_Continuity_PathTightness_ad16da33
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:36:11.810826+00:00
-- url     : https://prove2.me/theorems/f424a9c8-9ba5-4fa0-a11d-cfccbf16ffe1
-- title:
--   MarkovProcess: MarkovProcess_V3H_Continuity_PathTightness_ad16da33
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_PathModulus_4f3af818
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.UniformSpace.Ascoli

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Compact sets of paths, and tightness on continuous-path space

A family of laws on `C([0, ∞), alpha)` is tight as soon as two things hold uniformly over the
family: the time-zero position lies in a fixed compact set, and the oscillation over each bounded
time interval is controlled at a scale that does not depend on the law.  This file supplies the
compact sets that make that statement work and then assembles the tightness estimate.

The compact sets are `ContinuousPath.moduliSet K0 delta r`: the paths starting in `K0` whose
oscillation over `[0, n]` at scale `delta n` is at most `r n`, for every natural `n`.  When
`r n → 0` these conditions are exactly equicontinuity, so Arzelà--Ascoli applies as soon as the
values of the family at each fixed time stay in a compact set.  That last requirement --- the
compact containment condition of the weak-convergence literature --- is isolated as a hypothesis
in `isCompact_moduliSet_of_forall_isCompact`; over a *proper* metric state space (closed balls
compact) it is automatic, because the modulus already confines a path to a bounded neighbourhood
of its starting point, and `isCompact_moduliSet` discharges it.

Main results:

* `MarkovProcess.ContinuousPath.edist_le_of_modulus`, the chaining bound from the starting point;
* `MarkovProcess.ContinuousPath.moduliSet` and `moduliFunSet`, with closedness and
  equicontinuity;
* `MarkovProcess.ContinuousPath.isCompact_moduliSet_of_forall_isCompact` and
  `isCompact_moduliSet`, the Arzelà--Ascoli compactness statements;
* `MarkovProcess.ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le`, tightness of a
  family of laws from a uniform modulus estimate and a compact time-zero law.

Nothing here constructs a law, and no compactness theorem for measures (Prokhorov's theorem) is
proved or used.
-/

open Filter MeasureTheory Metric Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [MetricSpace alpha]

section Chaining



end Chaining

section Moduli

/-- The paths that start in `K0` and, for every natural `n`, oscillate by at most `r n` at
scale `delta n` over `[0, n]`. -/
def moduliSet (K0 : Set alpha) (delta rho : ℕ → ℝ≥0∞) : Set (ContinuousPath alpha) :=
  {omega | omega 0 ∈ K0} ∩ ⋂ n : ℕ, modulusSet (n : ℝ≥0) (delta n) (rho n)

/-- The same conditions read on arbitrary, not necessarily continuous, functions of time. -/
def moduliFunSet (K0 : Set alpha) (delta rho : ℕ → ℝ≥0∞) : Set (ℝ≥0 → alpha) :=
  {f | f 0 ∈ K0} ∩ ⋂ n : ℕ, {f : ℝ≥0 → alpha |
    ∀ s t : ℝ≥0, s ≤ (n : ℝ≥0) → t ≤ (n : ℝ≥0) → edist s t ≤ delta n → edist (f s) (f t) ≤ rho n}











end Moduli

section Tight





end Tight

end ContinuousPath

end MarkovProcess


