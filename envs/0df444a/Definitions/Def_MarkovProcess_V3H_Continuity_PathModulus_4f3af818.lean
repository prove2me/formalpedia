-- Prove2me | Definitions.Def_MarkovProcess_V3H_Continuity_PathModulus_4f3af818
-- name    : MarkovProcess_V3H_Continuity_PathModulus_4f3af818
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:34:45.945517+00:00
-- url     : https://prove2.me/theorems/d92dc084-8a3d-4fe3-b7e0-af2fff122a0a
-- title:
--   MarkovProcess: MarkovProcess_V3H_Continuity_PathModulus_4f3af818
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicChaining_a582e42e
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicIncrements_eff99a2c
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicPathChaining_e74fe8f3
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Time_FiniteGridIncrement_7a49f6ac
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.EMetricSpace.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A quantitative modulus of continuity from a Kolmogorov moment bound

The Kolmogorov--Chentsov argument is usually stated as an almost-sure Hölder property of a
continuous modification.  This file records the *quantitative* form that a tightness argument
needs: for a probability law on continuous paths whose coordinate process satisfies the
Kolmogorov moment condition with exponents `p`, `q` and constant `M`, the mass of the paths that
oscillate by more than `r` at scale `delta` on `[0, T]` is at most `eps`, once `delta` is small
enough --- and the threshold `delta` depends only on `p`, `q`, `M`, the Hölder exponent, `T`,
`r` and `eps`, not on the law.  This uniformity is the whole point: it is what makes the estimate
usable simultaneously at every starting point of a Markov process.

Main results:

* `MarkovProcess.ContinuousPath.modulusSet`, the closed set of paths whose oscillation over
  `[0, T]` at scale `delta` is at most `r`, with `isClosed_modulusSet` and
  `measurableSet_modulusSet`;
* `MarkovProcess.ContinuousPath.exists_measure_compl_modulusSet_le`, the quantitative estimate,
  uniform over all laws obeying one and the same moment bound.

Nothing here constructs a law, asserts a Hölder exponent for individual paths, or claims
tightness; tightness is assembled from this estimate elsewhere.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoEMetricSpace alpha]

/-- The paths whose oscillation over `[0, T]` at scale `delta` is at most `r`: any two times of
`[0, T]` within `delta` of each other carry values within `r` of each other. -/
def modulusSet (T : ℝ≥0) (delta r : ℝ≥0∞) : Set (ContinuousPath alpha) :=
  {omega | ∀ s t : ℝ≥0, s ≤ T → t ≤ T → edist s t ≤ delta → edist (omega s) (omega t) ≤ r}







end ContinuousPath

section Estimate

variable {alpha : Type*} [PseudoEMetricSpace alpha]

/-- The chaining bound produced at base level `N`: twice the exact geometric tail above `N` plus
one coarse threshold. -/
private noncomputable def dyadicChainBound (gamma : ℝ) (N : ℕ) : ℝ≥0∞ :=
  2 * (dyadicIncrementThreshold gamma (N + 1) *
      (1 - dyadicIncrementThresholdRatio gamma)⁻¹) + dyadicIncrementThreshold gamma N



/-- The event that some adjacent increment of the level-`n` subdivision of `[0, T]` reaches the
level's Kolmogorov--Chentsov threshold. -/
private def badLevel (T : ℝ≥0) (p gamma : ℝ) (n : ℕ) : Set (ContinuousPath alpha) :=
  finiteGridBadIncrement (fun (t : ℝ≥0) (omega : ContinuousPath alpha) ↦ omega t)
    (fun i : Fin (2 ^ n + 1) ↦ dyadicTime T n (i : ℕ)) p (dyadicIncrementThreshold gamma n)













end Estimate

end MarkovProcess


