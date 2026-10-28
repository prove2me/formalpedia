-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Parameterized_CemeteryDenseTimeSupport
-- name    : MarkovProcessModule_MarkovProcess_Parameterized_CemeteryDenseTimeSupport
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:41:49.142051+00:00
-- url     : https://prove2.me/theorems/2be1627d-d214-4412-b330-016c732ee285
-- title:
--   MarkovProcess.Parameterized.CemeteryDenseTimeSupport
-- statement:
--   # Simultaneous dense-time cemetery avoidance
--
--   For conservative live fibers, the jointly constructed parameterized cemetery trajectory avoids
--   the cemetery state simultaneously at every point of its countable dense-time index.
--
--   This is only a statement about the countable trajectory. It makes no continuous-extension,
--   lifetime-path, or spatial support claim.
--
--   Complete pinned Lean module MarkovProcess.Parameterized.CemeteryDenseTimeSupport by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Parameterized/CemeteryDenseTimeSupport.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Parameterized_CemeteryDenseTimeMarginals

/-!
# Simultaneous dense-time cemetery avoidance

For conservative live fibers, the jointly constructed parameterized cemetery trajectory avoids
the cemetery state simultaneously at every point of its countable dense-time index.

This is only a statement about the countable trajectory. It makes no continuous-extension,
lifetime-path, or spatial support claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess

noncomputable section

/-- A cemetery-valued path is live at every point of its index set. -/
def IsLiveAtEveryTime {D alpha : Type*} (path : D → Cemetery alpha) : Prop :=
  ∀ d, path d ≠ Cemetery.delta

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace (Cemetery alpha)]

/-- From a live starting state, the parameterized cemetery trajectory is almost surely live at
all enumerated dense times simultaneously. -/
theorem ae_isLiveAtEveryTime_parameterizedCemeteryDenseTimeTrajectory
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (theta : Theta) (x : alpha) :
    ∀ᵐ path ∂P.cemeterySemigroup.parameterizedDenseTimeTrajectory
        P.isConservative_cemeterySemigroup e iota (theta, Cemetery.alive x),
      IsLiveAtEveryTime path := by
  let mu := P.cemeterySemigroup.parameterizedDenseTimeTrajectory
    P.isConservative_cemeterySemigroup e iota (theta, Cemetery.alive x)
  have hdelta : MeasurableSet ({Cemetery.delta} : Set (Cemetery alpha)) := by
    simpa only [Set.range_unique] using
      (measurableSet_range_inr :
        MeasurableSet (Set.range (Sum.inr : Unit → alpha ⊕ Unit)))
  have hcoordinate : ∀ n : ℕ, ∀ᵐ path ∂mu, path (e n) ≠ Cemetery.delta := by
    intro n
    have hzero :=
      P.parameterizedCemeteryDenseTimeTrajectory_map_eval_singleton_delta
        hP e iota theta x (e n)
    rw [Kernel.map_apply _ (measurable_pi_apply (e n)),
      Measure.map_apply (measurable_pi_apply (e n)) hdelta] at hzero
    rw [ae_iff]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, not_ne_iff] using! hzero
  filter_upwards [ae_all_iff.mpr hcoordinate] with path hpath
  intro d
  simpa only [e.apply_symm_apply] using hpath (e.symm d)

end ParameterizedSubMarkovKernelSemigroup

end
end MarkovProcess


