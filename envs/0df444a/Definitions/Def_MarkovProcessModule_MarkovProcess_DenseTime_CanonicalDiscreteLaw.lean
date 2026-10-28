-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_DenseTime_CanonicalDiscreteLaw
-- name    : MarkovProcessModule_MarkovProcess_DenseTime_CanonicalDiscreteLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:47:06.027434+00:00
-- url     : https://prove2.me/theorems/563d7570-09a0-4795-a91b-66a9882cbbfb
-- title:
--   MarkovProcess.DenseTime.CanonicalDiscreteLaw
-- statement:
--   # Canonical discrete trajectory laws
--
--   This file equips the canonical discrete path space with the trajectory law of
--   a conservative transition-kernel semigroup along one fixed ordered grid.  It
--   records exact finite-prefix and coordinate marginal identities.  No
--   conditional-expectation Markov property is asserted here.
--
--   Complete pinned Lean module MarkovProcess.DenseTime.CanonicalDiscreteLaw by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/DenseTime/CanonicalDiscreteLaw.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_DenseTime_CanonicalDiscretePath
import Definitions.Def_MarkovProcessModule_MarkovProcess_Time_OrderedGrid

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

/-- The canonical discrete path law is a probability measure. -/
theorem IsConservative.isProbabilityMeasure_canonicalDiscreteLaw
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) :
    IsProbabilityMeasure (canonicalDiscreteLaw P hP grid x) := by
  exact IsConservative.isProbabilityMeasure_orderedGridTrajectoryLaw P hP grid x

/-- Restricting the canonical law to coordinates through `n` gives the
corresponding finite Ionescu--Tulcea trajectory law. -/
theorem IsConservative.canonicalDiscreteLaw_map_prefix
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) (n : ℕ) :
    (canonicalDiscreteLaw P hP grid x).map
        (fun path : DiscretePath α => fun i : Finset.Iic n => path i) =
      Kernel.partialTraj (X := fun _ => α) (orderedGridStepKernel P grid) 0 n
        (initialHistory x) := by
  exact IsConservative.orderedGridTrajectoryLaw_map_frestrictLe P hP grid x n

/-- The law of coordinate `n` is the last-coordinate pushforward of the
finite trajectory law through `n`. -/
theorem IsConservative.canonicalDiscreteLaw_map_coordinate
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) (n : ℕ) :
    (canonicalDiscreteLaw P hP grid x).map (DiscretePath.coordinate n) =
      (Kernel.partialTraj (X := fun _ => α) (orderedGridStepKernel P grid) 0 n
        (initialHistory x)).map (fun history => history ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
  rw [← IsConservative.canonicalDiscreteLaw_map_prefix P hP grid x n,
    Measure.map_map]
  · rfl
  · exact measurable_pi_apply (X := fun _ : Finset.Iic n => α)
      ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  · exact measurable_pi_iff.mpr fun _ => DiscretePath.measurable_coordinate (α := α) _

/-- The zeroth coordinate of the canonical law is deterministically the
starting state. -/
theorem IsConservative.canonicalDiscreteLaw_map_coordinate_zero
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) :
    (canonicalDiscreteLaw P hP grid x).map (DiscretePath.coordinate 0) = Measure.dirac x := by
  rw [IsConservative.canonicalDiscreteLaw_map_coordinate P hP grid x 0,
    Kernel.partialTraj_self, Kernel.id_apply]
  exact Measure.map_dirac'
    (measurable_pi_apply (X := fun _ : Finset.Iic 0 => α)
      ⟨0, Finset.mem_Iic.mpr le_rfl⟩) (initialHistory x)

end SubMarkovKernelSemigroup

end MarkovProcess


