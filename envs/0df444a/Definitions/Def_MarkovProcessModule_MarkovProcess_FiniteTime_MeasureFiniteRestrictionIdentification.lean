-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_MeasureFiniteRestrictionIdentification
-- name    : MarkovProcessModule_MarkovProcess_FiniteTime_MeasureFiniteRestrictionIdentification
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:30:22.157982+00:00
-- url     : https://prove2.me/theorems/5c89d864-8f14-4bcd-a87d-4c86ed9abe18
-- title:
--   MarkovProcess.FiniteTime.MeasureFiniteRestrictionIdentification
-- statement:
--   # Identifying measures from finite-coordinate restrictions
--
--   A finite measure on a product space is determined by all of its finite-coordinate pushforwards.
--   The empty coordinate set is part of the family and therefore records the total mass; measures of
--   unequal mass cannot satisfy the hypothesis.
--
--   This is generic measure-theoretic infrastructure and requires no topology.
--
--   Complete pinned Lean module MarkovProcess.FiniteTime.MeasureFiniteRestrictionIdentification by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/MeasureFiniteRestrictionIdentification.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Identifying measures from finite-coordinate restrictions

A finite measure on a product space is determined by all of its finite-coordinate pushforwards.
The empty coordinate set is part of the family and therefore records the total mass; measures of
unequal mass cannot satisfy the hypothesis.

This is generic measure-theoretic infrastructure and requires no topology.
-/

open MeasureTheory

namespace MarkovProcess
namespace Measure

noncomputable section

variable {index alpha : Type*} [MeasurableSpace alpha]

/-- Two measures on a product space agree if all their finite-coordinate pushforwards agree. -/
theorem eq_of_map_finiteRestriction_eq
    (mu nu : Measure (index → alpha)) [IsFiniteMeasure mu]
    (h : ∀ I : Finset index, mu.map I.restrict = nu.map I.restrict) :
    mu = nu := by
  let family : (I : Finset index) → Measure (I → alpha) :=
    fun I ↦ mu.map I.restrict
  have hmu : IsProjectiveLimit mu family := by
    intro I
    rfl
  have hnu : IsProjectiveLimit nu family := by
    intro I
    exact (h I).symm
  let (I : Finset index) : IsFiniteMeasure (family I) := by
    dsimp only [family]
    infer_instance
  exact hmu.unique hnu

end
end Measure
end MarkovProcess


