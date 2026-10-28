-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Kernel_FiniteRestrictionIdentification
-- name    : MarkovProcessModule_MarkovProcess_Kernel_FiniteRestrictionIdentification
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:30:32.904565+00:00
-- url     : https://prove2.me/theorems/8624d815-ab6f-40cd-99db-ba87b7407fdd
-- title:
--   MarkovProcess.Kernel.FiniteRestrictionIdentification
-- statement:
--   # Identifying path kernels from finite-coordinate restrictions
--
--   A finite kernel on a product path space is determined by all of its finite-coordinate
--   pushforwards.  The proof applies uniqueness of finite projective limits pointwise in the source
--   parameter.  No topology, time order, path regularity, or Markov property is used.
--
--   Complete pinned Lean module MarkovProcess.Kernel.FiniteRestrictionIdentification by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/FiniteRestrictionIdentification.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Identifying path kernels from finite-coordinate restrictions

A finite kernel on a product path space is determined by all of its finite-coordinate
pushforwards.  The proof applies uniqueness of finite projective limits pointwise in the source
parameter.  No topology, time order, path regularity, or Markov property is used.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace Kernel

noncomputable section

variable {index alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]

/-- Two finite kernels on a product path space agree if all their finite-coordinate pushforwards
agree. -/
theorem eq_of_map_finiteRestriction_eq
    (kappa eta : Kernel beta (index → alpha)) [IsFiniteKernel kappa]
    (h : ∀ I : Finset index,
      kappa.map I.restrict = eta.map I.restrict) :
    kappa = eta := by
  ext x : 1
  let family : (I : Finset index) → Measure (I → alpha) :=
    fun I ↦ (kappa x).map I.restrict
  have hkappa : IsProjectiveLimit (kappa x) family := by
    intro I
    rfl
  have heta : IsProjectiveLimit (eta x) family := by
    intro I
    have hx := congrArg (fun z : Kernel beta (I → alpha) ↦ z x) (h I)
    simpa only [Kernel.map_apply _ (Finset.measurable_restrict I) x] using hx.symm
  let (I : Finset index) : IsFiniteMeasure (family I) := by
    dsimp only [family]
    infer_instance
  exact hkappa.unique heta

end
end Kernel
end MarkovProcess


