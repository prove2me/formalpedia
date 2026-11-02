-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FiniteTimeSingletonMarginalCleanV1
-- name    : MarkovProcess_V3HRepair_FiniteTimeSingletonMarginalCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:35:30.899569+00:00
-- url     : https://prove2.me/theorems/ef5537a7-a2a1-494e-a942-5a203b94be5f
-- title:
--   Verified MarkovProcess repair proof module: FiniteTimeSingletonMarginalCleanV1
-- statement:
--   The one-time finite-time kernel maps under evaluation of its sole coordinate to the semigroup kernel at that time.
-- source:
--   MarkovProcess by Scott Armstrong (Apache-2.0), upstream source commit 1f8060caa137731fa08029592019eeaf9d997fe5; adapted axiom-clean Lean module V3HRepaired.FiniteTimeSingletonMarginalCleanV1 from verified v17 checkpoint.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d

open MeasureTheory ProbabilityTheory
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
variable {α : Type*} [MeasurableSpace α]

@[simp]
theorem finiteTimeKernel_one_map_eval (P : SubMarkovKernelSemigroup α)
    (times : FiniteOrderedTimes 1) :
    (finiteTimeKernel P times).map (fun path ↦ path 0) = P (times 0) := by
  let : IsFiniteKernel (P (times 0)) := (P.isSubMarkovKernel (times 0)).isFiniteKernel
  let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) :=
    by rw [finiteTimeKernel_zero]; infer_instance
  rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
  rw [← Kernel.map_comp_right]
  · have hcomp :
        ((fun path : Fin 1 → α ↦ path 0) ∘
          fun z : α × (Fin 0 → α) ↦
            @Fin.cons 0 (fun _ : Fin 1 ↦ α) z.1 z.2) = Prod.fst := by
        funext z
        rfl
    rw [hcomp, ← Kernel.fst_eq]
    exact Kernel.fst_compProd _ _
  · exact measurable_finCons
  · exact measurable_pi_apply 0

end
end MarkovProcess.SubMarkovKernelSemigroup
#print axioms MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel_one_map_eval


