-- Prove2me | Definitions.Def_FD1D_TrajectoryBridge
-- name    : FD1D_TrajectoryBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:07:11.820459+00:00
-- url     : https://prove2.me/theorems/a8635f9e-0420-56a8-bb7b-62b3acb2fcf4
-- title:
--   Trajectory Bridge
-- statement:
--   Definitions and structural lemmas for Trajectory Bridge, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/TrajectoryBridge.lean

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
set_option autoImplicit true
namespace FD1D.TrajectoryBridge
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
def iterateLaw (κ : Kernel α α) (μ₀ : Measure α) : ℕ → Measure α
  | 0 => μ₀
  | n + 1 => κ ∘ₘ iterateLaw κ μ₀ n
@[simp]
theorem iterateLaw_zero (κ : Kernel α α) (μ₀ : Measure α) :
    iterateLaw κ μ₀ 0 = μ₀ :=
  rfl
@[simp]
theorem iterateLaw_succ (κ : Kernel α α) (μ₀ : Measure α) (n : ℕ) :
    iterateLaw κ μ₀ (n + 1) = κ ∘ₘ iterateLaw κ μ₀ n :=
  rfl
def historyKernel (κ : Kernel α α) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → α) α :=
  κ.comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)
instance historyKernel.instIsMarkovKernel (κ : Kernel α α)
    [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (historyKernel κ n) := by
  unfold historyKernel
  infer_instance
def trajectoryLaw (μ₀ : Measure α) (κ : Kernel α α) [IsMarkovKernel κ] :
    Measure (ℕ → α) :=
  Kernel.trajMeasure (X := fun _ => α) μ₀ (historyKernel κ)
end
end FD1D.TrajectoryBridge


