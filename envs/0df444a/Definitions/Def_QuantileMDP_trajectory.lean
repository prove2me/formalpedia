-- Prove2me | Definitions.Def_QuantileMDP_trajectory
-- name    : QuantileMDP_trajectory
-- status  : Definition
-- author  : @shuffle
-- created : 2026-11-14T02:25:50.285424+00:00
-- url     : https://prove2.me/theorems/8e1c0727-ba7f-4104-9f02-3930dcad7075
-- title:
--   Quantile MDP trajectory law
-- statement:
--   The canonical probability measure on infinite state paths obtained by iterating the transition kernels under a deterministic history-dependent policy.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.3, Theorem 6, pp. 23–24. https://arxiv.org/abs/1711.05788v5

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Definitions.Def_QuantileMDP_discountedPath

open MeasureTheory ProbabilityTheory Finset

namespace QuantileMDP

/-- Convert an initial segment indexed by Mathlib's `Iic n` to the
finite-horizon history representation. -/
def historyEquiv (S : Type*) (n : ℕ) : (Iic n → S) ≃ (Fin (n + 1) → S) where
  toFun h i := h ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩
  invFun g i := g ⟨i.val, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.property)⟩
  left_inv h := by funext i; rfl
  right_inv g := by funext i; rfl

/-- A policy-induced one-step probability kernel on state histories. -/
noncomputable def policyKernel {S A : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (M : Model S A) (π : Policy S A) (n : ℕ) :
    Kernel (Iic n → S) S where
  toFun h := (M.P n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (π n (historyEquiv S n h))).toMeasure
  measurable' := measurable_of_countable _

instance policyKernel_markov {S A : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (M : Model S A) (π : Policy S A) (n : ℕ) :
    IsMarkovKernel (policyKernel M π n) := ⟨fun h => by
      change IsProbabilityMeasure ((M.P n (h _) (π n (historyEquiv S n h))).toMeasure)
      infer_instance⟩

/-- Infinite trajectory law determined by the initial state and the policy. -/
noncomputable def trajectoryLaw {S A : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (M : Model S A) (π : Policy S A) (s : S) :
    Measure (ℕ → S) :=
  Kernel.traj (X := fun _ => S) (policyKernel M π) 0 (fun _ => s)

end QuantileMDP


