-- Prove2me | Definitions.Def_StableFA_Discounted_Supplement_PairAverager
-- name    : StableFA_Discounted_Supplement_PairAverager
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:40:21.809991+00:00
-- url     : https://prove2.me/theorems/784b7592-68f0-4e6c-b5d3-8cb460aafea6
-- title:
--   §3 and Appendix A — averager on admissible state–action pairs and the explicit derived MDP
-- statement:
--   An averager $A$ on state–action pairs has real constants $k_{zc}$, nonnegative weights $\beta_{zc}$ on those constants, nonnegative goal weights $\beta^g_{zc}$ and nonnegative target weights $\beta_{zcxa}$, with
--   $$\beta_{zc}+\beta^g_{zc}+\sum_x\sum_{a\in U(x)}\beta_{zcxa}=1.$$
--   The weights do not depend on the Q-function. The mapping is
--   $$(M_AQ)(z,c)=\beta_{zc}k_{zc}+\sum_x\sum_{a\in U(x)}\beta_{zcxa}Q(x,a).$$
--   The goal weight multiplies the goal's fixed value zero. Appendix A's derived MDP has the same admissible action sets as $M$ and
--   $$c'_{zc}=\sum_x\sum_{a\in U(x)}\beta_{zcxa}c_{xa}+\beta_{zc}k_{zc},\qquad p'_{zcy}=\sum_x\sum_{a\in U(x)}\beta_{zcxa}p_{xay}.$$
--   The remaining transition mass goes to the cost-free absorbing goal. This file defines the pair averager, its mapping and the constructed MDP used by Theorem A.1. The derived model is independent of the discount, and the constant term of its cost is not discounted.
--
--   **Formalization Note** The general finite MDP is the published `BertsekasSSPModel`. A subtype indexes only admissible target actions; the output remains a full table. Finite state-dependent action sets generalize the report's common action set. The row-sum and nonnegativity proofs ensure that the constructed model is an actual substochastic MDP. Constants may be negative; no positivity, properness or discount assumption is imposed.
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 7, §3, averager definition; p. 19, Theorem A.1 proof, pair coordinates, final display and interpretation of M′

import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace StableFA.Discounted.Supplement

/-- The averager of p. 7 with admissible state-action pairs as input coordinates.
`βgoal` aggregates the weights on the goal's zero Q-values. -/
structure PairAverager {n : ℕ} {C : Type} [Fintype C] [DecidableEq C]
    (M : BertsekasSSPModel n C) where
  k : Fin n → C → ℝ
  βc : Fin n → C → ℝ
  βgoal : Fin n → C → ℝ
  β : Fin n → C → (x : Fin n) → {a : C // a ∈ M.U x} → ℝ
  βc_nonneg : ∀ z c, 0 ≤ βc z c
  βgoal_nonneg : ∀ z c, 0 ≤ βgoal z c
  β_nonneg : ∀ z c x a, 0 ≤ β z c x a
  sum_eq_one : ∀ z c, βc z c + βgoal z c + ∑ x, ∑ a, β z c x a = 1

/-- M_A on Q-functions; the goal-coordinate contribution vanishes. -/
noncomputable def PairAverager.apply {n : ℕ} {C : Type} [Fintype C] [DecidableEq C]
    {M : BertsekasSSPModel n C} (A : PairAverager M)
    (Q : Fin n → C → ℝ) : Fin n → C → ℝ :=
  fun z c => A.βc z c * A.k z c + ∑ x, ∑ a, A.β z c x a * Q x a.val


/-- Appendix A's explicit derived MDP, independent of the discount.
Its row deficit is the transition probability to the absorbing, cost-free goal. -/
noncomputable def derivedModel {n : ℕ} {C : Type} [Fintype C] [DecidableEq C]
    (M : BertsekasSSPModel n C) (A : PairAverager M) : BertsekasSSPModel n C where
  U := M.U
  hU := M.hU
  g z c := (∑ x, ∑ a, A.β z c x a * M.g x a.val) + A.βc z c * A.k z c
  p z c y := ∑ x, ∑ a, A.β z c x a * M.p x a.val y
  hp_nonneg z c y := Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun a _ => mul_nonneg (A.β_nonneg z c x a) (M.hp_nonneg x a.val y)
  hp_sum z c _ := by
    calc
      (∑ y, ∑ x, ∑ a, A.β z c x a * M.p x a.val y) =
          ∑ x, ∑ a, A.β z c x a * (∑ y, M.p x a.val y) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
      _ ≤ ∑ x, ∑ a, A.β z c x a := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro a _
        simpa using mul_le_mul_of_nonneg_left (M.hp_sum x a.val a.property) (A.β_nonneg z c x a)
      _ ≤ 1 := by
        have h := A.sum_eq_one z c
        have hc := A.βc_nonneg z c
        have hg := A.βgoal_nonneg z c
        linarith

end StableFA.Discounted.Supplement


