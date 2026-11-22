-- Prove2me | Definitions.Def_Comp_Basic
-- name    : Comp_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:42:57.475069+00:00
-- url     : https://prove2.me/theorems/1e755941-4763-4a5a-ad4b-b2d86fd70c81
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Basic.lean

import Definitions.Def_Csg_Discounted
import Mathlib.Probability.ProbabilityMassFunction.Constructions
set_option autoImplicit true
namespace Comp
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
structure CsgQ (S A1 A2 : Type*) [Fintype S] [Fintype A1] [Fintype A2]
    [Nonempty A1] [Nonempty A2] [DecidableEq A1] [DecidableEq A2] where
  /-- Transition weights: `K s a1 a2 s'` is the rational probability of moving to `s'`. Required to
      be a distribution by `WellFormed`, not by construction. -/
  K : S → A1 → A2 → S → ℚ
  /-- Reward for the joint action, paid by the row player to the column player, as in `CSG.r`. -/
  r : S → A1 → A2 → ℚ
structure DiscountedCsgQ (S A1 A2 : Type*) [Fintype S] [Fintype A1] [Fintype A2]
    [Nonempty A1] [Nonempty A2] [DecidableEq A1] [DecidableEq A2] extends CsgQ S A1 A2 where
  /-- Discount factor. Required to lie in `[0, 1)` by `WellFormed`. -/
  l : ℚ
namespace CsgQ
def WellFormed (G : CsgQ S A1 A2) : Prop :=
  (∀ s a1 a2 s', 0 ≤ G.K s a1 a2 s') ∧ (∀ s a1 a2, ∑ s', G.K s a1 a2 s' = 1)
instance (G : CsgQ S A1 A2) : Decidable G.WellFormed := by
  unfold WellFormed
  infer_instance
theorem K_cast_nonneg {G : CsgQ S A1 A2} (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) (s' : S) :
    (0 : ℝ) ≤ ((G.K s a1 a2 s' : ℚ) : ℝ) := by
  exact_mod_cast h.1 s a1 a2 s'
theorem sum_K_cast_eq_one {G : CsgQ S A1 A2} (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) :
    ∑ s' : S, ((G.K s a1 a2 s' : ℚ) : ℝ) = 1 := by
  have hq : ((∑ s' : S, G.K s a1 a2 s' : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by rw [h.2 s a1 a2]
  push_cast at hq
  exact hq
noncomputable def toPMF (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) :
    PMF S :=
  PMF.ofFintype (fun s' => ENNReal.ofReal ((G.K s a1 a2 s' : ℚ) : ℝ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun s' _ => K_cast_nonneg h s a1 a2 s',
      sum_K_cast_eq_one h s a1 a2, ENNReal.ofReal_one])
noncomputable def toCSG (G : CsgQ S A1 A2) (h : G.WellFormed) : CSG S A1 A2 where
  K s a1 a2 := G.toPMF h s a1 a2
  r s a1 a2 := ((G.r s a1 a2 : ℚ) : ℝ)
def expectQ (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) (v : S → ℚ) : ℚ :=
  ∑ s', G.K s a1 a2 s' * v s'
end CsgQ
namespace DiscountedCsgQ
def WellFormed (G : DiscountedCsgQ S A1 A2) : Prop :=
  G.toCsgQ.WellFormed ∧ 0 ≤ G.l ∧ G.l < 1
instance (G : DiscountedCsgQ S A1 A2) : Decidable G.WellFormed := by
  unfold WellFormed
  infer_instance
noncomputable def toDiscountedCSG (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) :
    DiscountedCSG S A1 A2 where
  toCSG := G.toCsgQ.toCSG h.1
  l := ((G.l : ℚ) : ℝ)
  l_nonneg := by exact_mod_cast h.2.1
  l_lt_one := by exact_mod_cast h.2.2
end DiscountedCsgQ
end Comp


