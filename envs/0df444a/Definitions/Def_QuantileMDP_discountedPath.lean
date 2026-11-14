-- Prove2me | Definitions.Def_QuantileMDP_discountedPath
-- name    : QuantileMDP_discountedPath
-- status  : Definition
-- author  : @shuffle
-- created : 2026-11-14T02:24:03.127339+00:00
-- url     : https://prove2.me/theorems/6adfef87-9e39-4878-a0c9-99952f9686e3
-- title:
--   Discounted quantile MDP path rewards and prefix laws
-- statement:
--   Path prefixes, per-step rewards, finite models with geometrically discounted rewards, and the prefix law specification.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.3, Theorem 6, pp. 23–24. https://arxiv.org/abs/1711.05788v5

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Definitions.Def_QuantileMDP_Model

namespace QuantileMDP
open MeasureTheory

/-- Prefix of an infinite state path, including the state at time `k`. -/
def infinitePrefix {S : Type*} (w : ℕ → S) (k : ℕ) : Fin (k + 1) → S :=
  fun i => w i.val

def stepReward {S A : Type*} (M : Model S A) (π : Policy S A) (k : ℕ)
    (w : ℕ → S) : ℝ :=
  M.r k (w k) (π k (infinitePrefix w k)) (w (k + 1))

noncomputable def discountedModel {S A : Type*} (M : Model S A) (γ : ℝ) : Model S A :=
  { M with r := fun k s a i => γ ^ k * M.r k s a i }

/-- The state path has the prefix cylinder weights prescribed by the model,
starting from the specified state. -/
def IsPolicyPathLaw {S A : Type*} [MeasurableSpace S] (M : Model S A)
    (π : Policy S A) (s : S) (P : Measure (ℕ → S)) : Prop := by
  classical
  exact IsProbabilityMeasure P ∧ ∀ n (g : Fin (n + 1) → S),
      P {w | infinitePrefix w n = g} =
        if g 0 = s then pathWeight M π g else 0

end QuantileMDP


