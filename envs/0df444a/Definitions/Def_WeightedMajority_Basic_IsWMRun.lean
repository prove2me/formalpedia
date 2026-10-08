-- Prove2me | Definitions.Def_WeightedMajority_Basic_IsWMRun
-- name    : WeightedMajority_Basic_IsWMRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:38:11.217832+00:00
-- url     : https://prove2.me/theorems/19e8035f-783e-4b12-b04a-90950ccbd064
-- title:
--   Finite runs of the binary Weighted Majority Algorithm
-- statement:
--   Fix a finite pool of $n$ prediction algorithms and a sequence of $T$ binary trials. On trial $t$, pool member $i$ predicts $x_{t,i}\in\{0,1\}$, the true label is $\rho_t\in\{0,1\}$, and the master predicts $\lambda_t\in\{0,1\}$. Let $w_{t,i}$ be member $i$'s weight before that trial, with prescribed initial weight $w_{0,i}$.
--
--   A WM run compares the total weights $q_{t,0}$ and $q_{t,1}$ backing the two predictions. It predicts the side with larger weight and permits either prediction on a tie. For a fixed factor $\beta$, its update is
--
--   $$
--   w_{t+1,i} =
--   \begin{cases}
--   \beta w_{t,i},&\lambda_t\ne\rho_t\text{ and }x_{t,i}\ne\rho_t,\\
--   w_{t,i},&\text{otherwise}.
--   \end{cases}
--   $$
--
--   The accompanying definitions give the total pool weight, the weight backing either prediction, and the number of master mistakes. The model makes no probabilistic assumption on the sequence. A run requires a nonempty pool, $0\le\beta<1$, and positive initial weights $w_{0,i}>0$.
--
--   **Formalization Note** Pool members are indexed by `Fin n`, trials by `Fin T`, and weights by natural-number trial boundaries. Boolean false and true represent 0 and 1. Weight values beyond the final boundary are immaterial.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108(2) (1994), pp. 213, 215, 220, §1, WM algorithm and Notations and Assumptions; https://doi.org/10.1006/inco.1994.1009

import Mathlib

namespace WeightedMajority.Basic

/-- The total weight of a finite pool at a given trial boundary. -/
def totalWeight {n : ℕ} (w : ℕ → Fin n → ℝ) (t : ℕ) : ℝ :=
  ∑ i : Fin n, w t i

/-- The weight backing a binary prediction in one trial. -/
def voteWeight {n T : ℕ} (x : Fin T → Fin n → Bool)
    (w : ℕ → Fin n → ℝ) (t : Fin T) (b : Bool) : ℝ :=
  ∑ i : Fin n, if x t i = b then w t.val i else 0

/-- The number of trials on which the master prediction differs from the label. -/
def mistakeCount {T : ℕ} (prediction label : Fin T → Bool) : ℕ :=
  (Finset.univ.filter (fun t => prediction t ≠ label t)).card

/-- A run of WM on a finite binary sequence. A tie admits either master prediction.
The weight of an incorrect pool member is multiplied by `β` only when WM errs. -/
structure IsWMRun {n T : ℕ} (β : ℝ) (initial : Fin n → ℝ)
    (x : Fin T → Fin n → Bool) (label : Fin T → Bool)
    (w : ℕ → Fin n → ℝ) (prediction : Fin T → Bool) : Prop where
  pool_nonempty : 0 < n
  beta_nonneg : 0 ≤ β
  beta_lt_one : β < 1
  initial_pos : ∀ i, 0 < initial i
  initial_weight : ∀ i, w 0 i = initial i
  predict_zero : ∀ t, voteWeight x w t true < voteWeight x w t false →
    prediction t = false
  predict_one : ∀ t, voteWeight x w t false < voteWeight x w t true →
    prediction t = true
  update : ∀ t i, w (t.val + 1) i =
    if prediction t ≠ label t ∧ x t i ≠ label t then β * w t.val i
    else w t.val i

end WeightedMajority.Basic


