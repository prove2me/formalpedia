-- Prove2me | Definitions.Def_MondererShapley_Improvement_HasFIP
-- name    : MondererShapley_Improvement_HasFIP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:13.51199+00:00
-- url     : https://prove2.me/theorems/36c5a8d5-094f-4f36-978f-0490571587b2
-- title:
--   Finite improvement property
-- statement:
--   A game has the **finite improvement property** (FIP) when every path on which the deviating player strictly raises their payoff is finite. Equivalently, there is no infinite sequence of profiles $(y_k)_{k\ge 0}$ and deviators $(i_k)_{k\ge 0}$ such that each step changes exactly player $i_k$ and
--
--   $$
--   u^{i_k}(y_k)<u^{i_k}(y_{k+1})\qquad\text{for every }k\ge0.
--   $$
--
--   The absence of an infinite path is the property characterized in Lemma 2.5.
--
--   **Formalization Note** Infinite paths are indexed by natural numbers; `IsStep` requires a genuine strategy change at each step.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 128 (PDF p. 5), definition of FIP

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsStep

namespace MondererShapley.Improvement

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- Every improvement path is finite: no infinite path of strict unilateral gains exists. -/
def HasFIP (u : ι → (∀ i, Y i) → ℝ) : Prop :=
  ¬ ∃ (y : ℕ → ∀ i, Y i) (d : ℕ → ι),
      ∀ k, MondererShapley.ClosedPath.IsStep (y k) (y (k + 1)) (d k) ∧
        u (d k) (y k) < u (d k) (y (k + 1))

end MondererShapley.Improvement


