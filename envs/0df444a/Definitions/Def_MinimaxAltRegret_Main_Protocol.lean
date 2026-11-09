-- Prove2me | Definitions.Def_MinimaxAltRegret_Main_Protocol
-- name    : MinimaxAltRegret_Main_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:11.553671+00:00
-- url     : https://prove2.me/theorems/fee9befb-ae24-4438-a0a9-0149d558a018
-- title:
--   History-based full-information learners and alternating regret
-- statement:
--   Let A be a measurable action space, L a space of revealed losses, and Omega a measurable private-seed space. A history learner selects its next action measurably from its private seed and the entire finite sequence of past losses. Its terminal action uses all T revealed losses. For a nonempty action set X, real losses f_t, and actions x_1 through x_(T+1), alternating regret is
--
--   $$R_T=\sup_{u\in X}\sum_{t=1}^T\bigl(f_t(x_t)+f_t(x_{t+1})-2f_t(u)\bigr).$$
--
--   The same interface applies to experts and continuous action sets. The supremum is evaluated on each trajectory before any expectation. The bound theorems use nonempty domains and bounded losses, making this a finite real supremum.
--
--   **Formalization Note** Actions and losses are zero-based in the arrays; `response learner f T` is the terminal action. No guarantee is a field of a learner. Measurability of each fixed-history seed response suffices for all oblivious fixed sequences and finitely supported environments used in the lower bounds.
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 3 / PDF p. 4, Section 2 protocol; Eq. (1), printed p. 4 / PDF p. 5; SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

/-- A full-information learner: action t+1 uses precisely t revealed losses and a private seed.
For each fixed history its action is a measurable function of that seed. No bound on regret
or property of any particular algorithm is part of this interface. -/
structure HistoryLearner (A L Ω : Type) [MeasurableSpace A] [MeasurableSpace Ω] where
  choose : (t : ℕ) → (Fin t → L) → Ω → A
  measurable_choose : ∀ t h, Measurable (choose t h)

/-- Zero-based actions: response at t is the paper's action x_(t+1), also when t=T. -/
def response {A L Ω : Type} [MeasurableSpace A] [MeasurableSpace Ω]
    (learner : HistoryLearner A L Ω) (f : ℕ → L) (t : ℕ) (ω : Ω) : A :=
  learner.choose t (fun i => f i.val) ω

/-- The hindsight supremum is computed on each realized trajectory, before expectation.
All uses impose nonempty action sets and bounded losses; no attainment is imposed. -/
def alternatingRegret {A : Type} (X : Set A) (T : ℕ)
    (f : ℕ → A → ℝ) (x : ℕ → A) : ℝ :=
  sSup ((fun u => ∑ t ∈ Finset.range T, (f t (x t) + f t (x (t+1)) - 2*f t u)) '' X)

/-- Each term is a genuine comparator regret, useful for matching the source definition. -/
def comparatorRegret {A : Type} (T : ℕ) (f : ℕ → A → ℝ) (x : ℕ → A) (u : A) : ℝ :=
  ∑ t ∈ Finset.range T, (f t (x t) + f t (x (t+1)) - 2*f t u)

end MinimaxAltRegret.Main


