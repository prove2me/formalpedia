-- Prove2me | Definitions.Def_KarlinDynamicProgramming_Uniqueness_Model
-- name    : KarlinDynamicProgramming_Uniqueness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:53:38.414169+00:00
-- url     : https://prove2.me/theorems/72d06558-1d8e-46a7-b6ca-36218c8a37f9
-- title:
--   Stationary deterministic model, strategies, trajectories and weights
-- statement:
--   The stationary data consist of a nonnegative jointly continuous real reward L, separately continuous transitions T, and a positive continuous real weight P. Strategies are all infinite decision sequences. The trajectory begins at the initial state; its Nth term is the state after N decisions, and its weight is the product of the first N decision weights. Topological Hausdorff and compactness assumptions are supplied by the theorem binders. Indices are zero based; the empty product is one.
-- source:
--   Karlin, The Structure of Dynamic Programing Models, Naval Research Logistics Quarterly 2(4) (1955), 285–294, doi:10.1002/nav.3800020408; Formal structure, PDF 2–3 / printed 286–287

import Mathlib

namespace KarlinDynamicProgramming.Uniqueness

/-- Stationary deterministic data, with precisely the source's separate continuity. -/
structure Model (Ω D : Type*) [TopologicalSpace Ω] [TopologicalSpace D] where
  L : Ω → D → ℝ
  T : D → Ω → Ω
  P : D → ℝ
  reward_nonneg : ∀ ω a, 0 ≤ L ω a
  reward_continuous : Continuous (fun p : Ω × D => L p.1 p.2)
  transition_state_continuous : ∀ a, Continuous (T a)
  transition_decision_continuous : ∀ ω, Continuous (fun a => T a ω)
  weight_pos : ∀ a, 0 < P a
  weight_continuous : Continuous P

/-- All infinite decision sequences, with the usual function/product topology. -/
abbrev Strategy (D : Type*) := ℕ → D

variable {Ω D : Type*} [TopologicalSpace Ω] [TopologicalSpace D]

/-- State after exactly N decisions; source state ωₙ is trajectory at n-1. -/
def trajectory (m : Model Ω D) (ω : Ω) (s : Strategy D) : ℕ → Ω
  | 0 => ω
  | N + 1 => m.T (s N) (trajectory m ω s N)

/-- Empty product is one. -/
def weight (m : Model Ω D) (s : Strategy D) (N : ℕ) : ℝ :=
  ∏ j ∈ Finset.range N, m.P (s j)

end KarlinDynamicProgramming.Uniqueness


