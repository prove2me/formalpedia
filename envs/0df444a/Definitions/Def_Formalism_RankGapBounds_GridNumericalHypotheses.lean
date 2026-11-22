-- Prove2me | Definitions.Def_Formalism_RankGapBounds_GridNumericalHypotheses
-- name    : Formalism_RankGapBounds_GridNumericalHypotheses
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:36.286642+00:00
-- url     : https://prove2.me/theorems/74e59df4-b549-4ad4-8ccc-caf06485cff3
-- title:
--   Grid Numerical Hypotheses
-- statement:
--   Definitions and structural lemmas for Grid Numerical Hypotheses, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/GridNumericalHypotheses.lean

import Definitions.Def_Formalism_RankGapBounds_RankAndGapBounds
import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_ConjInOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.RankGapBounds.V4
open Formalism.RankGapBounds.LocalQuadraticParts Formalism.RankGapBounds.ExistsSmulMemTer
def RankGapPrintedLemma : Prop :=
  ∀ (α ι : Type) [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)],
    0 < δ → δ ≤ 1 → 16 ≤ δ * Fintype.card α → 0 ≤ β → (∀ p, 0 ≤ ω p) →
    (∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T), wt δ T ≤ β * δ) →
    ∃ T : Finset α, δ * Fintype.card α / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card α ∧
      ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤ 4 * β * δ * Fintype.card α * ∑ p, ω p
def ConjInOrbitAll : Prop :=
  ∀ (e : ℕ) (φ : GG e), cc e ∈ AddSubgroup.zmultiples φ ↔ φ = cc e
def RankGapDecayHypothesis : Prop :=
  ∀ n m γ : ℝ, 3 ≤ n → 1 ≤ m → m ≤ n → n ^ 7 ≤ γ →
    120 * n * (m / 2) ^ ((3 : ℝ) / 2) ≤ γ
structure GridNumericalHypotheses (k m t r : ℕ) (h₀ : ℝ) : Prop where
  k_even : Even k
  m_even : Even m
  m_pos : 1 ≤ m
  r_def : r + 1 = k + m
  k_ge : m + 3 ≤ k
  t_odd : Odd t
  t_gt_m : 3 * m < t
  t_gt_r : r + 4 < t
  h₀_big : (t : ℝ) + 2 * ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < h₀
def RankGapBoundPair : Prop :=
  ∀ (k m t r : ℕ) (h₀ γ : ℝ), GridNumericalHypotheses k m t r h₀ →
    2 * ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 + 2 * ((r + 6 : ℕ) : ℝ) + 2 < γ →
    (∀ i j : ℕ, i ≤ m → j ≤ m → r + j * t + i * (r + 6) < k + m * (t + (r + 6) + 1)) ∧
    (∀ i : ℕ, i ≤ m → (r + 1) + i * (r + 5) < k + m * (t + (r + 6) + 1)) ∧
    (∀ M : ℕ, M < k + m * (t + (r + 6) + 1) →
      (M : ℝ) ^ 3 < (h₀ - t) / 2 ∧ (M : ℝ) ^ 3 < γ / 2 - ((r + 6 : ℕ) : ℝ)) ∧
    ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < (h₀ - t) / 2 ∧
    ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < γ / 2 - ((r + 6 : ℕ) : ℝ) ∧
    (((r + 6 : ℕ) : ℝ) + 1) / 2 ≤ γ / 2 - 1 ∧ ((r + 6 : ℕ) : ℝ) / 2 ≤ γ / 2 - 1 ∧
    γ / 2 - ((r + 6 : ℕ) : ℝ) ≤ γ / 2 - 1 - (((r + 6 : ℕ) : ℝ) - 1) / 2
end Formalism.RankGapBounds.V4


