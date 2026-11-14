-- Prove2me | Definitions.Def_CountingLLL_ContractedCost
-- name    : CountingLLL_ContractedCost
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T08:56:26.112826+00:00
-- url     : https://prove2.me/theorems/e5ff4516-7a5d-4d77-a260-378683464ddc
-- title:
--   Weighted changes in the contracted reciprocal-test walk
-- statement:
--   For the abstract absorbed walk of the paper, count the upward changes before each time and let the current counter be the initial value $j$ plus that count. An active contracted change has weight equal to the reciprocal of the current counter. The module defines the total weighted changes, the total restricted to upward changes, and their expectations. The source quantity $M$ is the expected total weighted changes starting from level three and counter two. All quantities refer to the suppressed-return walk; no coupling with the operational machine is asserted.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
set_option autoImplicit false

/-! Weighted changes in the suppressed-return contracted walk of #442,
Lemma 6.5. The source's quantity M is `expectedWeightedChanges θ 3 2`.
These are properties of the abstract walk; connecting it to the small-step
ReciprocalTest remains separate. -/
namespace CountingLLL.ContractedWalk
open MeasureTheory
open scoped ENNReal BigOperators

/-- Number of upward changes before time t. -/
def upwardBefore (ω : Tape) (start t : ℕ) : ℕ :=
  ∑ k ∈ Finset.range t, if level ω start k ≠ 0 ∧ ω k = true then 1 else 0

/-- Reciprocal counter just before an active change, and zero after absorption. -/
noncomputable def changeWeight (ω : Tape) (start j t : ℕ) : ℝ≥0∞ :=
  if level ω start t = 0 then 0 else ((j + upwardBefore ω start t : ℕ) : ℝ≥0∞)⁻¹

/-- Sum of the reciprocal counter before every contracted change. -/
noncomputable def weightedChanges (ω : Tape) (start j : ℕ) : ℝ≥0∞ :=
  ∑' t, changeWeight ω start j t

/-- Sum of the same weights over upward changes only. -/
noncomputable def weightedIncreases (ω : Tape) (start j : ℕ) : ℝ≥0∞ :=
  ∑' t, changeWeight ω start j t * (if ω t then 1 else 0)

noncomputable def expectedWeightedChanges (θ : ℝ≥0∞) (start j : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, weightedChanges ω start j ∂tapeLaw θ

noncomputable def expectedWeightedIncreases (θ : ℝ≥0∞) (start j : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, weightedIncreases ω start j ∂tapeLaw θ
end CountingLLL.ContractedWalk


