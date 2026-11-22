-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
-- name    : Formalism_SubspaceCounting_TopsChoiceSecondBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:10.717215+00:00
-- url     : https://prove2.me/theorems/b2c60fb9-521d-44ad-b376-53fe84f4b9be
-- title:
--   Tops Choice Second Bound
-- statement:
--   Definitions and structural lemmas for Tops Choice Second Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/TopsChoiceSecondBound.lean

import Definitions.Def_Formalism_SubspaceCounting_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.G0
def condProb (n : ℕ) (δ : ℝ) (A : Finset ℕ → Prop) : ℝ := by
  classical
  exact ∑ T ∈ (Finset.range n).powerset,
    if 0 ∈ T ∧ A T then δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) else 0
def TopsChoicePartA : Prop :=
  ∀ (n : ℕ) (δ : ℝ) (L₂ K : ℕ), 2 ≤ n → 0 ≤ δ → 1 ≤ L₂ → (L₂ : ℝ) * δ ≤ 1 →
    condProb n δ (fun T => ¬ CondA n T L₂ K) ≤ n * (L₂.choose K : ℝ) * δ ^ K
def TopsChoiceSecondBound : Prop :=
  ∀ (n : ℕ) (δ : ℝ) (L₂ r N₁ : ℕ), 2 ≤ n → Even n → 0 ≤ δ → 1 ≤ L₂ →
    (L₂ : ℝ) * δ ≤ 1 → 1 ≤ r → 3 * r ≤ N₁ →
    condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) ≤
      n * (1 - (1 / 2 : ℝ) ^ (3 * r) * (1 - L₂ * δ) ^ (3 * r)) ^ (N₁ / (3 * r) - 1)
def TopsChoiceThirdBound : Prop :=
  ∀ (n : ℕ) (δ : ℝ) (G : ℕ), 2 ≤ n → 0 ≤ δ → δ ≤ 1 →
    condProb n δ (fun T => ¬ CondC n T G) ≤ n * (1 - δ) ^ G
def SmallCardCondProbBound : Prop :=
  ∀ (n : ℕ) (δ : ℝ) (N₁ : ℕ), 2 ≤ n → 0 ≤ δ → δ ≤ 1 →
    condProb n δ (fun T => T.card < N₁) ≤ binLower n δ N₁
end Formalism.G0


