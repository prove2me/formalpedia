-- Prove2me | Definitions.Def_Formalism_ResultantValuation_WindowValuation
-- name    : Formalism_ResultantValuation_WindowValuation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:08.350813+00:00
-- url     : https://prove2.me/theorems/e9b6d8cb-2ebb-46bd-a892-f09ee71198cd
-- title:
--   Window Valuation
-- statement:
--   Definitions and structural lemmas for Window Valuation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/WindowValuation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.ResultantValuation
def LTEUnit : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ i : ℕ, 1 ≤ i → ((u ^ i - 1).valuation : ℕ) = 1 + padicValNat l i
def WindowValuation : Prop :=
  ∀ l b S : ℕ, l.Prime → 1 ≤ b →
    ((∑ i ∈ Finset.Ico b (b + S), padicValNat l i : ℕ) : ℝ) ≤
      (S : ℝ) / ((l : ℝ) - 1) + (Nat.log l (b + S) : ℝ)
def WindowKappaEq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ b S : ℕ, 1 ≤ b →
      (∏ i ∈ Finset.Ico b (b + S), (1 - u ^ i)).valuation =
        S + ∑ i ∈ Finset.Ico b (b + S), padicValNat l i
def WindowKappa : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ b S : ℕ, 1 ≤ b →
      ((∏ i ∈ Finset.Ico b (b + S), (1 - u ^ i)).valuation : ℝ) ≤
        (S : ℝ) + (S : ℝ) / ((l : ℝ) - 1) + (Nat.log l (b + S) : ℝ)
end Formalism.ResultantValuation


