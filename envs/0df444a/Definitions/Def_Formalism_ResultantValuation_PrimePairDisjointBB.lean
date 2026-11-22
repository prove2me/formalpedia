-- Prove2me | Definitions.Def_Formalism_ResultantValuation_PrimePairDisjointBB
-- name    : Formalism_ResultantValuation_PrimePairDisjointBB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:45.674109+00:00
-- url     : https://prove2.me/theorems/7bb1810e-94c0-4dc3-a374-f718a9e35744
-- title:
--   Prime Pair Disjoint BB
-- statement:
--   Definitions and structural lemmas for Prime Pair Disjoint BB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/PrimePairDisjointBB.lean

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
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
def PrimePairDisjointBB : Prop :=
  ∀ (adm : ℕ → Prop) (N : ℕ) (Y cond C : ℝ), 8 ≤ N → 0 < Y → 0 < cond →
    Y * cond ^ (-C) ≤ (Nat.card {p : ℕ // p.Prime ∧ adm p ∧ Y ≤ p ∧ (p : ℝ) ≤ 2 * Y} : ℝ) →
    (N : ℝ) ^ 4 * cond ^ C ≤ Y ^ (1 / 4 : ℝ) →
    ∃ g₁ g₂ : ℕ, g₁.Prime ∧ g₂.Prime ∧ adm g₁ ∧ adm g₂ ∧
      Y ≤ g₁ ∧ (g₁ : ℝ) ≤ 2 * Y ∧ Y ≤ g₂ ∧ (g₂ : ℝ) ≤ 2 * Y ∧
      g₁ ≠ g₂ ∧ Disjoint (Formalism.CyclotomicNorms.BB N g₁) (Formalism.CyclotomicNorms.BB N g₂)
end Formalism.ResultantValuation


