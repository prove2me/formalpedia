-- Prove2me | Definitions.Def_Formalism_ResultantValuation_PrimePairDyadicDisjointAlt
-- name    : Formalism_ResultantValuation_PrimePairDyadicDisjointAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:44.372802+00:00
-- url     : https://prove2.me/theorems/b145e8b7-0f09-4718-8926-a7b60b2a03e1
-- title:
--   Prime Pair Dyadic Disjoint Alt
-- statement:
--   Definitions and structural lemmas for Prime Pair Dyadic Disjoint Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/PrimePairDyadicDisjointAlt.lean

import Definitions.Def_Formalism_ResultantValuation_PrimePairDisjointBB
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
def PrimePairDyadicDisjoint : Prop :=
  ∀ (adm : ℕ → Prop) (N : ℕ) (X cond C C' : ℝ), 8 ≤ N → 0 < X → 0 < cond →
    (∃ Y : ℝ, X * cond ^ (-C') ≤ Y ∧ Y ≤ X ∧
      Y * cond ^ (-C) ≤ (Nat.card {p : ℕ // p.Prime ∧ adm p ∧ Y ≤ p ∧ (p : ℝ) ≤ 2 * Y} : ℝ)) →
    (N : ℝ) ^ 4 * cond ^ C ≤ (X * cond ^ (-C')) ^ (1 / 4 : ℝ) →
    ∃ Y : ℝ, X * cond ^ (-C') ≤ Y ∧ Y ≤ X ∧
      ∃ g₁ g₂ : ℕ, g₁.Prime ∧ g₂.Prime ∧ adm g₁ ∧ adm g₂ ∧
        Y ≤ g₁ ∧ (g₁ : ℝ) ≤ 2 * Y ∧ Y ≤ g₂ ∧ (g₂ : ℝ) ≤ 2 * Y ∧
        g₁ ≠ g₂ ∧ Disjoint (Formalism.CyclotomicNorms.BB N g₁) (Formalism.CyclotomicNorms.BB N g₂)
end Formalism.ResultantValuation


