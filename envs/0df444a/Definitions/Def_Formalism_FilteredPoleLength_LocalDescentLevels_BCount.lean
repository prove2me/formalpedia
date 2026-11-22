-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_BCount
-- name    : Formalism_FilteredPoleLength_LocalDescentLevels_BCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:54.836171+00:00
-- url     : https://prove2.me/theorems/3cfb4cf8-a856-41c6-88bc-205a1da50885
-- title:
--   BCount
-- statement:
--   Definitions and structural lemmas for BCount, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/BCount.lean

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LatticeBaseChangeAlt
open Finset
noncomputable def slackEquiv (D k : ℕ) :
    {α : Fin D → ℕ // ∑ i, α i ≤ k} ≃ {β : Fin (D + 1) → ℕ // ∑ i, β i = k} where
  toFun α := ⟨Fin.cons (k - ∑ i, α.1 i) α.1, by
    have := α.2
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega⟩
  invFun β := ⟨Fin.tail β.1, by
    have := β.2
    rw [Fin.sum_univ_succ] at this
    simp only [Fin.tail]
    omega⟩
  left_inv α := by
    apply Subtype.ext
    simp only [Fin.tail_cons]
  right_inv β := by
    apply Subtype.ext
    have h := β.2
    rw [Fin.sum_univ_succ] at h
    have h0 : k - ∑ i, Fin.tail β.1 i = β.1 0 := by
      simp only [Fin.tail]
      omega
    simp only [h0, Fin.cons_self_tail]
end Formalism.LatticeBaseChangeAlt


