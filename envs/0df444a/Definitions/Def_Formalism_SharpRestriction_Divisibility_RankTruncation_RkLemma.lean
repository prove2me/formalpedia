-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_RankTruncation_RkLemma
-- name    : Formalism_SharpRestriction_Divisibility_RankTruncation_RkLemma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:52.276425+00:00
-- url     : https://prove2.me/theorems/3a5b011e-13a7-4fd4-a672-a3505031343e
-- title:
--   Rk Lemma
-- statement:
--   Definitions and structural lemmas for Rk Lemma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/RankTruncation/RkLemma.lean

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
namespace ConditionalKappaBounds.Rk
def RkProp : Prop := ∀ (dp f m r t : ℕ) (x Ct q d rd CRd : ℝ), 1 < x → 6 ≤ CRd →
  dp ≤ 2 * f * m → f ≤ r → m ≤ r → r < t → 2 ≤ t → (t : ℝ) ≤ x ^ Ct →
  x ^ (2 * Ct + 5) < q → x ^ (2 * Ct + 5) < d → Real.sqrt (q * d) ≤ rd →
  (dp : ℝ) ^ 2 ≤ rd ^ (CRd - 2)
end ConditionalKappaBounds.Rk


