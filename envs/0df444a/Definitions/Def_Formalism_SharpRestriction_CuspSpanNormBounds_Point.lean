-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_Point
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:08.065812+00:00
-- url     : https://prove2.me/theorems/1dd253e1-efc8-4151-b4ea-8acd7691a922
-- title:
--   Point
-- statement:
--   Definitions and structural lemmas for Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/Point.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.S
def ptEntry {K : Type*} [Zero K] : List (K × ℕ) → ℕ → ℕ → K
  | [], _, _ => 0
  | (t, s) :: bs, i, j =>
    if i < s ∧ j < s then (if i + j + 1 = s then t else 0)
    else if s ≤ i ∧ s ≤ j then ptEntry bs (i - s) (j - s) else 0
def Point (K : Type*) [Zero K] (i : ℕ) : Type _ :=
  {bs : List (K × ℕ) // (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) ∧ (bs.map Prod.snd).sum = i}
def ptMat {K : Type*} [Zero K] {i : ℕ} (p : Point K i) : Matrix (Fin i) (Fin i) K :=
  fun a b => ptEntry p.1 a.val b.val
end Formalism.MainNotions.S


