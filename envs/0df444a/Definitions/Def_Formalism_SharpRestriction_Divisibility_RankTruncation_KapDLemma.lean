-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_RankTruncation_KapDLemma
-- name    : Formalism_SharpRestriction_Divisibility_RankTruncation_KapDLemma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:42.970795+00:00
-- url     : https://prove2.me/theorems/7599bc99-ec4d-4dc6-b240-a84eefc7ce3f
-- title:
--   Kap DLemma
-- statement:
--   Definitions and structural lemmas for Kap DLemma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/RankTruncation/KapDLemma.lean

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
namespace ConditionalKappaBounds.KapD
def sigParC (k m : ℕ) (v : Fin (k - 1) → ℚ) (b : Fin m → ℚ) (i : ℕ) : ℚ :=
  if h : i < k - 1 then v ⟨i, h⟩
  else if hb : i - (k - 1) < m then -b ⟨i - (k - 1), hb⟩ else 0
def aPlusC (k m t j : ℕ) (v : Fin (k - 1) → ℚ) (b : Fin m → ℚ) (e : ℚ) (i : ℕ) : ℚ :=
  sigParC k m v b i + e - (((k + m - 1 + t : ℕ) : ℚ) - 1 - 2 * (i : ℚ)) / 2 -
    (((k : ℚ) + j - 1) - ((m : ℚ) - j)) / 2
def aMinusC (m t j : ℕ) (b : Fin m → ℚ) (e : ℚ) (c : ℕ) : ℚ :=
  (if h : j + c < m then b ⟨j + c, h⟩ else 0) - e - ((t : ℚ) + 1 + 2 * (c : ℚ)) / 2
def DProp : Prop := ∃ C : ℝ, ∀ (k m t j : ℕ), m + 3 ≤ k → 1 ≤ j → j ≤ m →
  ∀ (v : Fin (k - 1) → ℚ) (b : Fin m → ℚ) (e : ℚ) (S η : ℝ),
    (∀ i, 0 ≤ ((v i : ℚ) : ℝ) ∧ ((v i : ℚ) : ℝ) ≤ S) → (∀ i, |((b i - e : ℚ) : ℝ)| ≤ η) →
    |((((∑ i : Fin (k + j - 1), aPlusC k m t j v b e i) + ∑ c : Fin (m - j), aMinusC m t j b e c : ℚ)) : ℝ) -
        ((k : ℝ) - 1) * ((e : ℚ) : ℝ)| ≤
      C * ((k : ℝ) * S + (m : ℝ) * η + (k : ℝ) * (((k + m * (t + 1) : ℕ) : ℝ) + t))
end ConditionalKappaBounds.KapD


