-- Prove2me | Definitions.Def_Formalism_DropLevelBounds_ThBounds
-- name    : Formalism_DropLevelBounds_ThBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:52.379792+00:00
-- url     : https://prove2.me/theorems/5f0ba6b3-f7b5-4a55-aa71-da95df0210a2
-- title:
--   Th Bounds
-- statement:
--   Definitions and structural lemmas for Th Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DropLevelBounds/ThBounds.lean

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
open scoped BigOperators
namespace Formalism.UnitaryBoundIntegral
def thl (k l : ℕ) : ℝ :=
  sSup {t : ℝ | ∃ i : ℕ, Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i ∧ t = ((l : ℝ) ^ i)⁻¹}
def ThBounds : Prop :=
  ∀ (k l : ℕ), 1 ≤ k → 2 ≤ l →
    thl k l ≤ ((l : ℝ) ^ 3)⁻¹ ∧ thl k l < ((k : ℝ) ^ ((3 : ℝ) / 2))⁻¹ ∧
      ((k : ℝ) < (l : ℝ) ^ 2 → thl k l = ((l : ℝ) ^ 3)⁻¹)
def SumTh : Prop :=
  ∃ C : ℝ, ∀ (k N : ℕ), 1 ≤ k →
    (∑ l ∈ (Finset.range (N + 1)).filter Nat.Prime, thl k l * Real.log l) ≤ C / k
end Formalism.UnitaryBoundIntegral


