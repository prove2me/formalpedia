-- Prove2me | Definitions.Def_Formalism_DropLevelBounds_SumAdd
-- name    : Formalism_DropLevelBounds_SumAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:07.789436+00:00
-- url     : https://prove2.me/theorems/175c4ac7-8a3c-41c9-a3ca-02e171a1301e
-- title:
--   Sum Add
-- statement:
--   Definitions and structural lemmas for Sum Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DropLevelBounds/SumAdd.lean

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
def addl (k n f : ℕ) (l1 : ℝ) (l : ℕ) : ℝ :=
  if (l : ℝ) ^ 2 < k then (f : ℝ) * (n : ℝ) ^ 3 * (k : ℝ) ^ 3 * Real.log k
  else if (l : ℝ) < l1 then (f : ℝ) * (n : ℝ) ^ 3 * l * Real.log ((n : ℝ) * l) else 0
def SumAdd : Prop :=
  ∃ C : ℝ, ∀ (k n f N : ℕ) (T m b L : ℝ), 1 ≤ k → 1 ≤ n → 1 ≤ f → 0 < T → 0 < m → 0 < b → 0 < L →
    Real.log ((n : ℝ) * (Real.sqrt (m * b / (T * f * (n : ℝ) ^ 3)) / L)) ≤ L ^ 2 →
    T * f * (n : ℝ) ^ 3 * (k : ℝ) ^ 4 ≤ m * b →
    T * (∑ l ∈ (Finset.range (N + 1)).filter Nat.Prime,
      addl k n f (Real.sqrt (m * b / (T * f * (n : ℝ) ^ 3)) / L) l * Real.log l) ≤ C * m * b
end Formalism.UnitaryBoundIntegral


