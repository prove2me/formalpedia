-- Prove2me | Definitions.Def_Formalism_GrowthSums_StatementC
-- name    : Formalism_GrowthSums_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:27:47.355994+00:00
-- url     : https://prove2.me/theorems/8e5f2242-1729-4dff-a2d7-ccff2a9098fd
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/StatementC.lean

import Mathlib
import Definitions.Def_Formalism_GrowthSums_StatementA
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
open Finset
namespace Formalism.GrowthSums
def LogCoefVal : Prop :=
  ∀ p t s : ℕ, p.Prime → 5 ≤ p → 1 ≤ s →
    ((s : ℝ) + 1) / 4 ≤
      (padicValRat p (((p ^ (t + 1) : ℕ) : ℚ) ^ s * (∑ y ∈ Ico 1 (p ^ (t + 1)), 1 / (y : ℚ) ^ s) / s) : ℝ)
        - 1 / ((p : ℝ) - 1)
def ServiceSplit : Prop :=
  ∀ (m : ℕ) (g g0 Pr : Fin m → ℝ),
    (∑ j, max (g j - Pr j - g0 j) 0) + ∑ j, g0 j = ∑ j, max (g j - Pr j) (g0 j) ∧
    ∑ j, max (g j - Pr j) (g0 j) =
      ∑ j ∈ univ.filter (fun j => g0 j ≤ g j - Pr j), (g j - Pr j) +
        ∑ j ∈ univ.filter (fun j => ¬ g0 j ≤ g j - Pr j), g0 j
end Formalism.GrowthSums


