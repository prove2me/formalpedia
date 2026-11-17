-- Prove2me | Definitions.Def_APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over_Vocabulary
-- name    : APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-17T03:35:55.632741+00:00
-- url     : https://prove2.me/theorems/6cc1f88d-1df5-4d85-bcf1-029ac16bb45f
-- title:
--   Model vocabulary — Infinite order of the specified 3-4-5 rotation
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   Integer recurrences for powers of 3+4i prove nonzero coordinates, distinct rational-circle points and no finite state realization of that orbit. Injective self-maps on finite types are periodic. The angle is chosen; density, a continuum, physical states and K3 are not established.
--
--   **Supplied data and hypotheses**
--
--   - Every parameter and hypothesis in the exact source declaration remains exposed; no author input is adopted.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over; Pullbacks v46, SHA-256 e73854102ad9e697e4bfaad3364866c49b0773357cf47209b364d0dccad08f7f. Theorems.Thm_APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over; pullbacks v46; SHA-256 e73854102ad9e697e4bfaad3364866c49b0773357cf47209b364d0dccad08f7f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finite.Prod
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace APFPaper5.K3.ThreeFourFive

/-- The whole numbers of `n` turns: `(3 + 4i)^n = a + b i`. -/
def pw : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (3 * (pw n).1 - 4 * (pw n).2, 4 * (pw n).1 + 3 * (pw n).2)


























/-- The place `n` turns on: where `n` turns carry the point `(1, 0)`. -/
def place (n : ℕ) : ℚ × ℚ := (((pw n).1 : ℚ) / 5 ^ n, ((pw n).2 : ℚ) / 5 ^ n)











end APFPaper5.K3.ThreeFourFive


