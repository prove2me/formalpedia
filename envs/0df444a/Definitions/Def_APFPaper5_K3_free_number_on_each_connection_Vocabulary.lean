-- Prove2me | Definitions.Def_APFPaper5_K3_free_number_on_each_connection_Vocabulary
-- name    : APFPaper5_K3_free_number_on_each_connection_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-17T03:35:58.998904+00:00
-- url     : https://prove2.me/theorems/26e078b9-f0e6-4a9a-a70c-610e336af882
-- title:
--   Model vocabulary — Off-diagonal freedom in supplied real tables
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   For a supplied finite real table, single basis reads fix its diagonal and symmetric pair reads determine the remaining entries. A quadratic bill on the unit circle is flat exactly when its cross price is zero; positive cross price fixes the minimizing table, not a unique signed vector. These are algebraic table and circle results, not constructed physical states, chances, or prices.
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
--   Theorems.Thm_APFPaper5_K3_free_number_on_each_connection; Pullbacks v46, SHA-256 9a7e70cb6a988b5fe9640fbbbd2eb2106425cc5f870aa5a31e48706f7f67de9d. Theorems.Thm_APFPaper5_K3_free_number_on_each_connection; pullbacks v46; SHA-256 9a7e70cb6a988b5fe9640fbbbd2eb2106425cc5f870aa5a31e48706f7f67de9d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Algebra.Order.Ring.Cast

set_option autoImplicit false

namespace APFPaper5.K3.Connections

open Finset

section Tables

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pairing of a table with two combinations of alternatives. -/
def pair (W : ι → ι → ℝ) (x y : ι → ℝ) : ℝ := ∑ a, ∑ b, W a b * (x a * y b)

/-- The read of a table at a combination of alternatives. -/
def read (W : ι → ι → ℝ) (x : ι → ℝ) : ℝ := pair W x x

/-- One alternative alone. -/
def alt (i : ι) : ι → ℝ := fun a => if a = i then 1 else 0

/-- A table is symmetric. -/
def IsSymm (W : ι → ι → ℝ) : Prop := ∀ a b, W a b = W b a















/-- Add `t` to the connection between `i` and `j`, in both orders. -/
def bump (W : ι → ι → ℝ) (i j : ι) (t : ℝ) : ι → ι → ℝ :=
  fun a b => W a b + if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then t else 0



















/-- Change the sign of some alternatives. -/
def flip (s : ι → ℝ) (W : ι → ι → ℝ) : ι → ι → ℝ := fun a b => s a * s b * W a b





end Tables

section Mark

/-- The bill of the place `(u, v)` on the circle of one mark, under a cost table with `eps` on each side
and `k` on the connection. -/
def bill (eps k u v : ℝ) : ℝ := eps * (u * u) + eps * (v * v) + 2 * k * (u * v)

































end Mark

end APFPaper5.K3.Connections


