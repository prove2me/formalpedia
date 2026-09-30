-- Prove2me | Definitions.Def_ShiQMAErrorIteration
-- name    : ShiQMAErrorIteration
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-30T06:07:49.913462+00:00
-- url     : https://prove2.me/theorems/bf80d5e5-e7c5-4a60-9ce8-f5c0f5c40653
-- title:
--   Numerical error model for majority-of-three QMA amplification
-- statement:
--   Defines the majority-of-three error map $e\mapsto3e^2-2e^3$, the error sequence beginning at $1/3$, and the logarithmic round schedule $R(m)=\lfloor\log_2m\rfloor+4$. The following theorem nodes establish error and copy-count bounds for this model.
-- source:
--   Marriott and Watrous, Quantum Arthur–Merlin Games (2005), Section 3, Theorem 3, https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf; original Lean proof: Yueheng Shi, AMPUNI-error-iteration.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace ShiQMAErrorIteration

/-- Failure probability of a majority of three independent trials. -/
def majorityError (e : ℝ) : ℝ := 3 * e ^ 2 - 2 * e ^ 3

/-- The scalar error recurrence, starting at the usual QMA error threshold. -/
noncomputable def error : Nat → ℝ
  | 0 => 1 / 3
  | r + 1 => majorityError (error r)

/-- A logarithmic number of rounds suffices for the target exponential error. -/
def roundsFor (m : Nat) : Nat := Nat.log 2 m + 4

end ShiQMAErrorIteration


