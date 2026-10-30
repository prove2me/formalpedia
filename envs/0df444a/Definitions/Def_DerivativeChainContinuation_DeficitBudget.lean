-- Prove2me | Definitions.Def_DerivativeChainContinuation_DeficitBudget
-- name    : DerivativeChainContinuation_DeficitBudget
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T18:04:07.93371+00:00
-- url     : https://prove2.me/theorems/8bc058e2-4413-4542-a97f-668754ea4436
-- title:
--   Degree-weighted variance deficit
-- statement:
--   For a scalar row sequence $V_m$, define the consecutive degree-weighted deficit $(m-2)V_m-(m-1)V_{m-1}$. It supplies the finite telescoping form used by the actual-polynomial transverse budget. The degree factors use natural-number truncated subtraction, as in the source definition.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/DeficitBudget.lean#L6-L7

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators

noncomputable def degreeDeficit (V : ℕ → ℝ) (m : ℕ) : ℝ :=
  (m-2 : ℕ) * V m - (m-1 : ℕ) * V (m-1)








end DerivativeChainContinuation


