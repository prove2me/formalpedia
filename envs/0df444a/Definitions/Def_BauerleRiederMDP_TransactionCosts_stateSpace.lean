-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_stateSpace
-- name    : BauerleRiederMDP_TransactionCosts_stateSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:20.787432+00:00
-- url     : https://prove2.me/theorems/c7f82db9-c3be-4a10-8e6d-015c3d13d2f4
-- title:
--   State space $E=\mathbb R_+^2$ of bond and stock holdings
-- statement:
--   The state space of the transaction cost model is
--   $$E:=\mathbb R_+^2=\{x=(x_0,x_1): x_0\ge 0,\ x_1\ge 0\},$$
--   where $x_0$ and $x_1$ are the amounts held in the bond and in the stock. Short sales are not allowed.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.5, p.106 (PDF 120)

import Mathlib

namespace BauerleRiederMDP.TransactionCosts

/-- The state space `E := ℝ²₊` of the transaction cost model (Bäuerle & Rieder 2011, §4.5,
p.106, PDF 120): a state `x = (x₀, x₁)` holds the amount `x₀ ≥ 0` in the bond and `x₁ ≥ 0` in
the stock ("short-sellings are not allowed").

**Formalization Note.** `E` is a subset of `ℝ × ℝ`; functions on `E` are functions on `ℝ × ℝ`
of which only the values on `E` are constrained or used. -/
def stateSpace : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2}

end BauerleRiederMDP.TransactionCosts


