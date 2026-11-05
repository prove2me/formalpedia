-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_admissibleSet
-- name    : BauerleRiederMDP_TransactionCosts_admissibleSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:19.188044+00:00
-- url     : https://prove2.me/theorems/b54d0e58-ba3a-4575-96b2-9790a213d508
-- title:
--   Admissible holdings after transaction $D(x)$, (4.23)
-- statement:
--   For a state $x=(x_0,x_1)\in E$ and transaction cost rate $c$, the set of admissible bond and stock holdings after transaction is
--   $$D(x_0,x_1)=\{(a_0,a_1)\in\mathbb R_+^2 : a_0+a_1\le x_0+x_1-c|a_1-x_1|\}. \tag{4.23}$$
--   Here $a_0$ and $a_1$ are the amounts in the bond and in the stock after transaction; the cost $c|a_1-x_1|$ of changing the stock position is paid from the bond.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.5, eq. (4.23), p.106 (PDF 120)

import Mathlib

namespace BauerleRiederMDP.TransactionCosts

/-- The set of admissible actions (4.23) of Bäuerle & Rieder (2011), §4.5, p.106 (PDF 120):
for a state `x = (x₀, x₁)` and transaction cost rate `c`,
`D(x₀, x₁) = {(a₀, a₁) ∈ A | a₀ + a₁ ≤ x₀ + x₁ − c|a₁ − x₁|}` with `A := ℝ²₊`; `a₀` and `a₁`
are the amounts held in the bond and in the stock after transaction. -/
def admissibleSet (c : ℝ) (x : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {a | 0 ≤ a.1 ∧ 0 ≤ a.2 ∧ a.1 + a.2 ≤ x.1 + x.2 - c * |a.2 - x.2|}

end BauerleRiederMDP.TransactionCosts


