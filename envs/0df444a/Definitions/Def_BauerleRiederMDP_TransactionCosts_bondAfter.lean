-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_bondAfter
-- name    : BauerleRiederMDP_TransactionCosts_bondAfter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:23.820884+00:00
-- url     : https://prove2.me/theorems/528583ed-4500-46b9-bf82-15440660240d
-- title:
--   Upper boundary $h(x,a)$ of $D(x)$
-- statement:
--   For a state $x=(x_0,x_1)$ and a stock holding $a$ after transaction,
--   $$h(x,a)=\begin{cases}x_0+(1-c)(x_1-a), & 0\le a\le x_1,\\ x_0+(1+c)(x_1-a), & x_1<a\le x_1+\frac{x_0}{1+c}.\end{cases}$$
--   It is the largest bond holding after transaction compatible with stock holding $a$: selling stock earns $(1-c)$ per unit, buying costs $(1+c)$ per unit.
--
--   **Formalization Note** The formula is defined for every real $a$; statements only use it on $0\le a\le x_1+x_0/(1+c)$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.5, p.108 (PDF 122)

import Mathlib

namespace BauerleRiederMDP.TransactionCosts

/-- The upper boundary `h(x, a₁)` of `D(x)` (Bäuerle & Rieder 2011, §4.5, p.108, PDF 122): the
largest bond holding after transaction when the stock holding after transaction is `a₁`
(transaction costs are paid from the bond position),
`h(x, a₁) = x₀ + (1 − c)(x₁ − a₁)` if `0 ≤ a₁ ≤ x₁`, and
`h(x, a₁) = x₀ + (1 + c)(x₁ − a₁)` if `x₁ < a₁ ≤ x₁ + x₀/(1 + c)`.

**Formalization Note.** The formula is used for every real `a₁` (the first branch for
`a₁ ≤ x₁`, the second otherwise); the statements only evaluate it for
`0 ≤ a₁ ≤ x₁ + x₀/(1 + c)`, where it is the book's `h`. -/
noncomputable def bondAfter (c : ℝ) (x : ℝ × ℝ) (a : ℝ) : ℝ :=
  if a ≤ x.2 then x.1 + (1 - c) * (x.2 - a) else x.1 + (1 + c) * (x.2 - a)

end BauerleRiederMDP.TransactionCosts


