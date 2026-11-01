-- Prove2me | Definitions.Def_DuanEP_Pure_fCount
-- name    : DuanEP_Pure_fCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:49.791278+00:00
-- url     : https://prove2.me/theorems/81e96b52-7394-4119-bac8-73e4192234a0
-- title:
--   The count $f_j^{(m)}=\binom{j+m-1}{j}$
-- statement:
--   For $m\ge 1$ and $j\in\mathbb N$, the function of Eqs. (2) and (3) is
--
--   $$
--   f_j^{(m)}=\frac{(j+m-1)!}{j!\,(m-1)!}=\binom{j+m-1}{j},
--   $$
--
--   the number of ways to write $j$ as an ordered sum of $m$ nonnegative integers.
--
--   **Formalization Note** It is defined as the binomial coefficient $\binom{j+m-1}{j}$ with natural-number subtraction. At $m=0$, where the factorial formula is undefined, the value is $1$ for $j=0$ and $0$ otherwise; no statement of the mission uses $m=0$ except through a limit $m\to\infty$.
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 2, first line (formula for f_j^(m))

import Mathlib

namespace DuanEP.Pure

/-- The function `f_j^{(m)} = (j + m − 1)! / (j! (m − 1)!)` of Eqs. (2) and (3)
(Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, p. 2, first line), written as the binomial coefficient `C(j + m − 1, j)`.

**Formalization Note** The binomial form is the paper's factorial quotient for `m ≥ 1`
(proved in the milestone `joint_state_decomposition`, together with the fact that it counts the
`m`-tuples of occupations with sum `j`). At `m = 0`, where the paper's formula is undefined,
`fCount 0 j` is `1` for `j = 0` and `0` otherwise. -/
def fCount (m j : ℕ) : ℕ := (j + m - 1).choose j

end DuanEP.Pure


