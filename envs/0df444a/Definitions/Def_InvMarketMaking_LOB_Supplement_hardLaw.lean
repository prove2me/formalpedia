-- Prove2me | Definitions.Def_InvMarketMaking_LOB_Supplement_hardLaw
-- name    : InvMarketMaking_LOB_Supplement_hardLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:31:14.952206+00:00
-- url     : https://prove2.me/theorems/82f94fc7-5332-4516-b8f2-94cea53d1510
-- title:
--   Hard instance (24) and the offline optimum $\mathrm{OPT}$ of Program (3)
-- statement:
--   The **hard instance** of Section 6.4 draws the seller's and the buyer's valuations independently, each from $\mu=\tfrac12\delta_{1/10}+\tfrac12\delta_{9/10}$. Its seller c.d.f. and buyer survival function are those of Eq. (24):
--   $$
--   F(b)=\begin{cases}0&b<1/10\\ 1/2&1/10\le b<9/10\\ 1&b\ge 9/10\end{cases}\qquad
--   S(a)=\begin{cases}1&a\le1/10\\ 1/2&1/10<a\le 9/10\\ 0&a>9/10.\end{cases}
--   $$
--   For any valuation law, the **offline optimum** of Program (3), written in the form (6), is
--   $$
--   \mathrm{OPT}=T\cdot\sup\{aS(a)-bF(b):\ b,a\in[0,1],\ b<a,\ F(b)=S(a)\}.
--   $$
--   It is the value of the best fixed bid–ask pair that keeps the expected inventory balanced. For the hard instance it equals $2T/5$, attained at $(1/10,9/10)$.
--
--   **Formalization Note** Eq. (24) gives only $F$ and $S$. The proof of Theorem 6.20 uses that the two valuations of a round are independent (pp. 51, 53), so the joint law is the product $\mu\otimes\mu$. $S(a)=\mathbb P(V^{\mathrm{buy}}\ge a)$ as in the published `buySurv`.
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Eq. (24), p. 50; Program (3), p. 16; Proposition 4.1, Eq. (6), p. 17

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_J

namespace InvMarketMaking.LOB.Supplement

open MeasureTheory

/-- The marginal `μ = ½ δ_{1/10} + ½ δ_{9/10}` of the hard instance (Maran, Restelli, Stradi,
No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints,
arXiv:2610.24562v1, Eq. (24), p. 50). -/
noncomputable def hardMarginal : Measure ℝ :=
  (1 / 2 : ENNReal) • Measure.dirac (1 / 10 : ℝ) + (1 / 2 : ENNReal) • Measure.dirac (9 / 10 : ℝ)

/-- The hard instance of Section 6.4 (Eq. (24), p. 50): the seller and the buyer valuations are
independent within a round, each with law `μ = ½ δ_{1/10} + ½ δ_{9/10}`. Its seller c.d.f. is
`F(b) = 0, 1/2, 1` on `b < 1/10`, `1/10 ≤ b < 9/10`, `b ≥ 9/10`, and its buyer survival function is
`S(a) = P(V^buy ≥ a) = 1, 1/2, 0` on `a ≤ 1/10`, `1/10 < a ≤ 9/10`, `a > 9/10`, as in (24).

**Formalization Note** Eq. (24) gives only `F` and `S`; the proof of Theorem 6.20 uses that the two
valuations of a round are independent (p. 51: `X^{(0)}` with masses 1/4, 1/2, 1/4; p. 53: "by
definition of `s_0` and independence of the valuations"), so the joint law is the product. -/
noncomputable def hardLaw : Measure (ℝ × ℝ) := hardMarginal.prod hardMarginal

/-- The optimal offline value of Program (3) (p. 16), in the form (6) of Proposition 4.1 (p. 17):
`OPT = T · sup {a S(a) − b F(b) : b, a ∈ [0, 1], b < a, F(b) = S(a)}`; the `T` identical expectations
of Program (3) sum to `T` times one of them.

**Formalization Note** The real supremum is the genuine one whenever the feasible set is nonempty
(for a probability law every value lies in `[−1, 1]`); for the hard instance it is attained at
`(1/10, 9/10)` with value `2/5` (p. 50). -/
noncomputable def OPT (V : Measure (ℝ × ℝ)) (T : ℕ) : ℝ :=
  T * sSup {x : ℝ | ∃ b a : ℝ, b ∈ Set.Icc (0 : ℝ) 1 ∧ a ∈ Set.Icc (0 : ℝ) 1 ∧ b < a ∧
    sellCdf V b = buySurv V a ∧ x = a * buySurv V a - b * sellCdf V b}

end InvMarketMaking.LOB.Supplement


