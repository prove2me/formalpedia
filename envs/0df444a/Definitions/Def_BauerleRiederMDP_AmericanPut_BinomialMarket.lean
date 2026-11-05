-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:51.211953+00:00
-- url     : https://prove2.me/theorems/29a7df2b-da1a-4f6b-bea1-eafdc196c114
-- title:
--   Binomial (Cox–Ross–Rubinstein) market with $d<1+i<u$
-- statement:
--   The **binomial market** consists of a bond with constant interest rate $i\ge 0$ and a stock whose relative price changes $\tilde R_1,\tilde R_2,\dots$ are independent and identically distributed with values $u>0$ (up) and $d>0$ (down), $d<u$. Section 11.1 assumes
--   $$d<1+i<u,$$
--   which excludes arbitrage and gives a unique equivalent martingale measure $\mathbb Q$.
--
--   This is the market model on which the American put of Chapter 11 is priced.
--
--   **Formalization Note** The data are the three reals $i,u,d$ with $0\le i$, $0<d$, $d<1+i<u$; $u>0$ and $d<u$ follow. The book does not require $d<1$: when $i>0$ it allows $1\le d<1+i$.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §3.1, p.60, PDF 74 (binomial model) and §11.1, p.331, PDF 339

import Mathlib

namespace BauerleRiederMDP.AmericanPut

/-- The **binomial (Cox–Ross–Rubinstein) market** underlying §11.1 (Bäuerle & Rieder, Markov Decision
Processes with Applications to Finance (2011), §3.1, p.60, PDF 74, and §11.1, p.331, PDF 339): one bond with
constant interest rate `i ∈ ℝ₊` and one stock whose relative price changes are i.i.d. and take the value
`u > 0` (up) or `d > 0` (down), `d < u`. Section 11.1 assumes `d < 1 + i < u`, "which implies no arbitrage
opportunities and the existence of a unique equivalent martingale measure `ℚ`".

**Formalization Note.** `u > 0` and `d < u` follow from the fields `0 < d` and `d < 1 + i < u`. The
interest rate is nonnegative (`i ∈ ℝ₊`, p.60), so the discount factor `β = (1 + i)⁻¹` lies in `(0, 1]`
(p.332). Nothing here requires `d < 1`: the book allows `1 ≤ d < 1 + i` when `i > 0`. -/
structure BinomialMarket where
  /-- The interest rate `i` of the bond. -/
  i : ℝ
  /-- The up factor `u` of the stock. -/
  u : ℝ
  /-- The down factor `d` of the stock. -/
  d : ℝ
  i_nonneg : 0 ≤ i
  d_pos : 0 < d
  d_lt : d < 1 + i
  lt_u : 1 + i < u

end BauerleRiederMDP.AmericanPut


