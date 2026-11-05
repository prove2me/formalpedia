-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_stock
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket_stock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:38.838767+00:00
-- url     : https://prove2.me/theorems/16eb692a-4868-474b-b3c6-b8e8c1c024de
-- title:
--   Stock price $S_n=x\,\tilde R_1\cdots\tilde R_n$
-- statement:
--   Started at $S_0=x$, the stock price after $n$ moves is
--   $$S_n=x\prod_{k=1}^{n}\tilde R_k,\qquad \tilde R_k\in\{u,d\}.$$
--   In §11.1 the process to be stopped is $X_n=S_n$, with state space $E=\mathbb R_+$; the price $0$ is absorbing.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §3.1, p.60, PDF 74 and §11.1, p.332, PDF 340

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket

namespace BauerleRiederMDP.AmericanPut

/-- The **stock price process** `S_n = S_0 · R̃_1 ⋯ R̃_n` of the binomial model started at `S_0 = x`
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §3.1, p.60, PDF 74; §11.1,
p.332, PDF 340, where the process to be stopped is `X_n = S_n`).

**Formalization Note.** `ω k = true` is an up move (`R̃_{k+1} = u`), `false` a down move (`R̃_{k+1} = d`);
`stock x 0 ω = x`. The book's state space is `E = ℝ₊`; from `x ≥ 0` the price stays in `ℝ₊`, and `x = 0` is
absorbing. -/
def BinomialMarket.stock (M : BinomialMarket) (x : ℝ) (n : ℕ) (ω : ℕ → Bool) : ℝ :=
  x * ∏ k ∈ Finset.range n, (if ω k then M.u else M.d)

end BauerleRiederMDP.AmericanPut


