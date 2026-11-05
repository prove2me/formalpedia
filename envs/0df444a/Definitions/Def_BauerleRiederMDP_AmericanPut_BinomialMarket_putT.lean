-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_putT
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket_putT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:29.326343+00:00
-- url     : https://prove2.me/theorems/1a53351e-d232-4169-8f50-8cf22520c252
-- title:
--   Maximal reward operator $\mathcal T v(x)=\max\{(K-x)^+,\beta(qv(xu)+(1-q)v(xd))\}$
-- statement:
--   The **maximal reward operator** of the put acts on functions $v$ on $E=\mathbb R_+$ by
--   $$\mathcal T v(x)=\max\Big\{(K-x)^+,\ \beta\big(q\,v(xu)+(1-q)\,v(xd)\big)\Big\}.$$
--   The $n$-stage values of the American put are $J_0(x)=(K-x)^+$ and $J_n=\mathcal TJ_{n-1}$.
--
--   **Formalization Note** Functions are real-valued on $\mathbb R$; all statements evaluate $\mathcal Tv$ only at $x\ge0$. $J_n$ is written as the $n$-fold iterate of $\mathcal T$ applied to $(K-x)^+$.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §11.1, p.336, PDF 344 (recursion of $J_n$) and Theorem 11.1.3 b), p.337, PDF 345

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_q
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_beta
import Definitions.Def_fd04_putPayoff
open FinancialDerivatives.FD04 (putPayoff)

namespace BauerleRiederMDP.AmericanPut

/-- The **maximal reward operator of the put** (Bäuerle & Rieder, Markov Decision Processes with Applications
to Finance (2011), Theorem 11.1.3 b), p.337, PDF 345):
`𝒯v(x) = max{(K − x)⁺, β(q v(xu) + (1 − q) v(xd))}`.
The `n`-stage values of the American put are `J₀ = (K − x)⁺`, `J_n = 𝒯 J_{n−1}` (p.336, PDF 344), i.e.
`J_n = (putT M K)^[n] (putPayoff K)`.

**Formalization Note.** Functions are `ℝ → ℝ`; every statement evaluates `𝒯v(x)` only at `x ∈ E = ℝ₊`, where
it uses `v` at `xu, xd ∈ ℝ₊`. -/
noncomputable def BinomialMarket.putT (M : BinomialMarket) (K : ℝ) (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  max (putPayoff K x) (M.beta * (M.q * v (x * M.u) + (1 - M.q) * v (x * M.d)))

end BauerleRiederMDP.AmericanPut


