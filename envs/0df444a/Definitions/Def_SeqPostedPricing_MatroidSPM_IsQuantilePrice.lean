-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_IsQuantilePrice
-- name    : SeqPostedPricing_MatroidSPM_IsQuantilePrice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:35:02.226589+00:00
-- url     : https://prove2.me/theorems/3926c875-107a-421d-8f25-fa018f4656be
-- title:
--   Quantile price $p=F^{-1}(1-q)$
-- statement:
--   For a distribution $\nu$ on $\mathbb R$ and $q\in\mathbb R$, a price $p$ is the **quantile price** $p=F^{-1}(1-q)$ if
--
--   $$
--   \Pr_{v\sim\nu}[v>p]=q\qquad\text{and}\qquad \Pr_{v\sim\nu}[v>p']<q\ \text{ for every } p'>p,
--   $$
--
--   i.e. $p$ is the largest price at which the item sells with probability $q$. These are the prices $p_i=F_i^{-1}(1-q_i)$ of the sequential posted-price mechanism.
--
--   **Formalization Note** A predicate rather than a function, so no default value of an empty infimum enters; for $q=0$ no such price exists.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 2, p. 5; §4, p. 6

import Mathlib
open MeasureTheory

namespace SeqPostedPricing.MatroidSPM

/-- **`p = F^{-1}(1 − q)`: the price that sells with probability `q`.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, Lemma 2, p. 5 (PDF p. 7): "p_i^M = F_i^{−1}(1 − q_i^M)"; §4, p. 6 (PDF p. 8): "pi =
Fi^{−1}(1 − qi)".

`IsQuantilePrice ν q p`: `Pr[v > p] = q` and `Pr[v > p'] < q` for every `p' > p`, i.e. `p` is
the largest price whose tail probability is `q`.

**Formalization Note.** The quantile is a predicate, not a function, so no junk value (`sInf ∅`,
`sInf ℝ = 0`) enters. For a regular distribution and `0 < q ≤ 1` such a `p` is unique; for
`q = 0` none exists (no agent with `q_i = 0` is priced; see `spmActive`). -/
def IsQuantilePrice (ν : Measure ℝ) (q p : ℝ) : Prop :=
  (ν (Set.Ioi p)).toReal = q ∧ ∀ p', p < p' → (ν (Set.Ioi p')).toReal < q

end SeqPostedPricing.MatroidSPM


