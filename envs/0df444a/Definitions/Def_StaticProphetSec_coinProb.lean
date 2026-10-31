-- Prove2me | Definitions.Def_StaticProphetSec_coinProb
-- name    : StaticProphetSec_coinProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:00.85157+00:00
-- url     : https://prove2.me/theorems/a5b91ebf-acd9-43bf-a727-2f62e9a58917
-- title:
--   Law of the tie-break coins
-- statement:
--   For $p\in[0,1]$ and a coin vector $B\in\{\text{heads},\text{tails}\}^n$, this is the probability of $B$ when the coins are independent with heads probability $p$:
--
--   $$\prod_{i:\,B_i=\text{heads}} p\ \prod_{i:\,B_i=\text{tails}}(1-p).$$
--
--   **Formalization Note** The value lies in $[0,\infty]$; an expectation over the coins is a finite sum weighted by this probability. Each statement using it assumes $0\le p\le1$.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Remark 1, p.5

import Mathlib

open scoped ENNReal

namespace StaticProphetSec

/-- The probability of the coin vector `B` when the coins are independent with probability `p`
of heads (`true`): the tie-break randomness of the policy `(t, p)` (Arnosti & Ma,
arXiv:2108.12893v2, Remark 1, p.5).

**Formalization Note.** `p` is a real number and every statement using `coinProb` assumes
`0 ≤ p ≤ 1`. An expectation over the coins is the finite sum `∑ B, coinProb p B * …`. -/
noncomputable def coinProb {n : ℕ} (p : ℝ) (B : Fin n → Bool) : ℝ≥0∞ :=
  ∏ i, if B i = true then ENNReal.ofReal p else ENNReal.ofReal (1 - p)

end StaticProphetSec


