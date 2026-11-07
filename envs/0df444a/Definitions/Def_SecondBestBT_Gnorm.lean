-- Prove2me | Definitions.Def_SecondBestBT_Gnorm
-- name    : SecondBestBT_Gnorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:12.214193+00:00
-- url     : https://prove2.me/theorems/553979a9-5e60-4fe7-9ebe-fbbcd062f7e9
-- title:
--   Normalized allocation level $G_b$, Eq. (6)
-- statement:
--   For $\alpha\ge0$ and cumulative ratios $P(u)=F_S(u)/F_S(0)$, the **normalized allocation level** is
--   $$
--   G_b=\sum_{t=1}^{b}\frac{F_S(t-1)/F_S(0)}{t(1+\alpha)}\prod_{j=t+1}^{b}\Big(1-\frac{1}{j(1+\alpha)}\Big),\qquad b\ge1,
--   $$
--   the unrolled form of the recursion (5) $x_b=\big(1-\frac1{b(1+\alpha)}\big)x_{b-1}+\frac{\beta}{b(1+\alpha)}\frac{F_S(b-1)}{F_S(0)}$, $x_1=\frac{\beta}{1+\alpha}$, with $x_b=\beta G_b$. The empty product is $1$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Eq. (5), (6), p.19

import Mathlib

namespace SecondBestBT

/-- The normalized allocation level of Eq. (6) (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version
sha256 17184930…, Section 5.1, Eq. (6), p.19):
`G_b = ∑_{t=1}^{b} (F_S(t−1)/F_S(0)) / (t(1 + α)) · ∏_{j=t+1}^{b} (1 − 1/(j(1 + α)))`, `b ≥ 1`.

**Formalization Note** The cumulative ratios enter as a function `P u = F_S(u)/F_S(0)`, so the
same definition serves a given seller prior (Lemma 5.3) and the constant-`φ^α_S` family
(Lemma 5.6). The product over `j ∈ (t, b]` is empty, hence `1`, at `t = b`. -/
noncomputable def Gnorm (α : ℝ) (P : ℕ → ℝ) (b : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 b, P (t - 1) / ((t : ℝ) * (1 + α)) *
    ∏ j ∈ Finset.Ioc t b, (1 - 1 / ((j : ℝ) * (1 + α)))

end SecondBestBT


