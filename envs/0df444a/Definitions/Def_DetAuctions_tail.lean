-- Prove2me | Definitions.Def_DetAuctions_tail
-- name    : DetAuctions_tail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:05.40656+00:00
-- url     : https://prove2.me/theorems/3aa0db40-154e-4cc9-9923-f0799c58fb19
-- title:
--   Tail function $\bar F(t)=\mathrm{Prob}[X>t]$
-- statement:
--   For a value law $F$ on $[0,\infty)$ and a real number $t$, the **tail function** is
--   $$\bar F(t)=1-F(t)=\mathrm{Prob}_{X\sim F}[X>t].$$
--   With a cap $c_j\ge0$, the **capped tail** is $\bar F_j^{c_j}(t)=\mathrm{Prob}[X_j>c_j+t]=\mathrm{Prob}[(X_j-c_j)_+>t]$ for $t\ge0$, i.e. $\bar F_j(c_j+t)$. Tail integrals of these functions are how the paper bounds the residual term of its master revenue inequality.
--
--   **Formalization Note** The inequality is strict, as on the page; the non-strict $\mathrm{Prob}[X\ge r]$ of Myerson's formula (3) is a different function. Values in $[0,\infty]$, in $[0,1]$ for a probability law.
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], §2, p.7 (pdf p.9); §4, p.15 (pdf p.17)

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace DetAuctions

/-- The **tail function** `F̄(t) = 1 − F(t) = Prob[X > t]` of a value law `ν` on `ℝ₊`, at a real
argument `t`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), §2, p.7: "F̄(x) = Prob[X > x] = 1 − F(x)"; §4, p.15: "Recall the
notation F̄j(t) = 1 − Fj(t) = Prob[Xj > t] … F̄j^{cj}(t) := Prob[Xj > cj + t] = Prob[Yj > t]."

**Formalization Note** The tail is strict (`t < x`), as on the page; the non-strict
`Prob[X ≥ r]` of Eq. (3) is a different function. It takes values in `ℝ≥0∞`; for a probability
law it lies in `[0, 1]`. The capped tail `F̄ⱼ^{cⱼ}(t)` is `tail (ν j) (c j + t)`. -/
noncomputable def tail (ν : Measure ℝ≥0) (t : ℝ) : ℝ≥0∞ :=
  ν {x | t < (x : ℝ)}

end DetAuctions


