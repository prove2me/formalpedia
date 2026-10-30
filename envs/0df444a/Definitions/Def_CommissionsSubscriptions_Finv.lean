-- Prove2me | Definitions.Def_CommissionsSubscriptions_Finv
-- name    : CommissionsSubscriptions_Finv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:21:54.021053+00:00
-- url     : https://prove2.me/theorems/fa95b4e9-b190-4644-8b87-f0dc99279857
-- title:
--   Inverse value distribution $F^{-1}:[0,1]\to[0,\bar v]$ in $\overline{\mathbb R}$
-- statement:
--   For an extended distribution function $F:\mathbb R\to\mathbb R$ and $u\in\mathbb R$,
--   $$F^{-1}(u)=\inf\{\,r\ge0:\ u\le F(r)\,\}\in\mathbb R\cup\{+\infty\},$$
--   with $\inf\emptyset=+\infty$.
--
--   For a distribution satisfying Assumption 1 this is the inverse function of eq. (1) of the paper on $[0,1]$: $F^{-1}(0)=0$; for $u\in(0,1)$, $F^{-1}(u)$ is the unique $v\in(0,\bar v)$ with $F(v)=u$; and $F^{-1}(1)=\bar v$, the upper end of the support, which is $+\infty$ for unbounded support. It gives the valuations of the marginal buyer, $F^{-1}_{b_j}(1-q^b_j/b_j)$, and of the marginal seller, $F^{-1}_{s_i}(q^s_i/s_i)$ (eqs. (4)–(5)).
--
--   **Formalization Note** The value is an extended real (`EReal`), so that $F^{-1}(1)=+\infty$ is represented; the paper's footnote-4 convention $F^{-1}(1)\cdot0=0$ is the extended-real rule $\top\cdot0=0$.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), eq. (1), p. 8; eqs. (4)–(5), p. 11; footnote 4, p. 12

import Mathlib

namespace CommissionsSubscriptions

/-- **Inverse value distribution `F⁻¹ : [0,1] → [0, v̄]`, valued in `ℝ ∪ {±∞}`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), eq. (1), p. 8.

`Finv F u = inf {r ≥ 0 : u ≤ F r}`, an infimum in `EReal`, with `inf ∅ = ⊤`.

**Formalization Note (Reading 1).** For a CDF `F` satisfying Assumption 1 (`IsValueCDF`) and
`u ∈ [0,1]` this is the paper's inverse function: `Finv F 0 = 0`; for `u ∈ (0,1)` it is the
unique `v ∈ (0, v̄)` with `F v = u`; and `Finv F 1 = v̄ ∈ ℝ₊ ∪ {∞}`, which is `⊤` exactly when the
support is unbounded (then `F r < 1` for every real `r`, so the set is empty). Footnote 4's
convention `F⁻¹(1)·0 = 0` is `EReal`'s `⊤ * 0 = 0`. -/
noncomputable def Finv (F : ℝ → ℝ) (u : ℝ) : EReal :=
  ⨅ (r : ℝ) (_ : 0 ≤ r ∧ u ≤ F r), (r : EReal)

end CommissionsSubscriptions


