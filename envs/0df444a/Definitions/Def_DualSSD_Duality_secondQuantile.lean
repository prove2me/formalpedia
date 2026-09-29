-- Prove2me | Definitions.Def_DualSSD_Duality_secondQuantile
-- name    : DualSSD_Duality_secondQuantile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:34:36.657241+00:00
-- url     : https://prove2.me/theorems/2865003e-43e2-4f16-a891-3716d25beaa7
-- title:
--   First quantile function $F_X^{(-1)}$, $p$-quantiles, and the second quantile function $F_X^{(-2)}$ (3.2)
-- statement:
--   Let $X$ be a real random variable with distribution function $F_X(\eta)=\mathbb P\{X\le\eta\}$.
--
--   1. The **first quantile function** is the left-continuous inverse of $F_X$,
--   $$F_X^{(-1)}(p)=\inf\{\eta:\ F_X(\eta)\ge p\},\qquad 0<p\le 1.$$
--   2. For $p\in[0,1]$, a number $q$ is a **$p$-quantile** of $X$ if
--   $$\mathbb P\{X<q\}\le p\le \mathbb P\{X\le q\}.$$
--   3. The **second quantile function** $F_X^{(-2)}:\mathbb R\to\overline{\mathbb R}$ (the absolute Lorenz curve) is
--   $$F_X^{(-2)}(p)=\int_0^p F_X^{(-1)}(\alpha)\,d\alpha\quad (0<p\le 1),\qquad F_X^{(-2)}(0)=0,\qquad F_X^{(-2)}(p)=+\infty\ \ (p\notin[0,1]). \tag{3.2}$$
--   It is finite on $[0,1]$ whenever $\mathbb E|X|<\infty$.
--
--   The graph of $F_X^{(-2)}$ on $[0,1]$ is the absolute Lorenz curve; its pointwise order is the dual description of second-degree stochastic dominance.
--
--   **Formalization Note** $F_X^{(-1)}$ is a real infimum (`sInf`). For $0<p<1$ the set $\{\eta: F_X(\eta)\ge p\}$ is nonempty and bounded below, so the value is the true infimum. At $p=1$ the paper's value is $+\infty$ when $X$ is unbounded above, while Lean's `sInf ∅` is $0$; this single point does not affect the integral (3.2), and no statement uses $F_X^{(-1)}(1)$ pointwise. $F_X^{(-2)}$ takes values in `EReal`, with the interval integral over $(0,p]$ on $[0,1]$ and `⊤` elsewhere.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 64 (F_X^(-1), p-quantile) and p. 65, eq. (3.2)

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance

namespace DualSSD.Duality

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The first quantile function `F_X^(−1)(p) = inf {η : F_X(η) ≥ p}`, the left-continuous inverse
of the distribution function (Ogryczak–Ruszczyński 2002, §3, p. 64), for `0 < p ≤ 1`.
Lean's real `sInf` returns `0` on a set that is empty or unbounded below. For `0 < p < 1` the set
is nonempty and bounded below, so the value is the genuine infimum. At `p = 1` the paper's value
is `+∞ ∈ ℝ̄` when `X` is unbounded above, while this definition returns `0`; that single point
does not affect the integral (3.2). No statement of this mission uses `leftQuantile P X 1`
pointwise, and values for `p ≤ 0` or `p > 1` are junk and never used. -/
noncomputable def leftQuantile (P : Measure Ω) (X : Ω → ℝ) (p : ℝ) : ℝ :=
  sInf {η : ℝ | p ≤ Shared.distFun P X η}

/-- `q` is a `p`-quantile of `X` (Ogryczak–Ruszczyński 2002, §3, p. 64):
`P{X < q} ≤ p ≤ P{X ≤ q}`. The paper uses this for `p ∈ [0, 1]`. -/
def IsPQuantile (P : Measure Ω) (X : Ω → ℝ) (p q : ℝ) : Prop :=
  P.real {ω | X ω < q} ≤ p ∧ p ≤ P.real {ω | X ω ≤ q}

/-- The second quantile function (absolute Lorenz curve) (3.2), `F_X^(−2) : ℝ → ℝ̄`
(Ogryczak–Ruszczyński 2002, §3, p. 65): `F_X^(−2)(p) = ∫_0^p F_X^(−1)(α) dα` for `0 < p ≤ 1`,
`F_X^(−2)(0) = 0`, and `F_X^(−2)(p) = +∞` for `p ∉ [0, 1]`. The interval integral over `(0, p]`
is `0` at `p = 0`, as the paper sets. Well defined (finite on `[0, 1]`) when `E|X| < ∞`. -/
noncomputable def secondQuantile (P : Measure Ω) (X : Ω → ℝ) (p : ℝ) : EReal :=
  if p ∈ Set.Icc (0 : ℝ) 1 then ((∫ α in (0 : ℝ)..p, leftQuantile P X α : ℝ) : EReal) else ⊤

end DualSSD.Duality


