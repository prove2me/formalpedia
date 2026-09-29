-- Prove2me | Definitions.Def_DualSSD_MeanRisk_secondQuantileR
-- name    : DualSSD_MeanRisk_secondQuantileR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:03:07.133986+00:00
-- url     : https://prove2.me/theorems/628b8cb4-41ca-4f54-818e-c6761cef8aaa
-- title:
--   Left quantile $F_X^{(-1)}$, $p$-quantiles and the absolute Lorenz curve $F_X^{(-2)}$ (3.2) on $[0,1]$
-- statement:
--   The first quantile function of $X$ is the left-continuous inverse of $F_X$,
--
--   $$F_X^{(-1)}(p)=\inf\{\eta:F_X(\eta)\ge p\},\qquad 0<p\le 1.$$
--
--   Given $p\in[0,1]$, a number $q$ is a **$p$-quantile** of $X$ if $P\{X<q\}\le p\le P\{X\le q\}$. The **second quantile function** (absolute Lorenz curve) is
--
--   $$F_X^{(-2)}(p)=\int_0^pF_X^{(-1)}(\alpha)\,d\alpha,\qquad 0<p\le 1,$$
--
--   with $F_X^{(-2)}(0)=0$. It is finite on $[0,1]$ whenever $E|X|<\infty$.
--
--   The dual (quantile) risk measures of the paper are all built from $F_X^{(-2)}$.
--
--   **Formalization Note** The paper's $F_X^{(-2)}$ is extended-real valued on all of $\mathbb R$ with value $+\infty$ off $[0,1]$; this mission only evaluates it on $[0,1]$, so a real-valued version is used and its values off $[0,1]$ are never used. The infimum is Lean's real `sInf`; at $p=1$ it returns $0$ instead of the paper's $+\infty$ when $X$ is unbounded above, which does not affect the integral, and no statement uses $F_X^{(-1)}(1)$ pointwise.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 64 (F_X^(−1), p-quantile), p. 65 eq. (3.2)

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance

namespace DualSSD.MeanRisk

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

/-- The second quantile function (absolute Lorenz curve) (3.2) on `[0, 1]`
(Ogryczak–Ruszczyński 2002, §3, p. 65): `F_X^(−2)(p) = ∫_0^p F_X^(−1)(α) dα` for `0 < p ≤ 1`, and
`F_X^(−2)(0) = 0` (the interval integral over `(0, 0]` is `0`).
The paper's `F_X^(−2)` is `ℝ̄`-valued on all of `ℝ`, with value `+∞` off `[0, 1]`; this mission only
evaluates it on `[0, 1]`, where it is finite when `E|X| < ∞`, so this real-valued version is used.
Its values for `p ∉ [0, 1]` are not the paper's and are never used by any statement. -/
noncomputable def secondQuantileR (P : Measure Ω) (X : Ω → ℝ) (p : ℝ) : ℝ :=
  ∫ α in (0 : ℝ)..p, leftQuantile P X α

end DualSSD.MeanRisk


