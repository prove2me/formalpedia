-- Prove2me | Definitions.Def_OCEClocks_DisplayAds_ExpClock
-- name    : OCEClocks_DisplayAds_ExpClock
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:20:41.351514+00:00
-- url     : https://prove2.me/theorems/8006ee78-ff85-45eb-9df7-303546a3f4e3
-- title:
--   Exponential clocks on $[0,\infty]$: $\mathrm{Exp}(r)$ with $\mathrm{Exp}(0)=\delta_\infty$, $\mathrm{Exp}(\infty)=\delta_0$ (§3.1)
-- statement:
--   Clocks take values in $[0,\infty]$. For a rate $r\in[0,\infty]$, the **exponential law** $\mathrm{Exp}(r)$ on $[0,\infty]$ is
--
--   1. the point mass at $\infty$ if $r=0$,
--   2. the point mass at $0$ if $r=\infty$,
--   3. otherwise the law with density $r e^{-rt}$ on $t\ge0$.
--
--   These are the conventions of §3.1 ("Exp(0) is a point mass at ∞ and Exp(∞) is a point mass at 0").
--
--   For a real rate $r\ge0$ and $y\in[0,\infty]$, $\operatorname{beat}_r(y)=\Pr[y<Z]$ for $Z\sim\mathrm{Exp}(r)$ is the probability that a clock showing $y$ rings strictly before a fresh competing clock of rate $r$. It equals $e^{-ry}$ for finite $y$ and $0$ for $y=\infty$.
--
--   These laws drive OCEC rounding (the discard clocks $\mathrm{Exp}(1-\sum_i x_{ij})$), the definition of an OCEC generator ($Y_j\sim\mathrm{Exp}(x_j)$), and the matching kernel, where the loss probability is $1-e^{-(1-x)Y}=1-\operatorname{beat}_{1-x}(Y)$.
--
--   **Formalization Note** `expLaw r : Measure ℝ≥0∞` is `dirac ⊤` for `r = 0`, `dirac 0` for `r = ⊤`, and otherwise the image under `ENNReal.ofReal` of Mathlib's `expMeasure r.toReal`. `beatProb r y` is `(expLaw (ENNReal.ofReal r) (Set.Ioi y)).toReal`.
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 6, §3.1 (conventions for Exp(0) and Exp(∞)); p. 6, Definition 3 (discard clocks); p. 10 (loss probability 1 − e^{−(1−x)Y})

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OCEClocks.DisplayAds

/-!
# Exponential clocks with values in `[0, ∞]`

Huang, Patton, Yang, Zhao, *Online Correlated Exponential Clocks*, STOC 2027 submission
(manuscript of November 3, 2026), p. 6, §3.1: "Throughout, Exp(0) is a point mass at ∞ and
Exp(∞) is a point mass at 0 by convention." Clocks live in `ℝ≥0∞ = [0, ∞]`.
-/

/-- The exponential law `Exp(r)` of rate `r ∈ [0, ∞]` on `[0, ∞]` (§3.1, p. 6): the point mass at
`∞` for `r = 0`, the point mass at `0` for `r = ∞`, and otherwise the image on `[0, ∞]` of
Mathlib's exponential distribution of rate `r` on `ℝ` (density `r e^{-r t}` on `t ≥ 0`). -/
noncomputable def expLaw (r : ℝ≥0∞) : Measure ℝ≥0∞ :=
  if r = 0 then Measure.dirac ⊤
  else if r = ⊤ then Measure.dirac 0
  else (expMeasure r.toReal).map ENNReal.ofReal

/-- The probability that a fresh competing clock `Z ∼ Exp(r)` (real rate `r ≥ 0`) rings strictly
after time `y ∈ [0, ∞]`, i.e. `P[y < Z]`: the probability that a clock showing `y` beats it.
For finite `y` this is `e^{-r y}`; for `y = ∞` it is `0`. -/
noncomputable def beatProb (r : ℝ) (y : ℝ≥0∞) : ℝ :=
  (expLaw (ENNReal.ofReal r) (Set.Ioi y)).toReal

end OCEClocks.DisplayAds


