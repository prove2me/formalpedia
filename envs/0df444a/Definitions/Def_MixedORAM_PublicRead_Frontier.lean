-- Prove2me | Definitions.Def_MixedORAM_PublicRead_Frontier
-- name    : MixedORAM_PublicRead_Frontier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:45:36.497941+00:00
-- url     : https://prove2.me/theorems/693635fe-b25d-4ad2-b6fc-2922b38f983c
-- title:
--   The quantities H, F_p, G_p(Q) and Φ
-- statement:
--   For array size $n$, client memory $m$ words, private probability $p$ and private budget $Q$,
--   $$H=\log_2\Big(2+\frac{n}{m+1}\Big),\qquad F_p=\max\Big\{1,\frac{H}{\log_2(2+1/p)}\Big\},\qquad G_p(Q)=\max\Big\{1,\frac{H}{\log_2(2+1/p+Q/H)}\Big\}.$$
--   $G_p(Q)$ is the public-read cost of the frontier of Theorem 3.1. For $x,y>0$,
--   $$\Phi(x,y)=\min\{x,y\}\,\log_2\Big(2+\frac{\max\{x,y\}}{\min\{x,y\}}\Big),$$
--   and $\Phi$ is $0$ when $x=0$ or $y=0$.
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), p. 1, Eq. (1); p. 7, §3.2

import Mathlib

set_option autoImplicit false

namespace MixedORAM.PublicRead

/-- `H = log₂(2 + n/(m + 1))` (Ciszewski, Ragnoli, *Access Cost Tradeoffs in Mixed-Mode Oblivious
RAM*, STOC 2027 submission (manuscript sha256 a4f849fd…), Eq. (1), p. 1), for array size `n` and
client memory `m` words. -/
noncomputable def Hn (n m : ℕ) : ℝ := Real.logb 2 (2 + (n : ℝ) / ((m : ℝ) + 1))

/-- `F_p = max{1, H/log₂(2 + 1/p)}` (Eq. (1), p. 1). -/
noncomputable def Fp (n m : ℕ) (p : ℝ) : ℝ := max 1 (Hn n m / Real.logb 2 (2 + 1 / p))

/-- `G_p(Q) = max{1, H/log₂(2 + 1/p + Q/H)}` (Eq. (1), p. 1). -/
noncomputable def Gp (n m : ℕ) (p Q : ℝ) : ℝ :=
  max 1 (Hn n m / Real.logb 2 (2 + 1 / p + Q / Hn n m))

/-- `Φ(x, y) = min{x, y} · log₂(2 + max{x, y}/min{x, y})` for `x, y > 0`, and `0` when `x = 0` or
`y = 0` (§3.2, p. 7: "zero on the axes"). For `x, y ≥ 0` the formula already gives `0` on the axes
(`min = 0`); the explicit case only fixes the value there. -/
noncomputable def Phi (x y : ℝ) : ℝ :=
  if x = 0 ∨ y = 0 then 0 else min x y * Real.logb 2 (2 + max x y / min x y)

end MixedORAM.PublicRead


