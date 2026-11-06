-- Prove2me | Definitions.Def_DRSub4633_wDens
-- name    : DRSub4633_wDens
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:40.329974+00:00
-- url     : https://prove2.me/theorems/1578e0e2-d245-4eb1-ab08-b0149ed3d77c
-- title:
--   The averaging density $w$
-- statement:
--   With $w_1=755091259/1617960000$, $w_2=11/40$ and $w_3=121/1000$, the averaging density is
--   $$w(t)=\begin{cases}0,&0\le t<t_0,\\ b+w_1(t-t_0)+w_2(t-t_0)^2,&t_0\le t\le t_1,\\ w(t_1)+w_3(t-t_1),&t_1\le t\le 1.\end{cases}$$
--   It is the density with which the large-block comparison (38)–(39) is averaged.
--
--   **Formalization Note** The function is defined on all of $\mathbb R$ (the first branch for $t<t_0$, the last for $t>t_1$); only $[0,1]$ is used.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eqs. (17)–(18), p.11

import Mathlib
import Definitions.Def_DRSub4633_bPar
import Definitions.Def_DRSub4633_t0
import Definitions.Def_DRSub4633_t1

namespace DRSub4633

/-- **The averaging density `w`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eqs. (17)–(18), p.11:
`w(t) = 0` for `0 ≤ t < t₀`; `w(t) = b + w₁(t − t₀) + w₂(t − t₀)²` for `t₀ ≤ t ≤ t₁`;
`w(t) = w(t₁) + w₃(t − t₁)` for `t₁ ≤ t ≤ 1`, with `w₁ = 755091259/1617960000`, `w₂ = 11/40`,
`w₃ = 121/1000`.

**Formalization Note.** The constants `w₁, w₂, w₃` of (17) are written as literals. The function is
total on `ℝ`: the first branch is used for every `t < t₀` and the last for every `t > t₁`; only
`[0, 1]` is used. -/
noncomputable def wDens (t : ℝ) : ℝ :=
  if t < t0 then 0
  else if t ≤ t1 then
    bPar + (755091259 / 1617960000) * (t - t0) + (11 / 40) * (t - t0) ^ 2
  else
    (bPar + (755091259 / 1617960000) * (t1 - t0) + (11 / 40) * (t1 - t0) ^ 2)
      + (121 / 1000) * (t - t1)

end DRSub4633


