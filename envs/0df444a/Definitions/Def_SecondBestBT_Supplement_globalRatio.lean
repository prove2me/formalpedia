-- Prove2me | Definitions.Def_SecondBestBT_Supplement_globalRatio
-- name    : SecondBestBT_Supplement_globalRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:32:39.363974+00:00
-- url     : https://prove2.me/theorems/6d0fb089-bc9b-4c63-a424-502187c17dd0
-- title:
--   Global ratio sequence $r_i=F_S(i-1)/f_S(i)$
-- statement:
--   For a seller prior on $\mathbb Z_{\ge0}$ with masses $f_S$ and $f_S(0)>0$, the **global ratio sequence** is
--   $$
--   r_i:=\frac{F_S(i-1)}{f_S(i)},\qquad i\ge0,
--   $$
--   at every positive-mass coordinate, with $F_S(i-1)=\sum_{k<i}f_S(k)$ and the convention $F_S(-1)=0$, so $r_0=0$. Beyond the support, $r_i=\infty$ (and $1/r_i=0$). For a seller with full support on $\{0,\dots,K\}$, $r_i$ is finite and positive for $1\le i\le K$ and infinite for $i>K$.
--
--   These inverse-hazard ratios are the data that the compressed states of the greedy construction record; the $\alpha$-virtual value is $\varphi^\alpha_S(i)=(1+\alpha)i+\alpha r_i$.
--
--   **Formalization Note** Values lie in $[0,\infty]$ (`ℝ≥0∞`); a coordinate with $f_S(i)\le0$ receives $\infty$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 5.1, p.16

import Mathlib

open scoped ENNReal

namespace SecondBestBT.Supplement

/-- The **global ratio sequence** of a seller prior on `ℤ_{≥0}` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Section 5.1, p.16):
`r_i := F_S(i − 1) / f_S(i)` at every positive-mass coordinate `i ≥ 0`, with `F_S(−1) = 0` (so
`r_0 = 0`), and `r_i = ∞` beyond the support.

**Formalization Note** Values are in `ℝ≥0∞`. `F_S(i − 1) = ∑_{k < i} f_S(k)`. A coordinate with
`f_S(i) ≤ 0` gets `∞`; for a seller with full support on `{0, …, K}` (the only sellers whose ratio
sequences the mission uses) these are exactly the coordinates `i > K`, as in the paper. -/
noncomputable def globalRatio (fS : ℕ → ℝ) (i : ℕ) : ℝ≥0∞ :=
  if 0 < fS i then ENNReal.ofReal ((∑ k ∈ Finset.range i, fS k) / fS i) else ⊤

end SecondBestBT.Supplement


