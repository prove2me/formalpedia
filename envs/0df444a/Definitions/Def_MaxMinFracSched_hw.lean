-- Prove2me | Definitions.Def_MaxMinFracSched_hw
-- name    : MaxMinFracSched_hw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:50.364043+00:00
-- url     : https://prove2.me/theorems/e2c113cb-6d37-4ed0-ae26-926e291d26e4
-- title:
--   Hard family: job works $w_i(j)$ (display (10), corrected)
-- statement:
--   The work of the job released at $t_i$ and due at $t_j$ ($0\le i<j\le k$):
--   $$w_i(j)=\begin{cases} T_j & i=0,\\[2pt] \dfrac{1-x}{x^{i}}\displaystyle\sum_{\ell=1}^{i+1}T_\ell & i\ge1,\ j=i+1,\\[8pt] \dfrac{1-x}{x^{i}}\,T_j & i\ge1,\ j\ge i+2.\end{cases}$$
--
--   At $t_0$ the adversary releases one job of work $T_j$ due at each $t_j$; at each later $t_i$ it may stop, or release one job due at each $t_j$, $j>i$, of work $w_i(j)$.
--
--   **Formalization Note (correction)** The printed display (10) has the cases "$T_j$ if $i=1$" and the exponent $x^{j}$. With it Lemma 6.2 fails: for $k=3$, $x=1/2$ the release at $t_0$ gets works $1/4,1/2,2$ and $\hat f_{J^{(1)}}=4/11\ne1$; taking $w_0(j)=T_j$ from the sentence on p.29 but keeping the printed case $i=1$ still gives $\hat f_{J^{(2)}}=4/7\ne 1/2$. Figure 3 and the proof of Lemma 6.2 ($W_{t_a}(t_d)=\frac{1-x}{x^a}\sum_{j=1}^{a+1}T_j+\dots$) use the release index in the exponent and use $T_j$ only for the release at $t_0$; this definition follows them.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 6.1, display (10) and Figure 3, p.29 (PDF p.31); proof of Lemma 6.2, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_MaxMinFracSched_TT__4c2bff

namespace MaxMinFracSched

/-- **The job works `w_i(j)` of the hard family, display (10) as corrected.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 6.1,
p.29 (PDF p.31): "We now describe how jobs arrive. At time t0, the adversary releases a job of
length Ti due at time ti for each i > 0. At each ti after t0 the adversary may observe that ALG has
fallen behind α-competitiveness and stop releasing jobs, or it may release a new set of jobs: for
each j > i, it releases a job due at tj with weight wi(j), given by"

`hw x k i j` is the work of the job released at `t_i` and due at `t_j` (`0 ≤ i < j ≤ k`):
* `T_j` if `i = 0`;
* `(1 − x)/x^i · Σ_{ℓ=1}^{i+1} T_ℓ` if `i ≥ 1` and `j = i + 1`;
* `(1 − x)/x^i · T_j` if `i ≥ 1` and `j ≥ i + 2`.

**Formalization Note (correction).** The printed (10) has the cases "`T_j` if `i = 1`" and the
exponent `x^j`. As printed, Lemma 6.2 fails: for `k = 3`, `x = 1/2` the release at `t_0` gets
works `1/4, 1/2, 2` (cases 2 and 3), so `f̂_{J^{(1)}} = 4/11` instead of `1`; taking `w_0(j) = T_j`
from the sentence on p.29 but keeping the printed case "`i = 1`" still gives `f̂_{J^{(2)}} = 4/7`
instead of `1/2`. Figure 3 (p.29) and the proof of Lemma 6.2 (p.30, "Wta(td) = … (1−x)/x^a ·
Σ_{j=1}^{a+1} Tj + …") use the release index in the exponent and use `T_j` only for the release at
`t_0`, as the sentence "At time t0, the adversary releases a job of length Ti due at time ti"
says. This definition follows Figure 3 and the proof. -/
noncomputable def hw (x : ℝ) (k i j : ℕ) : ℝ :=
  if i = 0 then TT x k j
  else if j = i + 1 then (1 - x) / x ^ i * ∑ ℓ ∈ Finset.Icc 1 (i + 1), TT x k ℓ
  else (1 - x) / x ^ i * TT x k j

end MaxMinFracSched


