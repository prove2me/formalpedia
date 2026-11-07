-- Prove2me | Definitions.Def_SecondBestBT_constP
-- name    : SecondBestBT_constP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:11.773684+00:00
-- url     : https://prove2.me/theorems/ee7a7509-57a2-4daf-b91e-389eaadb2270
-- title:
--   Cumulative ratios of the constant-$\varphi^\alpha_S$ family at $r=0$
-- statement:
--   For $\alpha>0$ and $r>0$ the constant-$\varphi^\alpha_S$ family on $\{0,\dots,N-1\}$ has ratios $r^{(N)}_0=0$ and $r^{(N)}_i=r+(N-1-i)(1+\alpha)/\alpha$, $i=1,\dots,N-1$, where $r_i=F_S(i-1)/f_S(i)$. Since $F_S(i)=F_S(i-1)(1+1/r_i)$, the cumulative ratios at ratio parameter $r=0$ are
--   $$
--   \frac{F_S(u)}{F_S(0)}=\prod_{i=1}^{u}\Big(1+\frac{\alpha}{(N-1-i)(1+\alpha)}\Big),\qquad u\le N-2 .
--   $$
--   Then $G^{(N)}_b$ is $G_b$ of Eq. (6) with these ratios.
--
--   **Formalization Note** The paper defines $G^{(N)}_b$ at $r=0$ for $b<N$ as the limit $r\to0^+$. Only $r_1,\dots,r_{b-1}$ enter, each continuous and positive at $r=0$, so the limit is the value computed directly here.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 5.2, p.20

import Mathlib

namespace SecondBestBT

/-- The cumulative ratios `F_S(u)/F_S(0)` of the constant-`φ^α_S` family on `{0, …, N − 1}` with
ratio parameter `r = 0` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…,
Section 5.2, p.20). The family has `r_0 = 0` and `r_i = r + (N − 1 − i)(1 + α)/α`; since
`r_i = F_S(i − 1)/f_S(i)`, `F_S(i) = F_S(i − 1)(1 + 1/r_i)`, so at `r = 0`
`F_S(u)/F_S(0) = ∏_{i=1}^{u} (1 + α/((N − 1 − i)(1 + α)))`.

**Formalization Note** The paper defines `G^{(N)}_b` at `r = 0` as the limit `r → 0⁺`; only
`r_1, …, r_{b−1}` enter, which are continuous and positive at `r = 0` for `b < N`, so the limit is
the direct value used here. The factor is meaningful for `u ≤ N − 2`, the only values used by
`G^{(N)}_{N−1}`; the subtraction `N − 1 − i` is taken in `ℝ`. -/
noncomputable def constP (α : ℝ) (N : ℕ) (u : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 u, (1 + α / (((N : ℝ) - 1 - i) * (1 + α)))

end SecondBestBT


