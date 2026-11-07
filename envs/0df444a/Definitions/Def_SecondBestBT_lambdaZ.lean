-- Prove2me | Definitions.Def_SecondBestBT_lambdaZ
-- name    : SecondBestBT_lambdaZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:03.259237+00:00
-- url     : https://prove2.me/theorems/a34a99b8-309c-4096-8736-38cb3d1431a8
-- title:
--   Budget-balance discriminant $\Lambda_D(x)$ on $Z_W$ (expanded form)
-- statement:
--   For priors $f_S,f_B$ on $Z_W$ and an allocation $x$, the budget-balance discriminant is, in its expanded denominator-free form,
--   $$
--   \Lambda_D(x)=\sum_{s,b=0}^{W}x(s,b)\Big[f_S(s)f_B(b)(b-s)-f_S(s)\sum_{b'>b}f_B(b')-f_B(b)F_S(s-1)\Big],
--   $$
--   with $F_S(s-1)=\sum_{k<s}f_S(k)$ and $F_S(-1)=0$. It is the expansion of $\sum_{s,b}x(s,b)f_S(s)f_B(b)\big(b-\frac{1-F_B(b)}{f_B(b)}-s-\frac{F_S(s-1)}{f_S(s)}\big)$ and agrees with Eq. (1) on the grid $t_i=i$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 4.1, p.8; display on p.13

import Mathlib

namespace SecondBestBT

/-- The budget-balance discriminant `Λ_D(x)` on the integer grid `Z_W` in its expanded,
denominator-free form (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…,
Section 4.1, p.8, and the display on p.13):
`Λ_D(x) = ∑_{s,b} x(s, b) [f_S(s) f_B(b)(b − s) − f_S(s) ∑_{b' > b} f_B(b') − f_B(b) F_S(s − 1)]`,
the expansion of `∑ x f_S f_B (b − (1 − F_B(b))/f_B(b) − s − F_S(s−1)/f_S(s))`.

**Formalization Note** `F_S(s − 1) = ∑_{k < s} f_S(k)`, so `F_S(−1) = 0`; `∑_{b' > b} f_B(b')`
runs over `b < b' ≤ W` and equals `1 − F_B(b)` for a probability vector. It agrees with Eq. (1)
for the grid `t_i = i` (checked in `Solutions/verification/SecondBestBT_sanity.lean`). -/
def lambdaZ (fS fB : ℕ → ℝ) (W : ℕ) (x : ℕ → ℕ → ℝ) : ℝ :=
  ∑ s ∈ Finset.range (W + 1), ∑ b ∈ Finset.range (W + 1),
    x s b * (fS s * fB b * ((b : ℝ) - s) - fS s * ∑ b' ∈ Finset.Ioc b W, fB b' -
      fB b * ∑ k ∈ Finset.range s, fS k)

end SecondBestBT


