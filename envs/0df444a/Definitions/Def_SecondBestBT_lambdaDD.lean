-- Prove2me | Definitions.Def_SecondBestBT_lambdaDD
-- name    : SecondBestBT_lambdaDD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:07.740701+00:00
-- url     : https://prove2.me/theorems/de2731d2-8914-4a2a-b638-d6e1fa964b22
-- title:
--   Discrete budget-balance discriminant $\Lambda^D_D(x)$, Eq. (1)
-- statement:
--   For a grid $D=\{0=t_0<\dots<t_N=1\}$ with masses $f_S,f_B$ and cumulative masses $F(j)=\sum_{k\le j}f(k)$, the **discrete budget-balance discriminant** of a grid allocation matrix $x$ is
--   $$
--   \Lambda^D_D(x)=\sum_{j=0}^{N-1}\big[t_jf_B(j)-(t_{j+1}-t_j)(1-F_B(j))\big]x_B(j)+t_Nf_B(N)x_B(N)-\sum_{i=1}^{N}\big[t_if_S(i)+(t_i-t_{i-1})F_S(i-1)\big]x_S(i).
--   $$
--   The seller term at $i=0$ vanishes because $t_0=0$. The form contains no denominators and is defined when grid masses vanish.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Eq. (1), p.6

import Mathlib
import Definitions.Def_SecondBestBT_gridInterimB
import Definitions.Def_SecondBestBT_gridInterimS

namespace SecondBestBT

/-- The discrete budget-balance discriminant `Λ^D_D(x)` of Eq. (1) (Liu–Qin–Ren–Wang,
arXiv:2606.03849, held version sha256 17184930…, Section 3, Eq. (1), p.6):
`∑_{j=0}^{N−1} [t_j f_B(j) − (t_{j+1} − t_j)(1 − F_B(j))] x_B(j) + t_N f_B(N) x_B(N)
 − ∑_{i=1}^{N} [t_i f_S(i) + (t_i − t_{i−1}) F_S(i−1)] x_S(i)`,
with `F(j) = ∑_{k ≤ j} f(k)`.

**Formalization Note** `F_S(i − 1)` is written `∑_{k < i} f_S(k)`; the seller sum runs over
`i ∈ {1, …, N}`, so `i − 1` is never a truncated natural subtraction. The form is
denominator-free and defined for zero masses, as the paper remarks. -/
def lambdaDD (t : ℕ → ℝ) (fS fB : ℕ → ℝ) (N : ℕ) (x : ℕ → ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range N,
      (t j * fB j - (t (j + 1) - t j) * (1 - ∑ k ∈ Finset.range (j + 1), fB k)) *
        gridInterimB fS N x j) +
    t N * fB N * gridInterimB fS N x N -
    ∑ i ∈ Finset.Icc 1 N,
      (t i * fS i + (t i - t (i - 1)) * ∑ k ∈ Finset.range i, fS k) * gridInterimS fB N x i

end SecondBestBT


