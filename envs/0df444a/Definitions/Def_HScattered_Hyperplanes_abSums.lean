-- Prove2me | Definitions.Def_HScattered_Hyperplanes_abSums
-- name    : HScattered_Hyperplanes_abSums
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:51.146625+00:00
-- url     : https://prove2.me/theorems/28f66a56-d3a4-4553-945d-8a77f5d004bd
-- title:
--   The triple sums $a_s$ and $b_s$ of §5.4
-- statement:
--   Let $q$ be real and $n, r, s, m \in \mathbb N$, where $m$ plays the role of $nr/s$. For $0 \le j,k,t \le s$ put
--   $$T_{j,k,t} = q^{\,mj - mt + (s-k)(m-n) + \frac12 (s-k-1)(s-k) + \frac12 (t-1)t}\begin{bmatrix} s\\ k\end{bmatrix}_q\begin{bmatrix} k\\ j\end{bmatrix}_q\begin{bmatrix} j\\ t\end{bmatrix}_q (-1)^{t+k},$$
--   where $(s-k)(m-n)$ is $(s-k)\,n(r-s)/s$ when $m = nr/s$. Then
--   $$a_s = \sum_{j=0}^{s} q^{\,nr - nj}\sum_{k=0}^{s}\sum_{t=0}^{s} T_{j,k,t}, \qquad b_s = \sum_{j=0}^{s}\sum_{k=0}^{s}\sum_{t=0}^{s} T_{j,k,t}.$$
--
--   The vanishing of the quantity $A$ of §5.2 is equivalent to $a_s = b_s$; Propositions 5.8 and 5.9 evaluate both sums.
--
--   **Formalization Note** The exponent of $q$ is an integer (possibly negative), so $q$ is raised to an integer power; the halves are written as binomial coefficients $\binom{s-k}{2}$ and $\binom{t}{2}$. $m$ is a free parameter here; the theorems tie it to $n, r, s$ by $s\,m = n\,r$.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 23, §5.4 (definitions of a_s and b_s)

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom

namespace HScattered.Hyperplanes

/-- The common summand of `a_s` and `b_s` (§5.4, arXiv:1906.10590v2, p. 23), with `m = rn/s`:
`q^{m j − m t + (s−k)(m − n) + ½(s−k−1)(s−k) + ½(t−1)t} [s k]_q [k j]_q [j t]_q (−1)^{t+k}`,
where `n(r − s)/s = m − n` and the halves are the binomial coefficients `C(s−k, 2)`, `C(t, 2)`.
The exponent is an integer, so `q` is raised to an integer power. -/
noncomputable def abTerm (q : ℝ) (n s m j k t : ℕ) : ℝ :=
  q ^ ((m : ℤ) * j - (m : ℤ) * t + ((s : ℤ) - k) * ((m : ℤ) - n) +
      ((s - k).choose 2 : ℕ) + (t.choose 2 : ℕ)) *
    gaussBinom q s k * gaussBinom q k j * gaussBinom q j t * (-1) ^ (t + k)

/-- §5.4 (p. 23): `a_s = ∑_{j=0}^s q^{nr − nj} ∑_{k=0}^s ∑_{t=0}^s (common summand)`. -/
noncomputable def aSum (q : ℝ) (n r s m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), q ^ ((n : ℤ) * r - (n : ℤ) * j) *
    ∑ k ∈ Finset.range (s + 1), ∑ t ∈ Finset.range (s + 1), abTerm q n s m j k t

/-- §5.4 (p. 23): `b_s = ∑_{j=0}^s ∑_{k=0}^s ∑_{t=0}^s (common summand)`. -/
noncomputable def bSum (q : ℝ) (n s m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), ∑ k ∈ Finset.range (s + 1), ∑ t ∈ Finset.range (s + 1),
    abTerm q n s m j k t

end HScattered.Hyperplanes


