-- Prove2me | Definitions.Def_AccelPPM_FPR_kimCoeff
-- name    : AccelPPM_FPR_kimCoeff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:38:54.189977+00:00
-- url     : https://prove2.me/theorems/477e0936-f1cb-47ba-bacb-1bed6609c768
-- title:
--   Kim's step coefficients (25): $h_{i,k}=-\frac{2k}{i(i+1)}$ for $k<i$, $h_{i,i}=\frac{2i}{i+1}$
-- statement:
--   Kim's step coefficients for the general proximal point method are, for $i\ge1$ and $1\le k\le i$,
--   $$
--   h_{i,k}=\begin{cases}-\dfrac{2k}{i(i+1)}, & k=1,\dots,i-1,\\[2mm] \dfrac{2i}{i+1}, & k=i.\end{cases}
--   $$
--   In the paper they are written for $i=1,\dots,N-1$, because the performance estimation problem runs $N$ steps; the values themselves do not depend on $N$. With these coefficients the general proximal point method attains the fixed-point residual rate $1/N^2$ (Lemma 4.1, Eq. (28)) and coincides with the proposed accelerated method (Proposition 4.1).
--
--   **Formalization Note** `kimCoeff i k` is a total function `ℕ → ℕ → ℝ` with the natural numbers cast to `ℝ`; it returns $2i/(i+1)$ when $k=i$ and $-2k/(i(i+1))$ otherwise. Only the values with $1\le k\le i$ are read by the general proximal point method and by the matrices of the dual problem (D); other values are irrelevant.
-- source:
--   Kim, Accelerated proximal point method for maximally monotone operators, arXiv:1905.05149v4, p. 8, Lemma 4.1, Eq. (25)

import Mathlib

namespace AccelPPM.FPR

/-- Kim's step coefficients (25) (arXiv:1905.05149v4, p. 8):
`h_{i,k} = −2k/(i(i+1))` for `k = 1, …, i − 1` and `h_{i,i} = 2i/(i+1)`.
Only the values with `1 ≤ k ≤ i` are meaningful; they are the only ones the general proximal
point method reads. The values do not depend on the horizon `N` of the performance estimation
problem. -/
noncomputable def kimCoeff (i k : ℕ) : ℝ :=
  if k = i then 2 * (i : ℝ) / ((i : ℝ) + 1) else -(2 * (k : ℝ)) / ((i : ℝ) * ((i : ℝ) + 1))

end AccelPPM.FPR


