-- Prove2me | Definitions.Def_DuanCV_Gauss_standardFormII
-- name    : DuanCV_Gauss_standardFormII
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:35.008729+00:00
-- url     : https://prove2.me/theorems/7635b43b-e43c-4295-a45e-772fbf51b882
-- title:
--   The matrix $M_s^{II}$ of standard form II
-- statement:
--   In the order $(\hat x_1,\hat p_1,\hat x_2,\hat p_2)$, the standard form II correlation matrix is
--
--   $$M_s^{II}=\begin{pmatrix} n_1&0&c_1&0\\ 0&n_2&0&c_2\\ c_1&0&m_1&0\\ 0&c_2&0&m_2\end{pmatrix}.$$
--
--   So $n_1,n_2$ belong to $\hat x_1,\hat p_1$, the entries $m_1,m_2$ belong to $\hat x_2,\hat p_2$, the entry $c_1$ couples the positions and $c_2$ couples the momenta. With $n_1=n_2$ and $m_1=m_2$ this is the standard form I of Eq. (8).
--
--   **Formalization Note** This is only a real matrix; it carries no claim that it is the covariance of a state.
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Eq. (10), p. 3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

namespace DuanCV.Gauss

/-- **The matrix `M_s^{II}` of standard form II.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, Eq. (10), p. 3.

In the order `(x̂₁, p̂₁, x̂₂, p̂₂)` the rows are `(n₁, 0, c₁, 0)`, `(0, n₂, 0, c₂)`, `(c₁, 0, m₁, 0)`,
`(0, c₂, 0, m₂)`. So `n₁, n₂` are the `x̂₁, p̂₁` entries, `m₁, m₂` the `x̂₂, p̂₂` entries, `c₁` is the
`x̂₁x̂₂` entry and `c₂` the `p̂₁p̂₂` entry.

**Formalization Note.** This is a real matrix and carries no state claim. With `n₁ = n₂` and
`m₁ = m₂` it is `Claimed50.P19.standardFormCovariance`, the paper's standard form I (8). -/
def standardFormII (n1 n2 m1 m2 c1 c2 : ℝ) : Cov 2 := fun i j =>
  if i.1 = j.1 then
    (if i.2 = j.2 then
      (if i.1 = 0 then (if i.2 = 0 then n1 else n2) else (if i.2 = 0 then m1 else m2))
    else 0)
  else if i.2 = j.2 then (if i.2 = 0 then c1 else c2) else 0

end DuanCV.Gauss


