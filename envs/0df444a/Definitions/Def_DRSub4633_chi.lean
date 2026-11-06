-- Prove2me | Definitions.Def_DRSub4633_chi
-- name    : DRSub4633_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:45.531833+00:00
-- url     : https://prove2.me/theorems/346b7ac7-956b-4c19-bb67-dc1fb7565dfb
-- title:
--   The coefficients $\chi_i$
-- statement:
--   For the labels $1\le i\le m$ of the large order,
--   $$\chi_i=\frac{q_i-q_{i+1}}{b}\ (i<m),\qquad \chi_m=\mathfrak c(q_m).$$
--   They are nonnegative and sum to $c_1$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (16), p.11

import Mathlib
import Definitions.Def_DRSub4633_qAt
import Definitions.Def_DRSub4633_mLarge
import Definitions.Def_DRSub4633_bPar
import Definitions.Def_DRSub4633_cFun

namespace DRSub4633

/-- **The coefficients `χᵢ`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (16), p.11:
`χᵢ = (qᵢ − qᵢ₊₁)/b` for `i < m` and `χ_m = 𝔠(q_m)`, with the labels of the large order (label `1`
the dummy coordinate, `q₁ = 1`). -/
noncomputable def chi {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : ℕ) : ℝ :=
  if i < mLarge x then (qAt x i - qAt x (i + 1)) / bPar else cFun (qAt x i)

end DRSub4633


