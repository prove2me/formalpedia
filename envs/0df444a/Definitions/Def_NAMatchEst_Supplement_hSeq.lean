-- Prove2me | Definitions.Def_NAMatchEst_Supplement_hSeq
-- name    : NAMatchEst_Supplement_hSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:36:22.471009+00:00
-- url     : https://prove2.me/theorems/13aa33ef-a780-4e1f-a880-5a314b1e9277
-- title:
--   Stage degrees $h_j$ of the §7 templates
-- statement:
--   The **stage degrees** of the layered templates of §7.1 are the natural numbers
--
--   $$
--   h_0=\alpha,\qquad h_1=2\alpha^2,\qquad h_j=(\alpha+j-1)\,(2h_{j-1}-2h_{j-2})+h_{j-1}\quad (j\ge 2).
--   $$
--
--   $h_j$ is the degree of the nodes introduced at stage $j$. After the last stage the template degrees are $b=2h_{r-2}$ on every node except $C_{r-1}$, and $h=h_{r-1}$ on $C_{r-1}$.
--
--   **Formalization Note** Natural-number subtraction; it never truncates because $h_j\ge 2h_{j-1}$ (p.93).
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §7.1, pp.92–93 (PDF 96–97)

import Mathlib

namespace NAMatchEst.Supplement

/-- The **stage degrees** `h_j` of the §7.1 templates: `h_0 = α`, `h_1 = 2α²` and
`h_j = (α + j − 1)(2h_{j−1} − 2h_{j−2}) + h_{j−1}` for `j ≥ 2`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §7.1, pp.92–93
(PDF 96–97): "Set h_0 = α, the initial maximum degree", "each new node has degree
h_1 = α + α(2α − 1) = 2α²", and "h_j = (α + j − 1)(2h_{j−1} − 2h_{j−2}) + h_{j−1} for
2 ⩽ j ⩽ r − 1".

**Formalization Note** Natural-number arithmetic. The subtraction `2h_{j−1} − 2h_{j−2}` never
truncates, since `h_j ⩾ 2h_{j−1}` (p.93). The paper's `b = 2h_{r−2}` and `h = h_{r−1}` are
`2 * hSeq α (r - 2)` and `hSeq α (r - 1)`. -/
def hSeq (α : ℕ) : ℕ → ℕ
  | 0 => α
  | 1 => 2 * α ^ 2
  | j + 2 => (α + j + 1) * (2 * hSeq α (j + 1) - 2 * hSeq α j) + hSeq α (j + 1)

end NAMatchEst.Supplement


