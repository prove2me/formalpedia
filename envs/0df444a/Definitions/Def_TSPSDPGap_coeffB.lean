-- Prove2me | Definitions.Def_TSPSDPGap_coeffB
-- name    : TSPSDPGap_coeffB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:09.50029+00:00
-- url     : https://prove2.me/theorems/f4b433f6-7a11-4a73-b0ce-b82afdc24153
-- title:
--   Coefficients $b_i$ of the circulant matrix $B$
-- statement:
--   With $a_i$ as above and $d=n/2$, for $1\le i\le d$,
--   $$
--   b_i=\begin{cases}\dfrac{2g-(n-g)a_i}{n(g-1)}, & i<d,\\[1.5ex] \dfrac{g-(n-g)a_i}{n(g-1)}, & i=d.\end{cases}
--   $$
--   They are the weights of $B=\sum_{i=1}^d b_iC_i$ in the feasible solution (3).
--
--   **Formalization Note** Real division; the second branch is used for every $i\ge d$, but only $i=d$ occurs.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, §4.1, p.15

import Mathlib
import Definitions.Def_TSPSDPGap_coeffA

namespace TSPSDPGap

/-- **The coefficients `b_i` of the circulant matrix `B`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, §4.1, p.15: "We also set
b_i = (2g − (n−g)a_i) / (n(g−1)), i < d;  b_i = (g − (n−g)a_i) / (n(g−1)), i = d."

**Formalization Note.** Real arithmetic, `d = n/2` (natural-number division). The paper uses
`b_i` only for `1 ≤ i ≤ d`; the `else` branch is the printed `i = d` case. -/
noncomputable def coeffB (g n i : ℕ) : ℝ :=
  if i < n / 2 then
    (2 * (g : ℝ) - ((n : ℝ) - g) * coeffA g n i) / ((n : ℝ) * ((g : ℝ) - 1))
  else
    ((g : ℝ) - ((n : ℝ) - g) * coeffA g n i) / ((n : ℝ) * ((g : ℝ) - 1))

end TSPSDPGap


