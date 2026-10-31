-- Prove2me | Definitions.Def_TSPSDPGap_bHat
-- name    : TSPSDPGap_bHat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:59.275936+00:00
-- url     : https://prove2.me/theorems/0f326136-499c-4fe0-aeb0-f8ce79172f03
-- title:
--   Cosine transform $b^{(k)}=\sum_{i=1}^d b_i\cos(2\pi ik/n)$
-- statement:
--   $$
--   b^{(k)}=\sum_{i=1}^{d}b_i\cos\Bigl(\frac{2\pi ik}{n}\Bigr),\qquad d=n/2,\ k\in\mathbb N .
--   $$
--   Half the eigenvalues of the circulant matrix $B$ (Claim 4.15).
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Proposition 4.14, p.21

import Mathlib
import Definitions.Def_TSPSDPGap_coeffB

namespace TSPSDPGap

/-- **The cosine transform `b^{(k)} = Σ_{i=1}^d b_i cos(2πik/n)`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Proposition 4.14, p.21: "As before, define … b^{(k)} = Σ_{i=1}^d b_i cos(2πik/n)".

**Formalization Note.** `d = n/2` (natural-number division), `k : ℕ`, real arithmetic. -/
noncomputable def bHat (g n k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (n / 2), coeffB g n i * Real.cos (2 * Real.pi * i * k / n)

end TSPSDPGap


