-- Prove2me | Definitions.Def_TSPSDPGap_aHat
-- name    : TSPSDPGap_aHat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:28.542444+00:00
-- url     : https://prove2.me/theorems/a9c608c2-8dbd-4d7e-a73d-4ae5e1dd9de6
-- title:
--   Cosine transform $a^{(k)}=\sum_{i=1}^d a_i\cos(2\pi ik/n)$
-- statement:
--   $$
--   a^{(k)}=\sum_{i=1}^{d}a_i\cos\Bigl(\frac{2\pi ik}{n}\Bigr),\qquad d=n/2,\ k\in\mathbb N .
--   $$
--   Half the eigenvalues of the circulant matrix $A$ (Claim 4.15).
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Proposition 4.14, p.21

import Mathlib
import Definitions.Def_TSPSDPGap_coeffA

namespace TSPSDPGap

/-- **The cosine transform `a^{(k)} = Σ_{i=1}^d a_i cos(2πik/n)`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Proposition 4.14, p.21: "As before, define a^{(k)} = Σ_{i=1}^d a_i cos(2πik/n)".

**Formalization Note.** `d = n/2` (natural-number division), `k : ℕ`, real arithmetic. -/
noncomputable def aHat (g n k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (n / 2), coeffA g n i * Real.cos (2 * Real.pi * i * k / n)

end TSPSDPGap


