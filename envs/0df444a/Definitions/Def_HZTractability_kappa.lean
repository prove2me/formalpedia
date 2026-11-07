-- Prove2me | Definitions.Def_HZTractability_kappa
-- name    : HZTractability_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:39.780374+00:00
-- url     : https://prove2.me/theorems/10562841-8168-4d0b-b549-078debba9b79
-- title:
--   The threshold tolerance $\kappa = 1/200$
-- statement:
--   The paper fixes the tolerance of the threshold game once and for all:
--   $$
--   \kappa = \frac{1}{200}.
--   $$
--   Every statement about the market construction, its parameters and its decoding uses this value.
--
--   **Formalization Note** A rational constant, cast to the reals where it meets prices.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §1 (Organization and notation), p.6 (PDF p.8); §2.1, p.6

import Mathlib

namespace HZTractability

/-- **The threshold tolerance** `κ = 1/200` (Panageas, Shein, Taherijam, Vazirani, *Exploring the
Tractability Frontier of Hylland–Zeckhauser Models*, arXiv:2610.35848, held version, sha256
74b7bf9f…, §1 "Organization and notation", p.6 (PDF 8): "We fix a rational middle utility
a ∈ (0, 1) and the threshold tolerance κ = 1/200"; also §2.1, p.6: "We fix κ = 1/200").

**Formalization Note** A rational constant; it is cast to `ℝ` where it meets real prices. -/
def kappa : ℚ := 1 / 200

end HZTractability


