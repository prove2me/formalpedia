-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_ch05_ramanujanPhi
-- name    : RamanujanLostNotebook_PartIV_ch05_ramanujanPhi
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T15:51:27.801119+00:00
-- url     : https://prove2.me/theorems/f82df497-0aa7-4678-b198-c41fba870564
-- title:
--   Ramanujan's Lost Notebook Part IV, Ch. 5: ramanujanPhi
-- statement:
--   Ramanujan's function `ϕ(α, x) = 1 / ∏_{k ≥ 0} (1 + (x / (α + k))^2)` of (5.1.7), for real
--   `α > 0` and real `x`.  The product converges absolutely; by (5.5.9) it equals
--   `|Γ(α + i x)|^2 / Γ(α)^2` (stated separately as `eq_5_5_9`, which also asserts that the product
--   is multipliable, so that `tprod` is not a junk value).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 5.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- Ramanujan's function `ϕ(α, x) = 1 / ∏_{k ≥ 0} (1 + (x / (α + k))^2)` of (5.1.7), for real
`α > 0` and real `x`.  The product converges absolutely; by (5.5.9) it equals
`|Γ(α + i x)|^2 / Γ(α)^2` (stated separately as `eq_5_5_9`, which also asserts that the product
is multipliable, so that `tprod` is not a junk value). -/
noncomputable def ramanujanPhi (α x : ℝ) : ℝ :=
  (∏' k : ℕ, (1 + (x / (α + (k : ℝ))) ^ 2))⁻¹

end RamanujanLostNotebook.PartIV


