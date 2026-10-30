-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Product
-- name    : RamanujanLostNotebook_PartI_ch07_ch07Product
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T04:57:22.988244+00:00
-- url     : https://prove2.me/theorems/8d290be9-c29f-4b39-8f8a-8dfb3a7bb2c4
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07Product
-- statement:
--   The real character product P(x)=∏_{r=1}^{k-1}(e^{-rx};e^{-kx})∞^{-χ(r)}. The real powers use positive bases on x>0 under the product-positivity conclusions.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Poch

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The real character product P(x)=∏_{r=1}^{k-1}(e^{-rx};e^{-kx})∞^{-χ(r)}. The real powers use positive bases on x>0 under the product-positivity conclusions. -/
noncomputable def ch07Product (k : ℕ) (χ : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∏ r ∈ Finset.Icc 1 (k - 1), Real.rpow (ch07Poch k r x) (-χ r)

end RamanujanLostNotebook.PartI

end


