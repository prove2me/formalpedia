-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch05_ch05EtaCoeff
-- name    : RamanujanLostNotebook_PartIII_ch05_ch05EtaCoeff
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T12:55:30.187879+00:00
-- url     : https://prove2.me/theorems/f2790626-f582-462f-925a-f7b3c203a62b
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 5: ch05EtaCoeff
-- statement:
--   Coefficient of X^n in a finite list of Euler powers, with pairs (d,r)
--   standing for ∏_{k≥1}(1-X^(d*k))^r. Negative exponents use exact reciprocal
--   binomial coefficients. The listed d are always positive.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 5.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch05_ch05EulerPower

namespace RamanujanLostNotebook.PartIII

/-- Coefficient of X^n in a finite list of Euler powers, with pairs (d,r)
standing for ∏_{k≥1}(1-X^(d*k))^r. Negative exponents use exact reciprocal
binomial coefficients. The listed d are always positive. -/
noncomputable def ch05EtaCoeff (factors : List (ℕ × ℤ)) (n : ℕ) : ℤ :=
  ((factors.map fun dr => ch05EulerPower dr.1 dr.2 n).prod).coeff n

end RamanujanLostNotebook.PartIII


