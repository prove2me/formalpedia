-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch01_ch1Q
-- name    : RamanujanLostNotebook_PartI_ch01_ch1Q
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T12:13:46.100405+00:00
-- url     : https://prove2.me/theorems/c7ebf25f-ed27-49ca-a70c-6daa08fa02ba
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 1: ch1Q
-- statement:
--   The editors' reconstruction of Q, (1.2.10), p. 16, with q^(-1/5)
--   represented by exp(-t/5). The theta denominator must be nonzero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 1.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_ramanujanTheta

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The editors' reconstruction of Q, (1.2.10), p. 16, with q^(-1/5)
represented by exp(-t/5). The theta denominator must be nonzero. -/
noncomputable def ch1Q (l t : ℂ) : ℂ :=
  (l * ramanujanTheta (-(l ^ 5) * Complex.exp (4 * t))
      (-(l ^ 20) * Complex.exp (11 * t)) -
    l ^ 3 * Complex.exp t * ramanujanTheta (-Complex.exp t)
      (-(l ^ 25) * Complex.exp (14 * t))) /
    (Complex.exp (-t / 5) * ramanujanTheta (-(l ^ 10) * Complex.exp (5 * t))
      (-(l ^ 15) * Complex.exp (10 * t)))

end RamanujanLostNotebook.PartI

end


