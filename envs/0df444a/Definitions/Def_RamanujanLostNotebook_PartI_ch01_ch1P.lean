-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch01_ch1P
-- name    : RamanujanLostNotebook_PartI_ch01_ch1P
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T12:13:21.894077+00:00
-- url     : https://prove2.me/theorems/7bb48e9d-eb6d-4b8e-94c9-32c06d72b513
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 1: ch1P
-- statement:
--   The editors' reconstruction of P, (1.2.9), p. 16, in q=exp t.
--   It is used only when |λ^5 q^3|<1 and its theta denominator is nonzero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 1.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_ramanujanTheta

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The editors' reconstruction of P, (1.2.9), p. 16, in q=exp t.
It is used only when |λ^5 q^3|<1 and its theta denominator is nonzero. -/
noncomputable def ch1P (l t : ℂ) : ℂ :=
  (ramanujanTheta (-(l ^ 10) * Complex.exp (7 * t))
      (-(l ^ 15) * Complex.exp (8 * t)) +
    l * Complex.exp t * ramanujanTheta (-(l ^ 5) * Complex.exp (2 * t))
      (-(l ^ 20) * Complex.exp (13 * t))) /
    (Complex.exp (t / 5) * ramanujanTheta (-(l ^ 10) * Complex.exp (5 * t))
      (-(l ^ 15) * Complex.exp (10 * t)))

end RamanujanLostNotebook.PartI

end


