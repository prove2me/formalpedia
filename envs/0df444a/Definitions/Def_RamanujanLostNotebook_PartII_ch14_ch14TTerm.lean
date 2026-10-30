-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch14_ch14TTerm
-- name    : RamanujanLostNotebook_PartII_ch14_ch14TTerm
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T04:33:20.648225+00:00
-- url     : https://prove2.me/theorems/8b05967e-d0e4-4670-809a-e12f0556bd22
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 14: ch14TTerm
-- statement:
--   Paired positive-index summand of T₂ₖ in (14.1.1), p.355.
--   Here r=n+1≥1, so both natural subtractions and the pentagonal divisions
--   are exact. Both branches have positive exponents; the constant is separate.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 14.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Paired positive-index summand of T₂ₖ in (14.1.1), p.355.
Here r=n+1≥1, so both natural subtractions and the pentagonal divisions
are exact. Both branches have positive exponents; the constant is separate. -/
noncomputable def ch14TTerm (k : ℕ) (q : ℂ) (n : ℕ) : ℂ :=
  let r := n + 1
  (-1 : ℂ) ^ r *
    (((6 * r - 1 : ℕ) : ℂ) ^ (2 * k) * q ^ (r * (3 * r - 1) / 2) +
      ((6 * r + 1 : ℕ) : ℂ) ^ (2 * k) * q ^ (r * (3 * r + 1) / 2))

end RamanujanLostNotebook.PartII

end


