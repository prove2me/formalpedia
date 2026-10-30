-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch08_ch08Q
-- name    : RamanujanLostNotebook_PartI_ch08_ch08Q
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T03:02:00.675172+00:00
-- url     : https://prove2.me/theorems/601d15b5-30b7-4e10-b5c6-d38967525532
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 8: ch08Q
-- statement:
--   Modified denominator Q_N(a), (8.2.1)--(8.2.2), pp.199,208.
--   For N>=2 the final denominator modification adds a*Q_(N-1)(0);
--   the prescribed initial values at N=0,1 remain 1,1. The quotient P_N/Q_N
--   represents the finite continued fraction only when Q_N is nonzero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 8.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch08_ch08PQ0

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Modified denominator Q_N(a), (8.2.1)--(8.2.2), pp.199,208.
For N>=2 the final denominator modification adds a*Q_(N-1)(0);
the prescribed initial values at N=0,1 remain 1,1. The quotient P_N/Q_N
represents the finite continued fraction only when Q_N is nonzero. -/
noncomputable def ch08Q (q a : ℂ) (N : ℕ) : ℂ :=
  if N < 2 then (ch08PQ0 q N).2 else
    (ch08PQ0 q N).2 + a * (ch08PQ0 q (N - 1)).2

end RamanujanLostNotebook.PartI

end


