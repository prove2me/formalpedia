-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqHeadUnits
-- name    : GrothendieckLB_Supplement_cqHeadUnits
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T16:33:58.934309+00:00
-- url     : https://prove2.me/theorems/317697fa-be3a-4431-887a-5b8a010e8502
-- title:
--   Integer enclosures for the 125 cubic–quintic head coefficients
-- statement:
--   For $0\le j<125$, entry $j$ records the published absolute upper endpoint for the coefficient of degree $2j+3$ in units of $10^{-20}$. For an Arb ball with integer midpoint $m$, radius $r$ and decimal exponent $e$, the stored integer is
--   $$
--   \left\lceil (|m|+r)10^{e+20}\right\rceil .
--   $$
--   The entries retain sufficient precision to reproduce the finite sum in Proposition 6.3 using integer addition.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, https://arxiv.org/pdf/2608.11158v2, Proposition 6.3, equation (27), p. 21, and the b_head entries of https://github.com/trishullab/grothendieck-bounds/blob/17de8e2331859d37322c199a3d56fb81d740764f/upper-bounds/theorem-cubic-quintic/certificate.json

import Mathlib.Data.Nat.Basic

namespace GrothendieckLB.Supplement

/-- Absolute upper endpoints for degrees 3, 5, ..., 251 in units of 10^(-20).
Each entry is rounded upwards from the corresponding published Arb ball. -/
def cqHeadUnits : List ℕ :=
  [345387334391, 9043553622, 11714323435775, 149458672238, 574318350055300,
   144895102968875, 94418062677504, 110420328567074, 84519504614758, 56305585214318,
   31330174082601, 14685447113073, 6021901120041, 2058498871941, 342882862370,
   283759636418, 386629529866, 297704765858, 185724182105, 103347237230,
   51384544826, 20614286432, 4176374940, 2837042890, 4540545830,
   3994889059, 2905425132, 1918537920, 1162380901, 620693674,
   264589607, 61519409, 31623550, 60178032, 59141628,
   48434295, 36313663, 25246412, 15942857, 8799843,
   3950942, 1125331, 241675, 751596, 850857,
   786129, 661073, 513514, 364229, 231698,
   129213, 60551, 20763, 758, 8072,
   11475, 12305, 11650, 9974, 7713,
   5366, 3347, 1866, 923, 389,
   106, 48, 138, 188, 203,
   190, 156, 114, 76, 46,
   26, 15, 8, 4, 1,
   2, 3, 4, 4, 4,
   3, 2, 1, 1, 1,
   1, 1, 1, 1, 1,
   1, 1, 1, 1, 1,
   1, 1, 1, 1, 1,
   1, 1, 1, 1, 1,
   1, 1, 1, 1, 1,
   1, 1, 1, 1, 1,
   1, 1, 1, 1, 1]

end GrothendieckLB.Supplement


