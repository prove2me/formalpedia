-- Prove2me | Definitions.Def_LL_Decomp1543c_Uf
-- name    : LL_Decomp1543c_Uf
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T17:29:38.405742+00:00
-- url     : https://prove2.me/theorems/35f1611f-c13f-4e25-af11-cded54a81b13
-- title:
--   The parameter $U$
-- statement:
--   For natural $N$, $U(N)=N^{2/5}(\log N)^{-4/5}$, with real powers.

import Mathlib

namespace LL_Decomp1543c

open Real Finset ArithmeticFunction

noncomputable def Uf (N : ℕ) : ℝ := (N : ℝ) ^ ((2 : ℝ) / 5) * Real.log N ^ (-(4 : ℝ) / 5)

end LL_Decomp1543c


