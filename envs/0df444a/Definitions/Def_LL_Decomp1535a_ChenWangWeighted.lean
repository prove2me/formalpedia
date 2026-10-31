-- Prove2me | Definitions.Def_LL_Decomp1535a_ChenWangWeighted
-- name    : LL_Decomp1535a_ChenWangWeighted
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-30T14:09:11.507068+00:00
-- url     : https://prove2.me/theorems/e4e4e404-76f1-43f4-aa71-01ad03cd0a2c
-- title:
--   Weighted ternary statement above $C$
-- statement:
--   For a real $C$, the statement that $R_3(N)>0$ for every odd natural number $N$ with $C \le N$.

import Mathlib
import Definitions.Def_LL_Decomp1535a_R3

namespace LL_Decomp1535a

noncomputable section

open MeasureTheory

def ChenWangWeighted (C : ℝ) : Prop := ∀ N : ℕ, Odd N → C ≤ N → 0 < R3 N

end

end LL_Decomp1535a


