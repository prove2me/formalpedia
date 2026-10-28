-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBoundB
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBoundB
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:19:06.476986+00:00
-- url     : https://prove2.me/theorems/a321d27c-c485-422d-9854-c0c5f8373d28
-- title:
--   DimBoundB: dimF bounds n>=35000
-- statement:
--   Upper-range densified dimension bound: for $35000\le n<62478$, one has $0<\mathrm{dimF}(n)\le 22$, combining DimBound packs 7--12.
-- source:
--   R8 Bit Oppbank densified DIMT; Track BitNB DimBound split

-- DimBoundB: densified dimF bounds on 35000 ≤ n < 62478 (packs 7-12).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound7
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound8
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound9
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound10
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound11
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound12
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.DimBound7
open IntMul.Kappa.R8.Bit.Oppbank.DimBound8
open IntMul.Kappa.R8.Bit.Oppbank.DimBound9
open IntMul.Kappa.R8.Bit.Oppbank.DimBound10
open IntMul.Kappa.R8.Bit.Oppbank.DimBound11
open IntMul.Kappa.R8.Bit.Oppbank.DimBound12

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBoundB

theorem dimF_le_22_ge_35000 : ∀ n, 35000 ≤ n → n < 62478 → dimF n ≤ 22 := by
  intro n hlo hn
  by_cases h7 : n < 40000
  · exact DimBound7.dimF_le_22_range n hlo h7
  · by_cases h8 : n < 45000
    · exact DimBound8.dimF_le_22_range n (by omega) h8
    · by_cases h9 : n < 50000
      · exact DimBound9.dimF_le_22_range n (by omega) h9
      · by_cases h10 : n < 55000
        · exact DimBound10.dimF_le_22_range n (by omega) h10
        · by_cases h11 : n < 60000
          · exact DimBound11.dimF_le_22_range n (by omega) h11
          · exact DimBound12.dimF_le_22_range n (by omega) hn

theorem dimF_pos_ge_35000 : ∀ n, 35000 ≤ n → n < 62478 → 0 < dimF n := by
  intro n hlo hn
  by_cases h7 : n < 40000
  · exact DimBound7.dimF_pos_range n hlo h7
  · by_cases h8 : n < 45000
    · exact DimBound8.dimF_pos_range n (by omega) h8
    · by_cases h9 : n < 50000
      · exact DimBound9.dimF_pos_range n (by omega) h9
      · by_cases h10 : n < 55000
        · exact DimBound10.dimF_pos_range n (by omega) h10
        · by_cases h11 : n < 60000
          · exact DimBound11.dimF_pos_range n (by omega) h11
          · exact DimBound12.dimF_pos_range n (by omega) hn

end IntMul.Kappa.R8.Bit.Oppbank.DimBoundB


