-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBoundA
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBoundA
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:16:30.964638+00:00
-- url     : https://prove2.me/theorems/0da7f4ad-bbef-43b0-be93-c375bd44d74e
-- title:
--   DimBoundA: dimF bounds n<35000
-- statement:
--   Half-range densified dimension bound: for all node indices $n<35000$, one has $0<\mathrm{dimF}(n)\le 22$, combining DimBound packs 0--6.
-- source:
--   R8 Bit Oppbank densified DIMT; Track BitNB DimBound split

-- DimBoundA: densified dimF bounds on n < 35000 (packs 0-6).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound0
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound5
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound6
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.DimBound0
open IntMul.Kappa.R8.Bit.Oppbank.DimBound1
open IntMul.Kappa.R8.Bit.Oppbank.DimBound2
open IntMul.Kappa.R8.Bit.Oppbank.DimBound3
open IntMul.Kappa.R8.Bit.Oppbank.DimBound4
open IntMul.Kappa.R8.Bit.Oppbank.DimBound5
open IntMul.Kappa.R8.Bit.Oppbank.DimBound6

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBoundA

theorem dimF_le_22_lt_35000 : ∀ n < 35000, dimF n ≤ 22 := by
  intro n hn
  by_cases h0 : n < 5000
  · exact DimBound0.dimF_le_22_range n (by omega) h0
  · by_cases h1 : n < 10000
    · exact DimBound1.dimF_le_22_range n (by omega) h1
    · by_cases h2 : n < 15000
      · exact DimBound2.dimF_le_22_range n (by omega) h2
      · by_cases h3 : n < 20000
        · exact DimBound3.dimF_le_22_range n (by omega) h3
        · by_cases h4 : n < 25000
          · exact DimBound4.dimF_le_22_range n (by omega) h4
          · by_cases h5 : n < 30000
            · exact DimBound5.dimF_le_22_range n (by omega) h5
            · exact DimBound6.dimF_le_22_range n (by omega) hn

theorem dimF_pos_lt_35000 : ∀ n < 35000, 0 < dimF n := by
  intro n hn
  by_cases h0 : n < 5000
  · exact DimBound0.dimF_pos_range n (by omega) h0
  · by_cases h1 : n < 10000
    · exact DimBound1.dimF_pos_range n (by omega) h1
    · by_cases h2 : n < 15000
      · exact DimBound2.dimF_pos_range n (by omega) h2
      · by_cases h3 : n < 20000
        · exact DimBound3.dimF_pos_range n (by omega) h3
        · by_cases h4 : n < 25000
          · exact DimBound4.dimF_pos_range n (by omega) h4
          · by_cases h5 : n < 30000
            · exact DimBound5.dimF_pos_range n (by omega) h5
            · exact DimBound6.dimF_pos_range n (by omega) hn

end IntMul.Kappa.R8.Bit.Oppbank.DimBoundA


