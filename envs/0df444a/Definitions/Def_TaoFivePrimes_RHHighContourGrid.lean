-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighContourGrid
-- name    : TaoFivePrimes_RHHighContourGrid
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T08:38:27.275736+00:00
-- url     : https://prove2.me/theorems/b076a2ea-4d6d-49a8-bebc-bb7a9c4dd953
-- title:
--   Proposed polynomial jet tables on all four contour edges
-- statement:
--   Transparent lookup into the24 existing proposed horizontal FFT output tables and the two existing proposed vertical jet tables. Bottom coefficients are complex conjugates of upper coefficients. Lists data only and asserts no analytic accuracy, nonvanishing, winding, count or RH result.
-- source:
--   Platt Fourier polynomial DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighVerticalJetsLeft
import Definitions.Def_TaoFivePrimes_RHHighVerticalJetsRight
import Definitions.Def_TaoFivePrimes_RHHighContourOutput00
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperNeg64K01
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperNeg64K02
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperNeg64K03
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperNeg64K04
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperNeg64K05
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperNeg64K06
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperNeg64K07
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperZeroK01
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperZeroK02
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperZeroK03
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperZeroK04
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperZeroK05
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperZeroK06
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperZeroK07
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperPos64K00
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperPos64K01
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperPos64K02
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperPos64K03
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperPos64K04
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperPos64K05
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperPos64K06
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperPos64K07
set_option autoImplicit false
namespace RHHighContourGrid
noncomputable def horizontalRows : List (List (List (List Nat))) := [[RHHighContourOutput00.rows,RHHighContourOutputUpperNeg64K01.rows,RHHighContourOutputUpperNeg64K02.rows,RHHighContourOutputUpperNeg64K03.rows,RHHighContourOutputUpperNeg64K04.rows,RHHighContourOutputUpperNeg64K05.rows,RHHighContourOutputUpperNeg64K06.rows,RHHighContourOutputUpperNeg64K07.rows],[RHHighContourOutputUpperZeroK00.rows,RHHighContourOutputUpperZeroK01.rows,RHHighContourOutputUpperZeroK02.rows,RHHighContourOutputUpperZeroK03.rows,RHHighContourOutputUpperZeroK04.rows,RHHighContourOutputUpperZeroK05.rows,RHHighContourOutputUpperZeroK06.rows,RHHighContourOutputUpperZeroK07.rows],[RHHighContourOutputUpperPos64K00.rows,RHHighContourOutputUpperPos64K01.rows,RHHighContourOutputUpperPos64K02.rows,RHHighContourOutputUpperPos64K03.rows,RHHighContourOutputUpperPos64K04.rows,RHHighContourOutputUpperPos64K05.rows,RHHighContourOutputUpperPos64K06.rows,RHHighContourOutputUpperPos64K07.rows]]
noncomputable def horizontal (j k : Nat) : Int×Int :=
 let t:=if j<2048 then 0 else if j<4096 then 1 else 2
 let rs:=(((horizontalRows[t]?).getD [])[k]?).getD []
 RHHighContourVector.decode ((((rs[(j%2048)/512]?).getD [])[j%512]?).getD 0)
noncomputable def verticalRows : List (List (List Nat)) :=
 [RHHighVerticalJetsRight.rows,RHHighVerticalJetsLeft.rows]
noncomputable def jet (e j k : Nat) : Int×Int :=
 if e=0 ∨ e=2 then
  let p:=horizontal j k
  if e=0 then (p.1,-p.2) else p
 else RHHighContourVector.decode ((((((verticalRows[if e=1 then 0 else 1]?).getD [])[j]?).getD [])[k]?).getD 0)
noncomputable def cells (e : Nat) : Nat := if e=0 ∨ e=2 then 4096 else 128
end RHHighContourGrid
noncomputable def TaoFivePrimes_RHHighContourGrid : Nat := 8448


