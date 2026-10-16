-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01ContourGrid
-- name    : TaoFivePrimes_RHBatch01ContourGrid
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T17:08:12.105453+00:00
-- url     : https://prove2.me/theorems/7d431b01-6a0c-43a3-a091-322a480ceb17
-- title:
--   Proposed polynomial jet tables on all four contour edges
-- statement:
--   Transparent lookup into the24 existing proposed horizontal FFT output tables and the two existing proposed vertical jet tables. Bottom coefficients are complex conjugates of upper coefficients. Lists data only and asserts no analytic accuracy, nonvanishing, winding, count or RH result.
-- source:
--   Platt Fourier polynomial DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalJetsLeft
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalJetsRight
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutput00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperNeg64K01
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperNeg64K02
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperNeg64K03
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperNeg64K04
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperNeg64K05
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperNeg64K06
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperNeg64K07
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperZeroK01
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperZeroK02
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperZeroK03
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperZeroK04
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperZeroK05
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperZeroK06
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperZeroK07
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperPos64K00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperPos64K01
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperPos64K02
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperPos64K03
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperPos64K04
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperPos64K05
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperPos64K06
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperPos64K07
set_option autoImplicit false
namespace RHBatch01ContourGrid
noncomputable def horizontalRows : List (List (List (List Nat))) := [[RHBatch01ContourOutput00.rows,RHBatch01ContourOutputUpperNeg64K01.rows,RHBatch01ContourOutputUpperNeg64K02.rows,RHBatch01ContourOutputUpperNeg64K03.rows,RHBatch01ContourOutputUpperNeg64K04.rows,RHBatch01ContourOutputUpperNeg64K05.rows,RHBatch01ContourOutputUpperNeg64K06.rows,RHBatch01ContourOutputUpperNeg64K07.rows],[RHBatch01ContourOutputUpperZeroK00.rows,RHBatch01ContourOutputUpperZeroK01.rows,RHBatch01ContourOutputUpperZeroK02.rows,RHBatch01ContourOutputUpperZeroK03.rows,RHBatch01ContourOutputUpperZeroK04.rows,RHBatch01ContourOutputUpperZeroK05.rows,RHBatch01ContourOutputUpperZeroK06.rows,RHBatch01ContourOutputUpperZeroK07.rows],[RHBatch01ContourOutputUpperPos64K00.rows,RHBatch01ContourOutputUpperPos64K01.rows,RHBatch01ContourOutputUpperPos64K02.rows,RHBatch01ContourOutputUpperPos64K03.rows,RHBatch01ContourOutputUpperPos64K04.rows,RHBatch01ContourOutputUpperPos64K05.rows,RHBatch01ContourOutputUpperPos64K06.rows,RHBatch01ContourOutputUpperPos64K07.rows]]
noncomputable def horizontal (j k : Nat) : Int×Int :=
 let t:=if j<2048 then 0 else if j<4096 then 1 else 2
 let rs:=(((horizontalRows[t]?).getD [])[k]?).getD []
 RHHighContourVector.decode ((((rs[(j%2048)/512]?).getD [])[j%512]?).getD 0)
noncomputable def verticalRows : List (List (List Nat)) :=
 [RHBatch01VerticalJetsRight.rows,RHBatch01VerticalJetsLeft.rows]
noncomputable def jet (e j k : Nat) : Int×Int :=
 if e=0 ∨ e=2 then
  let p:=horizontal j k
  if e=0 then (p.1,-p.2) else p
 else RHHighContourVector.decode ((((((verticalRows[if e=1 then 0 else 1]?).getD [])[j]?).getD [])[k]?).getD 0)
noncomputable def cells (e : Nat) : Nat := if e=0 ∨ e=2 then 4096 else 128
end RHBatch01ContourGrid
noncomputable def TaoFivePrimes_RHBatch01ContourGrid : Nat := 8448


