-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighFFTMomentBlock01
-- name    : TaoFivePrimes_RHHighFFTMomentBlock01
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T02:32:38.743113+00:00
-- url     : https://prove2.me/theorems/c0517de9-ff4c-48d0-9d29-51bf482966ec
-- title:
--   FFT moment-table lookup, block1
-- statement:
--   Hierarchical lookup for2048 existing packed moment words, globalindices2048 through4095. Imports onlyfour lightweight published data modules. This wrapper asserts no correctness, accuracy, sign or zero-count claim.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Init
import Definitions.Def_TaoFivePrimes_RHHighMomentValues04
import Definitions.Def_TaoFivePrimes_RHHighMomentValues05
import Definitions.Def_TaoFivePrimes_RHHighMomentValues06
import Definitions.Def_TaoFivePrimes_RHHighMomentValues07
namespace RHHighFFTMomentBlock01
noncomputable def blocks : List (List (List Nat)) := [RHHighMomentValues04.rows,RHHighMomentValues05.rows,RHHighMomentValues06.rows,RHHighMomentValues07.rows]
noncomputable def word (i : Nat) : Nat :=
  let block:=(blocks[i/512]?).getD []
  let row:=(block[i%512/16]?).getD []
  (row[i%16]?).getD 0
end RHHighFFTMomentBlock01
noncomputable def TaoFivePrimes_RHHighFFTMomentBlock01 : Nat := 1


