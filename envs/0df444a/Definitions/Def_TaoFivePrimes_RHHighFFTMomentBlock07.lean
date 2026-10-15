-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighFFTMomentBlock07
-- name    : TaoFivePrimes_RHHighFFTMomentBlock07
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T03:09:01.894682+00:00
-- url     : https://prove2.me/theorems/ccdaff66-3c3e-475b-aefe-fab1781e2e4a
-- title:
--   FFT moment-table lookup, block7
-- statement:
--   Hierarchical lookup for2048 existing packed moment words, globalindices14336 through16383. Imports onlyfour lightweight published data modules. This wrapper asserts no correctness, accuracy, sign or zero-count claim.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Init
import Definitions.Def_TaoFivePrimes_RHHighMomentValues28
import Definitions.Def_TaoFivePrimes_RHHighMomentValues29
import Definitions.Def_TaoFivePrimes_RHHighMomentValues30
import Definitions.Def_TaoFivePrimes_RHHighMomentValues31
namespace RHHighFFTMomentBlock07
noncomputable def blocks : List (List (List Nat)) := [RHHighMomentValues28.rows,RHHighMomentValues29.rows,RHHighMomentValues30.rows,RHHighMomentValues31.rows]
noncomputable def word (i : Nat) : Nat :=
  let block:=(blocks[i/512]?).getD []
  let row:=(block[i%512/16]?).getD []
  (row[i%16]?).getD 0
end RHHighFFTMomentBlock07
noncomputable def TaoFivePrimes_RHHighFFTMomentBlock07 : Nat := 7


