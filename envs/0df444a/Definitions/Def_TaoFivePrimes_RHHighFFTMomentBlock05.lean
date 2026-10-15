-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighFFTMomentBlock05
-- name    : TaoFivePrimes_RHHighFFTMomentBlock05
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T02:56:26.204058+00:00
-- url     : https://prove2.me/theorems/172d80e0-b356-4713-bd28-f2e332a0dac8
-- title:
--   FFT moment-table lookup, block5
-- statement:
--   Hierarchical lookup for2048 existing packed moment words, globalindices10240 through12287. Imports onlyfour lightweight published data modules. This wrapper asserts no correctness, accuracy, sign or zero-count claim.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Init
import Definitions.Def_TaoFivePrimes_RHHighMomentValues20
import Definitions.Def_TaoFivePrimes_RHHighMomentValues21
import Definitions.Def_TaoFivePrimes_RHHighMomentValues22
import Definitions.Def_TaoFivePrimes_RHHighMomentValues23
namespace RHHighFFTMomentBlock05
noncomputable def blocks : List (List (List Nat)) := [RHHighMomentValues20.rows,RHHighMomentValues21.rows,RHHighMomentValues22.rows,RHHighMomentValues23.rows]
noncomputable def word (i : Nat) : Nat :=
  let block:=(blocks[i/512]?).getD []
  let row:=(block[i%512/16]?).getD []
  (row[i%16]?).getD 0
end RHHighFFTMomentBlock05
noncomputable def TaoFivePrimes_RHHighFFTMomentBlock05 : Nat := 5


