-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighFFTMomentBlock04
-- name    : TaoFivePrimes_RHHighFFTMomentBlock04
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T02:50:15.534554+00:00
-- url     : https://prove2.me/theorems/5604ce8d-047c-4aed-99f4-b67f16078fec
-- title:
--   FFT moment-table lookup, block4
-- statement:
--   Hierarchical lookup for2048 existing packed moment words, globalindices8192 through10239. Imports onlyfour lightweight published data modules. This wrapper asserts no correctness, accuracy, sign or zero-count claim.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Init
import Definitions.Def_TaoFivePrimes_RHHighMomentValues16
import Definitions.Def_TaoFivePrimes_RHHighMomentValues17
import Definitions.Def_TaoFivePrimes_RHHighMomentValues18
import Definitions.Def_TaoFivePrimes_RHHighMomentValues19
namespace RHHighFFTMomentBlock04
noncomputable def blocks : List (List (List Nat)) := [RHHighMomentValues16.rows,RHHighMomentValues17.rows,RHHighMomentValues18.rows,RHHighMomentValues19.rows]
noncomputable def word (i : Nat) : Nat :=
  let block:=(blocks[i/512]?).getD []
  let row:=(block[i%512/16]?).getD []
  (row[i%16]?).getD 0
end RHHighFFTMomentBlock04
noncomputable def TaoFivePrimes_RHHighFFTMomentBlock04 : Nat := 4


