-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighFFTMomentBlock03
-- name    : TaoFivePrimes_RHHighFFTMomentBlock03
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T02:41:11.629551+00:00
-- url     : https://prove2.me/theorems/c5b1daab-1d9b-41a0-971a-035ebef7d5bc
-- title:
--   FFT moment-table lookup, block3
-- statement:
--   Hierarchical lookup for2048 existing packed moment words, globalindices6144 through8191. Imports onlyfour lightweight published data modules. This wrapper asserts no correctness, accuracy, sign or zero-count claim.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Init
import Definitions.Def_TaoFivePrimes_RHHighMomentValues12
import Definitions.Def_TaoFivePrimes_RHHighMomentValues13
import Definitions.Def_TaoFivePrimes_RHHighMomentValues14
import Definitions.Def_TaoFivePrimes_RHHighMomentValues15
namespace RHHighFFTMomentBlock03
noncomputable def blocks : List (List (List Nat)) := [RHHighMomentValues12.rows,RHHighMomentValues13.rows,RHHighMomentValues14.rows,RHHighMomentValues15.rows]
noncomputable def word (i : Nat) : Nat :=
  let block:=(blocks[i/512]?).getD []
  let row:=(block[i%512/16]?).getD []
  (row[i%16]?).getD 0
end RHHighFFTMomentBlock03
noncomputable def TaoFivePrimes_RHHighFFTMomentBlock03 : Nat := 3


