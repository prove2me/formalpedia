-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighFFTMomentBlock06
-- name    : TaoFivePrimes_RHHighFFTMomentBlock06
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T03:01:06.793923+00:00
-- url     : https://prove2.me/theorems/301aeff3-6c78-4ff2-be2a-e0a341a824f2
-- title:
--   FFT moment-table lookup, block6
-- statement:
--   Hierarchical lookup for2048 existing packed moment words, globalindices12288 through14335. Imports onlyfour lightweight published data modules. This wrapper asserts no correctness, accuracy, sign or zero-count claim.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Init
import Definitions.Def_TaoFivePrimes_RHHighMomentValues24
import Definitions.Def_TaoFivePrimes_RHHighMomentValues25
import Definitions.Def_TaoFivePrimes_RHHighMomentValues26
import Definitions.Def_TaoFivePrimes_RHHighMomentValues27
namespace RHHighFFTMomentBlock06
noncomputable def blocks : List (List (List Nat)) := [RHHighMomentValues24.rows,RHHighMomentValues25.rows,RHHighMomentValues26.rows,RHHighMomentValues27.rows]
noncomputable def word (i : Nat) : Nat :=
  let block:=(blocks[i/512]?).getD []
  let row:=(block[i%512/16]?).getD []
  (row[i%16]?).getD 0
end RHHighFFTMomentBlock06
noncomputable def TaoFivePrimes_RHHighFFTMomentBlock06 : Nat := 6


