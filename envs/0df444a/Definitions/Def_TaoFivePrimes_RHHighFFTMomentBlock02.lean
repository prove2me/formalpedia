-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighFFTMomentBlock02
-- name    : TaoFivePrimes_RHHighFFTMomentBlock02
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T02:32:39.218096+00:00
-- url     : https://prove2.me/theorems/1eb4c0ed-34f6-4759-9a06-d81be092a89b
-- title:
--   FFT moment-table lookup, block2
-- statement:
--   Hierarchical lookup for2048 existing packed moment words, globalindices4096 through6143. Imports onlyfour lightweight published data modules. This wrapper asserts no correctness, accuracy, sign or zero-count claim.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Init
import Definitions.Def_TaoFivePrimes_RHHighMomentValues08
import Definitions.Def_TaoFivePrimes_RHHighMomentValues09
import Definitions.Def_TaoFivePrimes_RHHighMomentValues10
import Definitions.Def_TaoFivePrimes_RHHighMomentValues11
namespace RHHighFFTMomentBlock02
noncomputable def blocks : List (List (List Nat)) := [RHHighMomentValues08.rows,RHHighMomentValues09.rows,RHHighMomentValues10.rows,RHHighMomentValues11.rows]
noncomputable def word (i : Nat) : Nat :=
  let block:=(blocks[i/512]?).getD []
  let row:=(block[i%512/16]?).getD []
  (row[i%16]?).getD 0
end RHHighFFTMomentBlock02
noncomputable def TaoFivePrimes_RHHighFFTMomentBlock02 : Nat := 2


