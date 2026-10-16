-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01AllMomentWords
-- name    : TaoFivePrimes_RHBatch01AllMomentWords
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T21:56:47.08118+00:00
-- url     : https://prove2.me/theorems/77348a95-455f-4b3f-ab6d-53c5d2d4693c
-- title:
--   Unified lookup for all proposed normalized moment words
-- statement:
--   A transparent bounded lookup joining the existing32 proposed moment-word packets into one16384-sample interface. Defines data only, with no arithmetic, analytic, sign, count or RH assertion.
-- source:
--   Existing Platt gamma Fourier data, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues00
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues01
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues02
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues03
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues04
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues05
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues06
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues07
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues08
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues09
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues10
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues11
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues12
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues13
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues14
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues15
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues16
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues17
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues18
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues19
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues20
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues21
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues22
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues23
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues24
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues25
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues26
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues27
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues28
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues29
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues30
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues31
namespace RHBatch01AllMomentWords
noncomputable def blocks : List (List (List Nat)) := [RHBatch01MomentValues00.rows,RHBatch01MomentValues01.rows,RHBatch01MomentValues02.rows,RHBatch01MomentValues03.rows,RHBatch01MomentValues04.rows,RHBatch01MomentValues05.rows,RHBatch01MomentValues06.rows,RHBatch01MomentValues07.rows,RHBatch01MomentValues08.rows,RHBatch01MomentValues09.rows,RHBatch01MomentValues10.rows,RHBatch01MomentValues11.rows,RHBatch01MomentValues12.rows,RHBatch01MomentValues13.rows,RHBatch01MomentValues14.rows,RHBatch01MomentValues15.rows,RHBatch01MomentValues16.rows,RHBatch01MomentValues17.rows,RHBatch01MomentValues18.rows,RHBatch01MomentValues19.rows,RHBatch01MomentValues20.rows,RHBatch01MomentValues21.rows,RHBatch01MomentValues22.rows,RHBatch01MomentValues23.rows,RHBatch01MomentValues24.rows,RHBatch01MomentValues25.rows,RHBatch01MomentValues26.rows,RHBatch01MomentValues27.rows,RHBatch01MomentValues28.rows,RHBatch01MomentValues29.rows,RHBatch01MomentValues30.rows,RHBatch01MomentValues31.rows]
noncomputable def word (i : Nat) : Nat :=
 (((((blocks[i/512]?).getD [])[i%512/16]?).getD [])[i%16]?).getD 0
end RHBatch01AllMomentWords
noncomputable def TaoFivePrimes_RHBatch01AllMomentWords : Nat := 16384


