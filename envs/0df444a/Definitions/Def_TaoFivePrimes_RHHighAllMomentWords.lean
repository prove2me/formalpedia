-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighAllMomentWords
-- name    : TaoFivePrimes_RHHighAllMomentWords
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T07:24:36.564888+00:00
-- url     : https://prove2.me/theorems/5ad6ac56-a9d6-4d27-b3c0-a12ddd73465e
-- title:
--   Unified lookup for all proposed normalized moment words
-- statement:
--   A transparent bounded lookup joining the existing32 proposed moment-word packets into one16384-sample interface. Defines data only, with no arithmetic, analytic, sign, count or RH assertion.
-- source:
--   Existing Platt gamma Fourier data, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighMomentValues00
import Definitions.Def_TaoFivePrimes_RHHighMomentValues01
import Definitions.Def_TaoFivePrimes_RHHighMomentValues02
import Definitions.Def_TaoFivePrimes_RHHighMomentValues03
import Definitions.Def_TaoFivePrimes_RHHighMomentValues04
import Definitions.Def_TaoFivePrimes_RHHighMomentValues05
import Definitions.Def_TaoFivePrimes_RHHighMomentValues06
import Definitions.Def_TaoFivePrimes_RHHighMomentValues07
import Definitions.Def_TaoFivePrimes_RHHighMomentValues08
import Definitions.Def_TaoFivePrimes_RHHighMomentValues09
import Definitions.Def_TaoFivePrimes_RHHighMomentValues10
import Definitions.Def_TaoFivePrimes_RHHighMomentValues11
import Definitions.Def_TaoFivePrimes_RHHighMomentValues12
import Definitions.Def_TaoFivePrimes_RHHighMomentValues13
import Definitions.Def_TaoFivePrimes_RHHighMomentValues14
import Definitions.Def_TaoFivePrimes_RHHighMomentValues15
import Definitions.Def_TaoFivePrimes_RHHighMomentValues16
import Definitions.Def_TaoFivePrimes_RHHighMomentValues17
import Definitions.Def_TaoFivePrimes_RHHighMomentValues18
import Definitions.Def_TaoFivePrimes_RHHighMomentValues19
import Definitions.Def_TaoFivePrimes_RHHighMomentValues20
import Definitions.Def_TaoFivePrimes_RHHighMomentValues21
import Definitions.Def_TaoFivePrimes_RHHighMomentValues22
import Definitions.Def_TaoFivePrimes_RHHighMomentValues23
import Definitions.Def_TaoFivePrimes_RHHighMomentValues24
import Definitions.Def_TaoFivePrimes_RHHighMomentValues25
import Definitions.Def_TaoFivePrimes_RHHighMomentValues26
import Definitions.Def_TaoFivePrimes_RHHighMomentValues27
import Definitions.Def_TaoFivePrimes_RHHighMomentValues28
import Definitions.Def_TaoFivePrimes_RHHighMomentValues29
import Definitions.Def_TaoFivePrimes_RHHighMomentValues30
import Definitions.Def_TaoFivePrimes_RHHighMomentValues31
namespace RHHighAllMomentWords
noncomputable def blocks : List (List (List Nat)) := [RHHighMomentValues00.rows,RHHighMomentValues01.rows,RHHighMomentValues02.rows,RHHighMomentValues03.rows,RHHighMomentValues04.rows,RHHighMomentValues05.rows,RHHighMomentValues06.rows,RHHighMomentValues07.rows,RHHighMomentValues08.rows,RHHighMomentValues09.rows,RHHighMomentValues10.rows,RHHighMomentValues11.rows,RHHighMomentValues12.rows,RHHighMomentValues13.rows,RHHighMomentValues14.rows,RHHighMomentValues15.rows,RHHighMomentValues16.rows,RHHighMomentValues17.rows,RHHighMomentValues18.rows,RHHighMomentValues19.rows,RHHighMomentValues20.rows,RHHighMomentValues21.rows,RHHighMomentValues22.rows,RHHighMomentValues23.rows,RHHighMomentValues24.rows,RHHighMomentValues25.rows,RHHighMomentValues26.rows,RHHighMomentValues27.rows,RHHighMomentValues28.rows,RHHighMomentValues29.rows,RHHighMomentValues30.rows,RHHighMomentValues31.rows]
noncomputable def word (i : Nat) : Nat :=
 (((((blocks[i/512]?).getD [])[i%512/16]?).getD [])[i%16]?).getD 0
end RHHighAllMomentWords
noncomputable def TaoFivePrimes_RHHighAllMomentWords : Nat := 16384


