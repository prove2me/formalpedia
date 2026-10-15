-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighFFTArithmetic
-- name    : TaoFivePrimes_RHHighFFTArithmetic
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T01:56:59.909338+00:00
-- url     : https://prove2.me/theorems/82874ded-d209-455a-bb11-2da0b95d94e8
-- title:
--   Pure integer inputs for the high-height Fourier transform
-- statement:
--   Definitions of the hierarchical moment-word lookup, exact chirp lookup and chirped integer input. No accuracy or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198, exact integer Bluestein inputs. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighChirpIndexed
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
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHHighFFTArithmetic
noncomputable def fieldBase : Nat := 79228162514264337593543950336
noncomputable def bias : Int := 39614081257132168796771975168
noncomputable def decode (p k : Nat) : Int×Int :=
  (((p/fieldBase^(2*k)%fieldBase:Nat):Int)-bias,((p/fieldBase^(2*k+1)%fieldBase:Nat):Int)-bias)
noncomputable def momentBlocks : List (List (List Nat)) := [RHHighMomentValues00.rows,RHHighMomentValues01.rows,RHHighMomentValues02.rows,RHHighMomentValues03.rows,RHHighMomentValues04.rows,RHHighMomentValues05.rows,RHHighMomentValues06.rows,RHHighMomentValues07.rows,RHHighMomentValues08.rows,RHHighMomentValues09.rows,RHHighMomentValues10.rows,RHHighMomentValues11.rows,RHHighMomentValues12.rows,RHHighMomentValues13.rows,RHHighMomentValues14.rows,RHHighMomentValues15.rows,RHHighMomentValues16.rows,RHHighMomentValues17.rows,RHHighMomentValues18.rows,RHHighMomentValues19.rows,RHHighMomentValues20.rows,RHHighMomentValues21.rows,RHHighMomentValues22.rows,RHHighMomentValues23.rows,RHHighMomentValues24.rows,RHHighMomentValues25.rows,RHHighMomentValues26.rows,RHHighMomentValues27.rows,RHHighMomentValues28.rows,RHHighMomentValues29.rows,RHHighMomentValues30.rows,RHHighMomentValues31.rows]
noncomputable def word (i : Nat) : Nat :=
  let block:=(momentBlocks[i/512]?).getD []
  let row:=(block[i%512/16]?).getD []
  (row[i%16]?).getD 0
noncomputable def momentInput (i k : Nat) : Int×Int := decode (word i) k
noncomputable def chirp (j : Nat) : Int×Int :=
  let q:=j*j%32768
  let v:RHHighChirpCache.Record := RHHighChirpIndexed.lookup (min q (32768-q))
  (v.r,if q>16384 then -v.i else v.i)
noncomputable def rawInput (i k : Nat) : Int×Int :=
  let m:=momentInput i k
  let c:=chirp i
  (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)
end RHHighFFTArithmetic
noncomputable def TaoFivePrimes_RHHighFFTArithmetic : Nat := 16384


