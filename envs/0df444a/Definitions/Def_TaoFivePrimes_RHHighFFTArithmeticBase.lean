-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
-- name    : TaoFivePrimes_RHHighFFTArithmeticBase
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T02:19:37.665557+00:00
-- url     : https://prove2.me/theorems/f8be357e-fc88-482b-8486-24621cbefecb
-- title:
--   Chirp lookup and raw input arithmetic without moment-table imports
-- statement:
--   Transparent generic chirp lookup and integer input multiplication, taking a packed moment word as a parameter. No full moment tables are imported, and no accuracy or zero-count statement is asserted.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighChirpIndexed
set_option autoImplicit false
namespace RHHighFFTArithmeticBase
noncomputable def fieldBase : Nat := 79228162514264337593543950336
noncomputable def bias : Int := 39614081257132168796771975168
noncomputable def decode (p k : Nat) : Int×Int :=
  (((p/fieldBase^(2*k)%fieldBase:Nat):Int)-bias,((p/fieldBase^(2*k+1)%fieldBase:Nat):Int)-bias)
noncomputable def chirp (j : Nat) : Int×Int :=
  let q:=j*j%32768
  let v:RHHighChirpCache.Record := RHHighChirpIndexed.lookup (min q (32768-q))
  (v.r,if q>16384 then -v.i else v.i)
noncomputable def raw (p k i : Nat) : Int×Int :=
  let m:=decode p k
  let c:=chirp i
  (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)
end RHHighFFTArithmeticBase
noncomputable def TaoFivePrimes_RHHighFFTArithmeticBase : Nat := 16384


