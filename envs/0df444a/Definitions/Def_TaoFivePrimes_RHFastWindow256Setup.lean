-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
-- name    : TaoFivePrimes_RHFastWindow256Setup
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T10:38:32.807991+00:00
-- url     : https://prove2.me/theorems/f69553ce-3039-47b1-863b-599d0da70e75
-- title:
--   256-bit center coefficient setup program
-- statement:
--   Transparent256-bit rescaling of the independently checked128-bit center seeds, polynomial-circuit evaluation, and recurrence for the24 moment factors. Concrete cached equality and analytic accuracy are separate proofs.
-- source:
--   Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastBallSeedPrograms
import Definitions.Def_TaoFivePrimes_RHFastPolynomialCircuit
namespace RHFastWindow256Setup
open RHFastBallArithmetic
noncomputable def D:Nat:=2^256
noncomputable def lift (a:Ball):Ball:=⟨a.re*(2:Int)^128,a.im*(2:Int)^128,a.radius*2^128⟩
noncomputable def inputs (T:Nat):List Ball:=
 [lift (RHFastBallSeedPrograms.center T),lift (RHFastBallSeedPrograms.inverseCenter T),
  lift (RHFastBallSeedPrograms.logCenter T),lift RHFastBallSeedPrograms.pi,lift (RHFastBallSeedPrograms.omega T)]
noncomputable def coefficients (T:Nat):List Ball:=
 RHFastPolynomialCircuit.evaluate D (inputs T) RHFastPolynomialCircuit.approximation
noncomputable def factor (pi:Ball):Nat→Ball
 |0=>integer D 1
 |n+1=>divide (mul D (factor pi n) (neg pi)) (n+1)
noncomputable def factors (pi:Ball):List Ball:=(List.range 24).map (factor pi)
end RHFastWindow256Setup
noncomputable def TaoFivePrimes_RHFastWindow256Setup : Nat:=256


