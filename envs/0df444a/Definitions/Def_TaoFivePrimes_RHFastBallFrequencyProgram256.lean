-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastBallFrequencyProgram256
-- name    : TaoFivePrimes_RHFastBallFrequencyProgram256
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T10:36:53.949326+00:00
-- url     : https://prove2.me/theorems/12fd813b-5f39-43ad-b7c1-56cadccd4a5f
-- title:
--   Computed full-frequency256-bit certificate traces
-- statement:
--   A transparent loop program generates the full52-term Hermite,41-term exponential and21-term squaring traces used by the256-bit frequency checker. The checked Boolean remains a finite arithmetic claim.
-- source:
--   Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
namespace RHFastBallFrequencyProgram256
open RHFastBallArithmetic RHFastBallFrequencyChecker256
noncomputable def hermites (pi omega:Ball) (j:Nat) : List Ball:=
 let p:=pnu (frequency pi omega j)
 (List.range 50).foldl (fun hs n=>hs++[hermiteStep p n (entry hs n) (entry hs (n+1))]) [integer D 1,p]
noncomputable def exponentials (pi omega:Ball) (j:Nat) : List Ball:=
 let z:=divide (gaussianInput (frequency pi omega j)) (2^20)
 (List.range 40).foldl (fun es n=>es++[expStep z n (entry es n)]) [integer D 1]
noncomputable def squares (pi omega:Ball) (j:Nat) : List Ball:=
 (List.range 20).foldl (fun ss n=>ss++[mul D (entry ss n) (entry ss n)])
   [inflate (entry (exponentials pi omega j) 40) 1]
noncomputable def checked (j:Nat) (anchor pi root omega:Ball) (qs factors:List Ball)
 (reference:List (Int×Int)) : Bool:=
 valid j anchor pi root omega qs factors (hermites pi omega j) (exponentials pi omega j) (squares pi omega j) reference
end RHFastBallFrequencyProgram256
noncomputable def TaoFivePrimes_RHFastBallFrequencyProgram256 : Nat:=256


