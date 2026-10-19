-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastBallPolynomialArithmetic
-- name    : TaoFivePrimes_RHFastBallPolynomialArithmetic
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T10:17:48.861179+00:00
-- url     : https://prove2.me/theorems/0a9ec196-d5de-4f65-bf9a-536992fdeb66
-- title:
--   Integer error-ball polynomial-list arithmetic
-- statement:
--   Ordinary integer error-ball list addition, convolution and division for polynomial coefficients. All omitted entries are the exact zero ball. Definitions alone provide no coefficient containment or RH assertion.
-- source:
--   Coefficient arithmetic for the center Gaussian/Hermite method, Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastComplexBallArithmetic
namespace RHFastBallPoly
open RHFastBallArithmetic
noncomputable def entry (xs:List Ball) (i:Nat) : Ball := (xs[i]?).getD zero
noncomputable def addList (xs ys:List Ball) : List Ball :=
 (List.range (max xs.length ys.length)).map (fun i=>add (entry xs i) (entry ys i))
noncomputable def mulCoeff (D:Nat) (xs ys:List Ball) (k:Nat) : Ball :=
 (List.range (k+1)).foldl (fun a i=>add a
  (if i<xs.length ∧ i≤k ∧ k-i<ys.length then mul D (entry xs i) (entry ys (k-i)) else zero)) zero
noncomputable def mulList (D:Nat) (xs ys:List Ball) : List Ball :=
 (List.range (xs.length+ys.length-1)).map (mulCoeff D xs ys)
noncomputable def divideList (xs:List Ball) (n:Nat) : List Ball := xs.map (fun a=>divide a n)
end RHFastBallPoly
noncomputable def TaoFivePrimes_RHFastBallPolynomialArithmetic : Nat := 28


