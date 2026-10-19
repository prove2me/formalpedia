-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastPolynomialCircuitSemantics
-- name    : TaoFivePrimes_RHFastPolynomialCircuitSemantics
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T10:32:15.074991+00:00
-- url     : https://prove2.me/theorems/42e46e78-3afa-48d7-ac61-17fde4e3741b
-- title:
--   Polynomial circuit exact semantics
-- statement:
--   Complex list and polynomial semantics of the short center expression circuit. Equality of these semantics and ball containment require separate ordinary proofs.
-- source:
--   Platt DOI10.1090/mcom/3198; original attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastPolynomialCircuit
import Definitions.Def_TaoFivePrimes_RHFastComplexPolynomialLists
namespace RHFastPolynomialCircuitSemantics
open Complex Polynomial RHFastPolynomialCircuit
noncomputable def powerList (a:List ℂ) : Nat→List ℂ
 | 0 => [1]
 | n+1 => RHFastComplexPoly.mulList (powerList a n) a
noncomputable def evaluate (inputs:List ℂ) : Expr→List ℂ
 | .zero => [0]
 | .one => [1]
 | .imag => [I]
 | .variable => [0,1]
 | .input i => [RHFastComplexPoly.entry inputs i]
 | .rational p q => [(p:ℂ)/(q+1:ℂ)]
 | .add a b => RHFastComplexPoly.addList (evaluate inputs a) (evaluate inputs b)
 | .mul a b => RHFastComplexPoly.mulList (evaluate inputs a) (evaluate inputs b)
 | .divide a n => RHFastComplexPoly.divideList (evaluate inputs a) (n+1)
 | .power a n => powerList (evaluate inputs a) n
noncomputable def polynomial (inputs:List ℂ) : Expr→Polynomial ℂ
 | .zero => 0
 | .one => 1
 | .imag => C I
 | .variable => X
 | .input i => C (RHFastComplexPoly.entry inputs i)
 | .rational p q => C ((p:ℂ)/(q+1:ℂ))
 | .add a b => polynomial inputs a+polynomial inputs b
 | .mul a b => polynomial inputs a*polynomial inputs b
 | .divide a n => polynomial inputs a*C ((n+1:ℂ)⁻¹)
 | .power a n => (polynomial inputs a)^n
end RHFastPolynomialCircuitSemantics
noncomputable def TaoFivePrimes_RHFastPolynomialCircuitSemantics : Nat:=28


