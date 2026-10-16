-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
-- name    : TaoFivePrimes_RHFastKernelDirichletArithmetic
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T20:24:44.643202+00:00
-- url     : https://prove2.me/theorems/c573f3e8-3c79-4c29-9878-7262aeb4856f
-- title:
--   Parameterized low-import Dirichlet coefficient arithmetic
-- statement:
--   Existing exact integer log/bin/phase/exponential/normalized Dirichlet coefficient program, with the centerT as a natural-number argument and the public parameterized gamma Record type. Contains algorithms only. Does not claim that guards, proposed values, analytic errors, zero counts or RH hold.
-- source:
--   Platt Fourier construction DOI10.1090/mcom/3198. Same formulas as the accepted fixed-center Dirichlet arithmetic. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option autoImplicit false
namespace RHFastKernelDirichletArithmetic
open RHFastKernelLogData RHFastKernelGammaArithmetic
noncomputable def exponent (n : Nat) : Nat := n.log2
noncomputable def logInput (n : Nat) : Nat :=
  exponent n*RHFastKernelLogData.log2+rounded (n-2^(exponent n)) (n+2^(exponent n)) D
noncomputable def loga (n : Nat) : Nat := logInput n+(RHFastKernelLogData.log2pi-RHFastKernelLogData.log2)/2
noncomputable def compute (T n : Nat) : Record :=
  let lu:=rounded (n-2^(exponent n)) (n+2^(exponent n)) D
  let la:=loga n
  let rr:Int:=(-(la:Int))/2
  let ii:Int:= -(T:Int)*(la:Int)
  let k:Int:=(ii*10^50+(P:Int)*(D:Int))/(2*(P:Int)*(D:Int))
  let res:=ii*10^50-2*(P:Int)*k*(D:Int)
  let dp:=res.natAbs/(8*10^50)
  let da:=(-rr).toNat/256
  let cs:=phaseCS dp
  let w:=square (square (square ((cs.1:Int),(cs.2:Int))))
  let wi:=if res<0 then -w.2 else w.2
  let ea:=RHFastKernelNegativeExp.seed D da
  let a:=(List.range 8).foldl (fun z _ => z*z/D) ea
  ⟨lu,rr,ii,k,dp,decide (res<0),da,cs.1,cs.2,ea,a,
    (a:Int)*w.1/(D:Int)^8,(a:Int)*wi/(D:Int)^8⟩
noncomputable def bin (n : Nat) : Nat :=
  ((512*(loga n:Int)*10^50+(P:Int)*(D:Int))/(2*(P:Int)*(D:Int))).toNat
noncomputable def delta (n : Nat) : Int :=
  (512*(loga n:Int)*10^50-2*(P:Int)*(D:Int)*(bin n:Int))/(2*(P:Int))
noncomputable def power (n k : Nat) : Int :=
  (List.range k).foldl (fun a _ => a*delta n/(D:Int)) (D:Int)
noncomputable def coefficient (T n k : Nat) : Int×Int :=
  let v:=compute T n
  (v.gammaRe*power n k/(D:Int),v.gammaIm*power n k/(D:Int))
noncomputable def guard (n : Nat) (v : Record) : Bool :=
  RHFastKernelGammaGuards.guard v && decide (exponent n≤15 ∧ 2^(exponent n)≤n ∧ n≤2^(exponent n+1) ∧
    2*(delta n).natAbs≤D ∧ bin n≤1024)
end RHFastKernelDirichletArithmetic
noncomputable def TaoFivePrimes_RHFastKernelDirichletArithmetic : Nat := 50000


