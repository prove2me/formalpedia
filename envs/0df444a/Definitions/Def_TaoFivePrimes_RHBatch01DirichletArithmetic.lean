-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01DirichletArithmetic
-- name    : TaoFivePrimes_RHBatch01DirichletArithmetic
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T15:55:15.558812+00:00
-- url     : https://prove2.me/theorems/276f3d9e-4000-45ff-9693-654a05abdd75
-- title:
--   Exact logarithm, phase, weight and bin arithmetic for50000 Dirichlet terms
-- statement:
--   Transparent fixed-point algorithms for the50000 Dirichlet terms atT3289999808. Reuses the ordinary rational logarithm and phase algorithms. The definition itself asserts no numerical accuracy, endpoint sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198, finite Fourier reconstruction. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham; Euler–Maclaurin foundations alya/Community(Bot)/dbenbenn/Davenport.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01GammaArithmetic
set_option autoImplicit false
namespace RHBatch01DirichletArithmetic
open RHBatch01LogData RHBatch01GammaArithmetic
noncomputable def exponent (n : Nat) : Nat := n.log2
noncomputable def logInput (n : Nat) : Nat :=
  exponent n*RHBatch01LogData.log2+rounded (n-2^(exponent n)) (n+2^(exponent n)) D
noncomputable def loga (n : Nat) : Nat := logInput n+(RHBatch01LogData.log2pi-RHBatch01LogData.log2)/2
noncomputable def compute (n : Nat) : Record :=
  let lu:=rounded (n-2^(exponent n)) (n+2^(exponent n)) D
  let la:=loga n
  let rr:Int:=(-(la:Int))/2
  let ii:Int:= -3289999808*(la:Int)
  let k:Int:=(ii*10^50+(P:Int)*(D:Int))/(2*(P:Int)*(D:Int))
  let res:=ii*10^50-2*(P:Int)*k*(D:Int)
  let dp:=res.natAbs/(8*10^50)
  let da:=(-rr).toNat/256
  let cs:=phaseCS dp
  let w:=square (square (square ((cs.1:Int),(cs.2:Int))))
  let wi:=if res<0 then -w.2 else w.2
  let ea:=RHBatch01NegativeExp.seed D da
  let a:=(List.range 8).foldl (fun z _ => z*z/D) ea
  ⟨lu,rr,ii,k,dp,decide (res<0),da,cs.1,cs.2,ea,a,
    (a:Int)*w.1/(D:Int)^8,(a:Int)*wi/(D:Int)^8⟩
noncomputable def bin (n : Nat) : Nat :=
  ((512*(loga n:Int)*10^50+(P:Int)*(D:Int))/(2*(P:Int)*(D:Int))).toNat
noncomputable def delta (n : Nat) : Int :=
  (512*(loga n:Int)*10^50-2*(P:Int)*(D:Int)*(bin n:Int))/(2*(P:Int))
noncomputable def power (n k : Nat) : Int :=
  (List.range k).foldl (fun a _ => a*delta n/(D:Int)) (D:Int)
noncomputable def coefficient (n k : Nat) : Int×Int :=
  let v:=compute n
  (v.gammaRe*power n k/(D:Int),v.gammaIm*power n k/(D:Int))
noncomputable def guard (n : Nat) (v : Record) : Bool :=
  RHBatch01GammaGuards.guard v && decide (exponent n≤15 ∧ 2^(exponent n)≤n ∧ n≤2^(exponent n+1) ∧
    2*(delta n).natAbs≤D ∧ bin n≤1024)
end RHBatch01DirichletArithmetic
noncomputable def TaoFivePrimes_RHBatch01DirichletArithmetic : Nat := 50000


