-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelation
-- name    : TaoFivePrimes_RHBatch01ZetaCorrelation
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T19:51:50.540701+00:00
-- url     : https://prove2.me/theorems/4feafd1e-4b96-47d4-9eaf-f6aa5d53c416
-- title:
--   Exact binned Taylor and gamma-DFT correlation
-- statement:
--   Transparent ordinary integer program computing1025 complex unrounded correlations from one of24 global bin-coefficient rows and the proposed gamma DFT. Three272-bit packed convolutions, with offsets and sliding sums, produce each result. No exact computation result, analytic accuracy, sign, zero count or RH statement is asserted.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01GlobalDirichletBins
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT
set_option autoImplicit false
namespace RHBatch01ZetaCorrelation
noncomputable def sample (values : List Nat) (j : Nat) : Int×Int :=
  let p:=(values[j]?).getD 0
  (((p%2^96:Nat):Int)-2^95,((p/2^96%2^96:Nat):Int)-2^95)
noncomputable def signed (values : List Nat) (j : Nat) : Int×Int :=
  let p:=sample values j
  if j%2=0 then p else (-p.1,-p.2)
noncomputable def aReal (k : Nat) : List Nat := List.ofFn (fun j:Fin 929=>
  ((RHBatch01GlobalDirichletBins.coefficient (928-j.val) k).1+(2:Int)^140).toNat)
noncomputable def aImag (k : Nat) : List Nat := List.ofFn (fun j:Fin 929=>
  ((RHBatch01GlobalDirichletBins.coefficient (928-j.val) k).2+(2:Int)^140).toNat)
noncomputable def bReal (v : List Nat) : List Nat := List.ofFn (fun j:Fin 1954=>((signed v j.val).1+(2:Int)^100).toNat)
noncomputable def bImag (v : List Nat) : List Nat := List.ofFn (fun j:Fin 1954=>((signed v j.val).2+(2:Int)^100).toNat)
noncomputable def convolution (a b : List Nat) (A C : Nat) : List Int :=
  let digits:=(RHHighPackedFFT.digits 11 272 (Nat.shiftRight
    (RHHighPackedFFT.pack 10 272 a*RHHighPackedFFT.pack 11 272 b) (272*928))).take 1025
  let sums:=RHHighPackedFFT.windows 1025 (b.take 929).sum (b.take 1025) (b.drop 929)
  (digits.zip sums).map (fun p=>(p.1:Int)-(C:Int)*(a.sum:Int)-(A:Int)*(p.2:Int)+(929*A*C:Nat))
noncomputable def combine (rr ii ss : List Int) : List (Int×Int) :=
  ((rr.zip ii).zip ss).map (fun p=>(p.1.1-p.1.2,p.2-p.1.1-p.1.2))
noncomputable def output (k : Nat) (v : List Nat) : List (Int×Int) :=
  combine (convolution (aReal k) (bReal v) (2^140) (2^100))
    (convolution (aImag k) (bImag v) (2^140) (2^100))
    (convolution (((aReal k).zip (aImag k)).map (fun p=>p.1+p.2))
      (((bReal v).zip (bImag v)).map (fun p=>p.1+p.2)) (2^141) (2^101))
noncomputable def decode (v : List Nat) : List (Int×Int) := v.map (fun p=>
  (((p%2^256:Nat):Int)-2^255,((p/2^256%2^256:Nat):Int)-2^255))
end RHBatch01ZetaCorrelation
noncomputable def TaoFivePrimes_RHBatch01ZetaCorrelation : Nat := 1025


