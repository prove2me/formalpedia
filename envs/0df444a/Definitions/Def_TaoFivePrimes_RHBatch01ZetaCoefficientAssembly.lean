-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01ZetaCoefficientAssembly
-- name    : TaoFivePrimes_RHBatch01ZetaCoefficientAssembly
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T15:44:49.016241+00:00
-- url     : https://prove2.me/theorems/a077516b-d20d-4907-b75d-5fae85939cc0
-- title:
--   Exact24-order Fourier coefficient assembly
-- statement:
--   Transparent linear integer program summing24 proposed correlation vectors, dividing by2^142, and setting the constant imaginary coefficient to zero. It also decodes the existing proposed Fourier polynomial coefficients. This definition asserts no equality or analytic accuracy.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaFourierData
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput00
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput01
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput02
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput03
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput04
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput05
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput06
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput07
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput08
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput09
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput10
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput11
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput12
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput13
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput14
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput15
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput16
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput17
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput18
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput19
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput20
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput21
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput22
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput23
set_option autoImplicit false
namespace RHBatch01ZetaCoefficientAssembly
noncomputable def packets : List (List Nat) := [RHBatch01ZetaCorrelationOutput00.rows.flatten,RHBatch01ZetaCorrelationOutput01.rows.flatten,RHBatch01ZetaCorrelationOutput02.rows.flatten,RHBatch01ZetaCorrelationOutput03.rows.flatten,RHBatch01ZetaCorrelationOutput04.rows.flatten,RHBatch01ZetaCorrelationOutput05.rows.flatten,RHBatch01ZetaCorrelationOutput06.rows.flatten,RHBatch01ZetaCorrelationOutput07.rows.flatten,RHBatch01ZetaCorrelationOutput08.rows.flatten,RHBatch01ZetaCorrelationOutput09.rows.flatten,RHBatch01ZetaCorrelationOutput10.rows.flatten,RHBatch01ZetaCorrelationOutput11.rows.flatten,RHBatch01ZetaCorrelationOutput12.rows.flatten,RHBatch01ZetaCorrelationOutput13.rows.flatten,RHBatch01ZetaCorrelationOutput14.rows.flatten,RHBatch01ZetaCorrelationOutput15.rows.flatten,RHBatch01ZetaCorrelationOutput16.rows.flatten,RHBatch01ZetaCorrelationOutput17.rows.flatten,RHBatch01ZetaCorrelationOutput18.rows.flatten,RHBatch01ZetaCorrelationOutput19.rows.flatten,RHBatch01ZetaCorrelationOutput20.rows.flatten,RHBatch01ZetaCorrelationOutput21.rows.flatten,RHBatch01ZetaCorrelationOutput22.rows.flatten,RHBatch01ZetaCorrelationOutput23.rows.flatten]
noncomputable def add (xs ys : List (Int×Int)) : List (Int×Int) :=
  List.zipWith (fun a b=>(a.1+b.1,a.2+b.2)) xs ys
noncomputable def total : List (Int×Int) := packets.foldl
  (fun acc xs=>add acc (RHBatch01ZetaCorrelation.decode xs)) (List.replicate 1025 (0,0))
noncomputable def rounded : List (Int×Int) := total.zipIdx.map (fun p=>
  (p.1.1/(2:Int)^142,if p.2=0 then 0 else p.1.2/(2:Int)^142))
noncomputable def expected : List (Int×Int) := RHHighPackedFFT.decode RHBatch01ZetaFourierData.rows.flatten
end RHBatch01ZetaCoefficientAssembly
noncomputable def TaoFivePrimes_RHBatch01ZetaCoefficientAssembly : Nat := 24


