-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighZetaCoefficientAssembly
-- name    : TaoFivePrimes_RHHighZetaCoefficientAssembly
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T05:48:31.1366+00:00
-- url     : https://prove2.me/theorems/d9011574-dfc3-458a-93d7-346ef1a22568
-- title:
--   Exact24-order Fourier coefficient assembly
-- statement:
--   Transparent linear integer program summing24 proposed correlation vectors, dividing by2^142, and setting the constant imaginary coefficient to zero. It also decodes the existing proposed Fourier polynomial coefficients. This definition asserts no equality or analytic accuracy.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHHighZetaFourierData
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput00
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput01
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput02
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput03
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput04
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput05
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput06
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput07
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput08
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput09
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput10
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput11
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput12
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput13
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput14
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput15
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput16
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput17
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput18
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput19
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput20
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput21
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput22
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput23
set_option autoImplicit false
namespace RHHighZetaCoefficientAssembly
noncomputable def packets : List (List Nat) := [RHHighZetaCorrelationOutput00.rows.flatten,RHHighZetaCorrelationOutput01.rows.flatten,RHHighZetaCorrelationOutput02.rows.flatten,RHHighZetaCorrelationOutput03.rows.flatten,RHHighZetaCorrelationOutput04.rows.flatten,RHHighZetaCorrelationOutput05.rows.flatten,RHHighZetaCorrelationOutput06.rows.flatten,RHHighZetaCorrelationOutput07.rows.flatten,RHHighZetaCorrelationOutput08.rows.flatten,RHHighZetaCorrelationOutput09.rows.flatten,RHHighZetaCorrelationOutput10.rows.flatten,RHHighZetaCorrelationOutput11.rows.flatten,RHHighZetaCorrelationOutput12.rows.flatten,RHHighZetaCorrelationOutput13.rows.flatten,RHHighZetaCorrelationOutput14.rows.flatten,RHHighZetaCorrelationOutput15.rows.flatten,RHHighZetaCorrelationOutput16.rows.flatten,RHHighZetaCorrelationOutput17.rows.flatten,RHHighZetaCorrelationOutput18.rows.flatten,RHHighZetaCorrelationOutput19.rows.flatten,RHHighZetaCorrelationOutput20.rows.flatten,RHHighZetaCorrelationOutput21.rows.flatten,RHHighZetaCorrelationOutput22.rows.flatten,RHHighZetaCorrelationOutput23.rows.flatten]
noncomputable def add (xs ys : List (Int×Int)) : List (Int×Int) :=
  List.zipWith (fun a b=>(a.1+b.1,a.2+b.2)) xs ys
noncomputable def total : List (Int×Int) := packets.foldl
  (fun acc xs=>add acc (RHHighZetaCorrelation.decode xs)) (List.replicate 1025 (0,0))
noncomputable def rounded : List (Int×Int) := total.zipIdx.map (fun p=>
  (p.1.1/(2:Int)^142,if p.2=0 then 0 else p.1.2/(2:Int)^142))
noncomputable def expected : List (Int×Int) := RHHighPackedFFT.decode RHHighZetaFourierData.rows.flatten
end RHHighZetaCoefficientAssembly
noncomputable def TaoFivePrimes_RHHighZetaCoefficientAssembly : Nat := 24


