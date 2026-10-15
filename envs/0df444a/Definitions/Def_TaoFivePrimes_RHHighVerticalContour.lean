-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighVerticalContour
-- name    : TaoFivePrimes_RHHighVerticalContour
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T06:55:00.491683+00:00
-- url     : https://prove2.me/theorems/a89ea4a1-7ceb-47ea-9158-d4cf6b4f1d58
-- title:
--   Exact rational program for vertical contour Taylor coefficients
-- statement:
--   Transparent integer program that advances rational polynomial seeds in vertical steps ofi/128 and sums normalized Taylor coefficients of orders0..7 in bounded point blocks. The program and its input records make no analytic, sign, winding, zero-count or RH assertion; their output accuracy is proved separately.
-- source:
--   Existing Platt Fourier polynomial construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighContourCoefficient
import Definitions.Def_TaoFivePrimes_RHHighVerticalFactor
set_option autoImplicit false
namespace RHHighVerticalContour
open RHHighContourCoefficientData
noncomputable def add (xs ys : List (Int×Int)) : List (Int×Int) :=
 List.zipWith (fun a b=>(a.1+b.1,a.2+b.2)) xs ys
noncomputable def input (w : Nat) (positive : Bool) : Int×Int :=
 let p:=decode w
 (p.1*2^48,(if positive then p.2 else -p.2)*2^48)
noncomputable def initial (t : Fin 3) (positive : Bool) (r : RHHighContourReference.Record) (w : Nat) : Int×Int :=
 mul (mul (input w positive) (RHHighContourUnit.pair (rootIndex t positive r.m)))
  ((if positive then r.inverse else r.amplitude:Int),0)
noncomputable def factor (r : RHHighVerticalFactor.Record) (positive : Bool) : Int×Int :=
 ((if positive then r.negative else r.positive:Int),0)
noncomputable def frequency (r : RHHighContourReference.Record) (positive : Bool) : Int×Int :=
 (if positive then -((r.x/4:Nat):Int) else ((r.x/4:Nat):Int),0)
noncomputable def iterate (n : Nat) (p f : Int×Int) : Int×Int :=
 match n with
 | 0 => p
 | n+1 => mul (iterate n p f) f
noncomputable def terms (n next : Nat) (p f : Int×Int) : List (Int×Int) :=
 match n with
 | 0 => []
 | n+1 => p::terms n (next+1) (divide (mul p f) next) f
noncomputable def points (n : Nat) (p advance frequency : Int×Int) : List (Int×Int) :=
 match n with
 | 0 => []
 | n+1 => terms 8 1 p frequency++points n (mul p advance) advance frequency
noncomputable def recordBlock (t : Fin 3) (lo count : Nat) (r : RHHighContourReference.Record)
    (f : RHHighVerticalFactor.Record) (w : Nat) : List (Int×Int) :=
 add (points count (iterate lo (initial t true r w) (factor f true)) (factor f true) (frequency r true))
     (points count (iterate lo (initial t false r w) (factor f false)) (factor f false) (frequency r false))
noncomputable def inputs : List (RHHighContourReference.Record×(RHHighVerticalFactor.Record×Nat)) :=
 RHHighContourReference.records.zip (RHHighVerticalFactor.records.zip (RHHighZetaFourierData.rows.flatten.drop 1))
noncomputable def constant : Int×Int :=
 let p:=decode ((RHHighZetaFourierData.rows.flatten[0]?).getD 0)
 (p.1*2^48,p.2*2^48)
noncomputable def block (t : Fin 3) (lo count : Nat) : List (Int×Int) :=
 inputs.foldl (fun acc p=>add acc (recordBlock t lo count p.1 p.2.1 p.2.2))
  ((List.range count).flatMap (fun _=>constant::List.replicate 7 (0,0)))
end RHHighVerticalContour
noncomputable def TaoFivePrimes_RHHighVerticalContour : Nat := 129


