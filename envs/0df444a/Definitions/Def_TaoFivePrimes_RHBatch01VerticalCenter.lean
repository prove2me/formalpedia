-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenter
-- name    : TaoFivePrimes_RHBatch01VerticalCenter
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T19:01:09.128282+00:00
-- url     : https://prove2.me/theorems/948834c1-bc60-4163-8181-786fbbe7d1f7
-- title:
--   Bounded center Taylor algorithm for both vertical contour edges
-- statement:
--   Transparent rational program:55 center Taylor coefficients,32-frequency packet contributions, stable48-term Horner evaluation at rational offsets in[-1,1]. Only algorithms; no analytic approximation, sign, winding, count or RH assertion.
-- source:
--   Platt Fourier polynomial DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01ContourCoefficient
set_option autoImplicit false
namespace RHBatch01VerticalCenter
open RHBatch01ContourCoefficientData
noncomputable def input (w : Nat) (positive : Bool) : Int×Int :=
 let p:=decode w
 (p.1*2^48,(if positive then p.2 else -p.2)*2^48)
noncomputable def seed (t : Fin 3) (positive : Bool) (r : RHBatch01ContourReference.Record) (w : Nat) : Int×Int :=
 mul (input w positive) (RHHighContourUnit.pair (rootIndex t positive r.m))
noncomputable def frequency (r : RHBatch01ContourReference.Record) (positive : Bool) : Int×Int :=
 (if positive then -((r.x:Int)*16) else (r.x:Int)*16,0)
noncomputable def terms (n next : Nat) (p f : Int×Int) : List (Int×Int) :=
 match n with
 | 0 => []
 | n+1 => p::terms n (next+1) (divide (mul p f) next) f
noncomputable def add (xs ys : List (Int×Int)) : List (Int×Int) :=
 List.zipWith (fun a b=>(a.1+b.1,a.2+b.2)) xs ys
noncomputable def inputs : List (RHBatch01ContourReference.Record×Nat) :=
 RHBatch01ContourReference.records.zip (RHBatch01ZetaFourierData.rows.flatten.drop 1)
noncomputable def recordTerms (t : Fin 3) (r : RHBatch01ContourReference.Record) (w : Nat) : List (Int×Int) :=
 add (terms 55 1 (seed t true r w) (frequency r true))
     (terms 55 1 (seed t false r w) (frequency r false))
noncomputable def packet (t : Fin 3) (b : Nat) : List (Int×Int) :=
 ((inputs.drop (32*b)).take 32).foldl (fun acc p=>add acc (recordTerms t p.1 p.2))
  (List.replicate 55 (0,0))
noncomputable def weight (c : Int×Int) (k n : Nat) : Int×Int :=
 (c.1*(Nat.choose (k+n) k:Int)/(64:Int)^k,c.2*(Nat.choose (k+n) k:Int)/(64:Int)^k)
noncomputable def horner (cs : List (Int×Int)) (x : Int) : Int×Int :=
 cs.foldr (fun a h=>(a.1+h.1*x/64,a.2+h.2*x/64)) (0,0)
noncomputable def evaluate (cs : List (Int×Int)) (j k : Nat) : Int×Int :=
 horner ((List.range 48).map (fun n=>weight ((cs[k+n]?).getD (0,0)) k n)) ((j:Int)-64)
end RHBatch01VerticalCenter
noncomputable def TaoFivePrimes_RHBatch01VerticalCenter : Nat := 55


