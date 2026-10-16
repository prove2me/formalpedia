-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01ContourArithmetic
-- name    : TaoFivePrimes_RHBatch01ContourArithmetic
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T17:53:59.264781+00:00
-- url     : https://prove2.me/theorems/3fecd19f-75cc-4398-83a3-51d8b3a2b440
-- title:
--   Exact rational contour guard and logarithm algorithm
-- statement:
--   Integer norm-square guards, explicit128-bit endpoint ratio and16-term rounded logarithm algorithm, and a record type whose necessary finite Boolean guards are proved fields. The guards refer to proposed jet data; no analytic enclosure, nonvanishing, winding, zero count or RH assertion is defined or proved.
-- source:
--   Finite Taylor/logarithm certificate arithmetic for the Platt Fourier polynomial DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01ContourGrid
set_option autoImplicit false
namespace RHBatch01ContourArithmetic
noncomputable def normSq (p : Int×Int) : Nat := p.1.natAbs^2+p.2.natAbs^2
noncomputable def difference (a b : Int×Int) : Int×Int := (a.1-b.1,a.2-b.2)
noncomputable def mul (a b : Int×Int) : Int×Int :=
 ((a.1*b.1-a.2*b.2)/(2:Int)^128,(a.1*b.2+a.2*b.1)/(2:Int)^128)
noncomputable def logAux (r : Int×Int) (n next : Nat) (p acc : Int×Int) : Int×Int :=
 match n with
 | 0 => acc
 | n+1 =>
  let p':=mul p r
  let sg:Int:=if next%2=1 then 1 else -1
  logAux r n (next+1) p' (acc.1+sg*(p'.1/(next:Int)),acc.2+sg*(p'.2/(next:Int)))
noncomputable def log16 (r : Int×Int) : Int×Int := logAux r 16 1 (2^128,0) (0,0)
noncomputable def ratio (c v : Int×Int) : Int×Int :=
 let d:=difference v c
 let M:Int:=normSq c
 ((d.1*c.1+d.2*c.2)*(2:Int)^128/M,(d.2*c.1-d.1*c.2)*(2:Int)^128/M)
noncomputable def check (e j lower : Nat) (upper : List Nat) (r log : Int×Int) : Bool :=
 let c:=RHBatch01ContourGrid.jet e j 0
 let v:=RHBatch01ContourGrid.jet e (j+1) 0
 decide (e<4 ∧ j<RHBatch01ContourGrid.cells e ∧ upper.length=7 ∧ 0<normSq c) &&
 upper.zipIdx.all (fun p=>decide (normSq (RHBatch01ContourGrid.jet e j (p.2+1))≤p.1^2)) &&
 decide (lower^2≤normSq c ∧ upper.sum≤lower ∧
  101000008*2^80≤(lower-upper.sum)*10^12 ∧
  4*normSq (difference v c)≤normSq c ∧ r=ratio c v ∧ log=log16 r)
structure Record where
 edge : Nat
 index : Nat
 lower : Nat
 upper : List Nat
 ratio128 : Int×Int
 log128 : Int×Int
 valid : check edge index lower upper ratio128 log128=true
end RHBatch01ContourArithmetic
noncomputable def TaoFivePrimes_RHBatch01ContourArithmetic : Nat := 16


