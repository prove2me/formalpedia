-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01ContourArithmeticV2
-- name    : TaoFivePrimes_RHBatch01ContourArithmeticV2
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T17:58:19.130884+00:00
-- url     : https://prove2.me/theorems/46fab02e-15d1-4c29-a653-de308098dccb
-- title:
--   Finite contour guards using the corrected512-word vertical table lookup
-- statement:
--   Finite contour guards using the corrected512-word vertical table lookup. Transparent finite data/algorithms and necessary finite guards only. No analytic enclosure, nonvanishing, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01ContourArithmetic
import Definitions.Def_TaoFivePrimes_RHBatch01ContourGridV2
set_option autoImplicit false
namespace RHBatch01ContourArithmeticV2
export RHBatch01ContourArithmetic (normSq difference mul logAux log16 ratio)
noncomputable def check (e j lower : Nat) (upper : List Nat) (r log : Int×Int) : Bool :=
 let c:=RHBatch01ContourGridV2.jet e j 0
 let v:=RHBatch01ContourGridV2.jet e (j+1) 0
 decide (e<4 ∧ j<RHBatch01ContourGridV2.cells e ∧ upper.length=7 ∧ 0<normSq c) &&
 upper.zipIdx.all (fun p=>decide (normSq (RHBatch01ContourGridV2.jet e j (p.2+1))≤p.1^2)) &&
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
end RHBatch01ContourArithmeticV2
noncomputable def TaoFivePrimes_RHBatch01ContourArithmeticV2 : Nat := 16


