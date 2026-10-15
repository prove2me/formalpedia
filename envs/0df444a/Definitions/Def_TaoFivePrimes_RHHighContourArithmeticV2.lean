-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighContourArithmeticV2
-- name    : TaoFivePrimes_RHHighContourArithmeticV2
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T08:53:24.835013+00:00
-- url     : https://prove2.me/theorems/9f76650d-af3b-42a1-a790-72441b370f30
-- title:
--   Finite contour guards using the corrected512-word vertical table lookup
-- statement:
--   Finite contour guards using the corrected512-word vertical table lookup. Transparent finite data/algorithms and necessary finite guards only. No analytic enclosure, nonvanishing, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighContourArithmetic
import Definitions.Def_TaoFivePrimes_RHHighContourGridV2
set_option autoImplicit false
namespace RHHighContourArithmeticV2
export RHHighContourArithmetic (normSq difference mul logAux log16 ratio)
noncomputable def check (e j lower : Nat) (upper : List Nat) (r log : Int×Int) : Bool :=
 let c:=RHHighContourGridV2.jet e j 0
 let v:=RHHighContourGridV2.jet e (j+1) 0
 decide (e<4 ∧ j<RHHighContourGridV2.cells e ∧ upper.length=7 ∧ 0<normSq c) &&
 upper.zipIdx.all (fun p=>decide (normSq (RHHighContourGridV2.jet e j (p.2+1))≤p.1^2)) &&
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
end RHHighContourArithmeticV2
noncomputable def TaoFivePrimes_RHHighContourArithmeticV2 : Nat := 16


