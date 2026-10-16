-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01ContourGridV2
-- name    : TaoFivePrimes_RHBatch01ContourGridV2
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T17:53:56.886455+00:00
-- url     : https://prove2.me/theorems/99b60c85-b979-4848-b4e1-7782391d76bf
-- title:
--   Correct geometric lookup for512-word vertical chunks, reusing the existing horizontal jet tables
-- statement:
--   Correct geometric lookup for512-word vertical chunks, reusing the existing horizontal jet tables. Transparent finite data/algorithms and necessary finite guards only. No analytic enclosure, nonvanishing, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01ContourGrid
set_option autoImplicit false
namespace RHBatch01ContourGridV2
noncomputable def vertical (right : Bool) (j k : Nat) : Int×Int :=
 let rs:=if right then RHBatch01VerticalJetsRight.rows else RHBatch01VerticalJetsLeft.rows
 let i:=8*j+k
 RHHighContourVector.decode ((((rs[i/512]?).getD [])[i%512]?).getD 0)
noncomputable def jet (e j k : Nat) : Int×Int :=
 if e=0 ∨ e=2 then RHBatch01ContourGrid.jet e j k else vertical (e=1) j k
noncomputable def cells (e : Nat) : Nat := RHBatch01ContourGrid.cells e
end RHBatch01ContourGridV2
noncomputable def TaoFivePrimes_RHBatch01ContourGridV2 : Nat := 8448


