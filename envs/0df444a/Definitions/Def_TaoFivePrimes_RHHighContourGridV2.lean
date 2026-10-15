-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighContourGridV2
-- name    : TaoFivePrimes_RHHighContourGridV2
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T08:50:53.673046+00:00
-- url     : https://prove2.me/theorems/b6ec2a56-d5ab-4a8f-a0ca-4d79f689db0d
-- title:
--   Correct geometric lookup for512-word vertical chunks, reusing the existing horizontal jet tables
-- statement:
--   Correct geometric lookup for512-word vertical chunks, reusing the existing horizontal jet tables. Transparent finite data/algorithms and necessary finite guards only. No analytic enclosure, nonvanishing, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighContourGrid
set_option autoImplicit false
namespace RHHighContourGridV2
noncomputable def vertical (right : Bool) (j k : Nat) : Int×Int :=
 let rs:=if right then RHHighVerticalJetsRight.rows else RHHighVerticalJetsLeft.rows
 let i:=8*j+k
 RHHighContourVector.decode ((((rs[i/512]?).getD [])[i%512]?).getD 0)
noncomputable def jet (e j k : Nat) : Int×Int :=
 if e=0 ∨ e=2 then RHHighContourGrid.jet e j k else vertical (e=1) j k
noncomputable def cells (e : Nat) : Nat := RHHighContourGrid.cells e
end RHHighContourGridV2
noncomputable def TaoFivePrimes_RHHighContourGridV2 : Nat := 8448


