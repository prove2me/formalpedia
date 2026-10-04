-- Prove2me | Definitions.Def_Yukon_751a18f29ce94f2197de2915
-- name    : Yukon_751a18f29ce94f2197de2915
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T23:52:02.652639+00:00
-- url     : https://prove2.me/theorems/1b1698b9-e46e-4e15-ab1c-a09bf30fca98
-- title:
--   Relative certificate source part 3/3
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B52T3680To3840Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B52T3680To3840Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B52T3680To3840Fast.lean
--
--   yukon-proof-operation:certificate-b52-tail-module-Yukon_751a18f29ce94f2197de2915
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNGI1NDdiOThkNDlhNTE1YTlkYzkyYzBmMGY4OGY2YzA5YTlkOWM3NTYzZDk4Nzk4ZTMwNzQzOWI0ZThjMDhlYSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Mi10YWlsLW1vZHVsZS1ZdWtvbl83NTFhMThmMjljZTk0ZjIxOTdkZTI5MTUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83NTFhMThmMjljZTk0ZjIxOTdkZTI5MTUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_cc1c7b1db99a28de5ef11982
import Definitions.Def_Yukon_de091d30b1349f12d747d334
import Definitions.Def_Yukon_3610560a362096f5bd3bc086
import Definitions.Def_Yukon_e757298719adf05c20287f89

import Definitions.Def_Yukon_4e6a4328ff3b4945ae675da9











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: 641479a808f9c4405d3bda86b9d2a699e3fb8a5d22a965a26786df9004fc102a.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR12B52T3680To3840Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def witnessedRows : List (Rectangle × FastWitness) := b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19++b20++b21++b22++b23++b24++b25++b26++b27++b28++b29++b30++b31++b32++b33++b34++b35++b36++b37++b38++b39++b40++b41++b42++b43++b44++b45++b46++b47++b48++b49++b50++b51++b52++b53++b54++b55++b56++b57++b58++b59
def rows : List Rectangle := witnessedRows.map Prod.fst
theorem all_fast_checked : fastCheckList band witnessedRows=true := by
  have joinChecked (xs ys : List (Rectangle × FastWitness)) (hx : fastCheckList band xs = true) (hy : fastCheckList band ys = true) : fastCheckList band (xs ++ ys) = true := by
    rw [fastCheckList_append, hx, hy]
    rfl
  have joined1 := joinChecked _ _ checked0 checked1
  have joined2 := joinChecked _ _ joined1 checked2
  have joined3 := joinChecked _ _ joined2 checked3
  have joined4 := joinChecked _ _ joined3 checked4
  have joined5 := joinChecked _ _ joined4 checked5
  have joined6 := joinChecked _ _ joined5 checked6
  have joined7 := joinChecked _ _ joined6 checked7
  have joined8 := joinChecked _ _ joined7 checked8
  have joined9 := joinChecked _ _ joined8 checked9
  have joined10 := joinChecked _ _ joined9 checked10
  have joined11 := joinChecked _ _ joined10 checked11
  have joined12 := joinChecked _ _ joined11 checked12
  have joined13 := joinChecked _ _ joined12 checked13
  have joined14 := joinChecked _ _ joined13 checked14
  have joined15 := joinChecked _ _ joined14 checked15
  have joined16 := joinChecked _ _ joined15 checked16
  have joined17 := joinChecked _ _ joined16 checked17
  have joined18 := joinChecked _ _ joined17 checked18
  have joined19 := joinChecked _ _ joined18 checked19
  have joined20 := joinChecked _ _ joined19 checked20
  have joined21 := joinChecked _ _ joined20 checked21
  have joined22 := joinChecked _ _ joined21 checked22
  have joined23 := joinChecked _ _ joined22 checked23
  have joined24 := joinChecked _ _ joined23 checked24
  have joined25 := joinChecked _ _ joined24 checked25
  have joined26 := joinChecked _ _ joined25 checked26
  have joined27 := joinChecked _ _ joined26 checked27
  have joined28 := joinChecked _ _ joined27 checked28
  have joined29 := joinChecked _ _ joined28 checked29
  have joined30 := joinChecked _ _ joined29 checked30
  have joined31 := joinChecked _ _ joined30 checked31
  have joined32 := joinChecked _ _ joined31 checked32
  have joined33 := joinChecked _ _ joined32 checked33
  have joined34 := joinChecked _ _ joined33 checked34
  have joined35 := joinChecked _ _ joined34 checked35
  have joined36 := joinChecked _ _ joined35 checked36
  have joined37 := joinChecked _ _ joined36 checked37
  have joined38 := joinChecked _ _ joined37 checked38
  have joined39 := joinChecked _ _ joined38 checked39
  have joined40 := joinChecked _ _ joined39 checked40
  have joined41 := joinChecked _ _ joined40 checked41
  have joined42 := joinChecked _ _ joined41 checked42
  have joined43 := joinChecked _ _ joined42 checked43
  have joined44 := joinChecked _ _ joined43 checked44
  have joined45 := joinChecked _ _ joined44 checked45
  have joined46 := joinChecked _ _ joined45 checked46
  have joined47 := joinChecked _ _ joined46 checked47
  have joined48 := joinChecked _ _ joined47 checked48
  have joined49 := joinChecked _ _ joined48 checked49
  have joined50 := joinChecked _ _ joined49 checked50
  have joined51 := joinChecked _ _ joined50 checked51
  have joined52 := joinChecked _ _ joined51 checked52
  have joined53 := joinChecked _ _ joined52 checked53
  have joined54 := joinChecked _ _ joined53 checked54
  have joined55 := joinChecked _ _ joined54 checked55
  have joined56 := joinChecked _ _ joined55 checked56
  have joined57 := joinChecked _ _ joined56 checked57
  have joined58 := joinChecked _ _ joined57 checked58
  have joined59 := joinChecked _ _ joined58 checked59
  exact joined59
theorem all_checked : checkList band rows=true := fastCheckList_sound band witnessedRows all_fast_checked
theorem tiled : covers (minimumWeight band) (tail band) rows=true := by decide +kernel
theorem verified : VerifiedCover band rows :=
  ⟨all_checked,tiled,by decide +kernel⟩

open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance  _root_.ProximityPrize.SubmissionLower.RelativeCertR12B52T3680To3840Fast.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 12)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 12≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤52)
    (hT0 : 3680≤T) (hT1 : T≤3840) (hnu : 6815680≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181255≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80889) :
    (RCN140.regularSeeds H selected Gamma F).card≤13454343594378053 :=
  regular_count_of_cover K I band rows verified F hbox hcode htotal hslope hB hT0 hT1 hnu
    nodes u0 u1 hcard selected Gamma hdegree hagreement hno



end
end ProximityPrize.SubmissionLower.RelativeCertR12B52T3680To3840Fast


