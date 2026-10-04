-- Prove2me | Definitions.Def_Yukon_3b4f372e3837cd1dfa5952a8
-- name    : Yukon_3b4f372e3837cd1dfa5952a8
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T01:52:44.180589+00:00
-- url     : https://prove2.me/theorems/e9231696-4cfd-43c4-8aff-d2085dd8300a
-- title:
--   Relative certificate source part 6/6
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B56T3579To3720Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B56T3579To3720Fast.lean
--
--   yukon-proof-operation:certificate-b56-ace1bf3e1da5c77b0dc39a0d6c3c9d8c038cbb5a73e731be63ead21ae7c80b1a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZDMyMTZjZDliNjUwZmRiNmM4NTdhZGQ1MzdhZTY5MTQ3NGUwMDFkNDRmMjljODc4MDYzY2JkZTcxNGZhYWJlOSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni1hY2UxYmYzZTFkYTVjNzdiMGRjMzlhMGQ2YzNjOWQ4YzAzOGNiYjVhNzNlNzMxYmU2M2VhZDIxYWU3YzgwYjFhIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fM2I0ZjM3MmUzODM3Y2QxZGZhNTk1MmE4IiwidiI6Mn0]

import Definitions.Def_Yukon_5d0797dafa92de1f4d3d3165
import Definitions.Def_Yukon_59d15dffbe1d30b023fa92f7
import Definitions.Def_Yukon_8004ff7cd4208865a812356b
import Definitions.Def_Yukon_df96a6af7fa1e83b4131180f
import Definitions.Def_Yukon_e757298719adf05c20287f89

import Definitions.Def_Yukon_dd35002c4104ec31e41819fa











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: 07832c8515ee45a9cd576a8e6dc88890fd3e7c99ee877e80bf6d1362ebaf25e9.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def witnessedRows : List (Rectangle × FastWitness) := b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19++b20++b21++b22++b23++b24++b25++b26++b27++b28++b29++b30++b31++b32++b33++b34++b35++b36++b37++b38++b39++b40++b41++b42++b43++b44++b45++b46++b47++b48++b49++b50++b51++b52++b53++b54++b55++b56++b57++b58++b59++b60++b61++b62++b63++b64++b65++b66++b67++b68++b69++b70++b71++b72++b73++b74++b75++b76++b77++b78++b79++b80++b81++b82++b83++b84++b85++b86++b87++b88++b89++b90++b91++b92++b93++b94++b95++b96++b97++b98++b99++b100++b101++b102++b103++b104++b105++b106++b107++b108++b109++b110++b111++b112++b113++b114++b115++b116++b117++b118++b119++b120++b121++b122++b123++b124++b125++b126++b127++b128++b129++b130++b131++b132++b133++b134++b135++b136++b137
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
  have joined60 := joinChecked _ _ joined59 checked60
  have joined61 := joinChecked _ _ joined60 checked61
  have joined62 := joinChecked _ _ joined61 checked62
  have joined63 := joinChecked _ _ joined62 checked63
  have joined64 := joinChecked _ _ joined63 checked64
  have joined65 := joinChecked _ _ joined64 checked65
  have joined66 := joinChecked _ _ joined65 checked66
  have joined67 := joinChecked _ _ joined66 checked67
  have joined68 := joinChecked _ _ joined67 checked68
  have joined69 := joinChecked _ _ joined68 checked69
  have joined70 := joinChecked _ _ joined69 checked70
  have joined71 := joinChecked _ _ joined70 checked71
  have joined72 := joinChecked _ _ joined71 checked72
  have joined73 := joinChecked _ _ joined72 checked73
  have joined74 := joinChecked _ _ joined73 checked74
  have joined75 := joinChecked _ _ joined74 checked75
  have joined76 := joinChecked _ _ joined75 checked76
  have joined77 := joinChecked _ _ joined76 checked77
  have joined78 := joinChecked _ _ joined77 checked78
  have joined79 := joinChecked _ _ joined78 checked79
  have joined80 := joinChecked _ _ joined79 checked80
  have joined81 := joinChecked _ _ joined80 checked81
  have joined82 := joinChecked _ _ joined81 checked82
  have joined83 := joinChecked _ _ joined82 checked83
  have joined84 := joinChecked _ _ joined83 checked84
  have joined85 := joinChecked _ _ joined84 checked85
  have joined86 := joinChecked _ _ joined85 checked86
  have joined87 := joinChecked _ _ joined86 checked87
  have joined88 := joinChecked _ _ joined87 checked88
  have joined89 := joinChecked _ _ joined88 checked89
  have joined90 := joinChecked _ _ joined89 checked90
  have joined91 := joinChecked _ _ joined90 checked91
  have joined92 := joinChecked _ _ joined91 checked92
  have joined93 := joinChecked _ _ joined92 checked93
  have joined94 := joinChecked _ _ joined93 checked94
  have joined95 := joinChecked _ _ joined94 checked95
  have joined96 := joinChecked _ _ joined95 checked96
  have joined97 := joinChecked _ _ joined96 checked97
  have joined98 := joinChecked _ _ joined97 checked98
  have joined99 := joinChecked _ _ joined98 checked99
  have joined100 := joinChecked _ _ joined99 checked100
  have joined101 := joinChecked _ _ joined100 checked101
  have joined102 := joinChecked _ _ joined101 checked102
  have joined103 := joinChecked _ _ joined102 checked103
  have joined104 := joinChecked _ _ joined103 checked104
  have joined105 := joinChecked _ _ joined104 checked105
  have joined106 := joinChecked _ _ joined105 checked106
  have joined107 := joinChecked _ _ joined106 checked107
  have joined108 := joinChecked _ _ joined107 checked108
  have joined109 := joinChecked _ _ joined108 checked109
  have joined110 := joinChecked _ _ joined109 checked110
  have joined111 := joinChecked _ _ joined110 checked111
  have joined112 := joinChecked _ _ joined111 checked112
  have joined113 := joinChecked _ _ joined112 checked113
  have joined114 := joinChecked _ _ joined113 checked114
  have joined115 := joinChecked _ _ joined114 checked115
  have joined116 := joinChecked _ _ joined115 checked116
  have joined117 := joinChecked _ _ joined116 checked117
  have joined118 := joinChecked _ _ joined117 checked118
  have joined119 := joinChecked _ _ joined118 checked119
  have joined120 := joinChecked _ _ joined119 checked120
  have joined121 := joinChecked _ _ joined120 checked121
  have joined122 := joinChecked _ _ joined121 checked122
  have joined123 := joinChecked _ _ joined122 checked123
  have joined124 := joinChecked _ _ joined123 checked124
  have joined125 := joinChecked _ _ joined124 checked125
  have joined126 := joinChecked _ _ joined125 checked126
  have joined127 := joinChecked _ _ joined126 checked127
  have joined128 := joinChecked _ _ joined127 checked128
  have joined129 := joinChecked _ _ joined128 checked129
  have joined130 := joinChecked _ _ joined129 checked130
  have joined131 := joinChecked _ _ joined130 checked131
  have joined132 := joinChecked _ _ joined131 checked132
  have joined133 := joinChecked _ _ joined132 checked133
  have joined134 := joinChecked _ _ joined133 checked134
  have joined135 := joinChecked _ _ joined134 checked135
  have joined136 := joinChecked _ _ joined135 checked136
  have joined137 := joinChecked _ _ joined136 checked137
  exact joined137
theorem all_checked : checkList band rows=true := fastCheckList_sound band witnessedRows all_fast_checked
theorem tiled : covers (minimumWeight band) (tail band) rows=true := by decide +kernel
theorem verified : VerifiedCover band rows :=
  ⟨all_checked,tiled,by decide +kernel⟩

open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance  _root_.ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 12)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 12≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤56)
    (hT0 : 3579≤T) (hT1 : T≤3720) (hnu : 7339964≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181255≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80889) :
    (RCN140.regularSeeds H selected Gamma F).card≤45323634816865846 :=
  regular_count_of_cover K I band rows verified F hbox hcode htotal hslope hB hT0 hT1 hnu
    nodes u0 u1 hcard selected Gamma hdegree hagreement hno



end
end ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast


