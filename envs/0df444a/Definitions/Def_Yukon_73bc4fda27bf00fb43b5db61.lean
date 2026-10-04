-- Prove2me | Definitions.Def_Yukon_73bc4fda27bf00fb43b5db61
-- name    : Yukon_73bc4fda27bf00fb43b5db61
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T22:19:40.50088+00:00
-- url     : https://prove2.me/theorems/53afb330-b3b7-445f-a954-39f4f3666046
-- title:
--   Relative certificate source part 2/2
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B51T3746To3868Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B51T3746To3868Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B51T3746To3868Fast.lean
--
--   yukon-proof-operation:certificate-r12-split-module-Yukon_73bc4fda27bf00fb43b5db61
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzMyZTY1MjAxN2FhMmZjZGJlMTlmZWY5YmQyZmI5NzM1YTkxYzkxMTQ2YjA3MGNlM2VmZjZhZWNiNjBkODdlNSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMi1zcGxpdC1tb2R1bGUtWXVrb25fNzNiYzRmZGEyN2JmMDBmYjQzYjVkYjYxIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fNzNiYzRmZGEyN2JmMDBmYjQzYjVkYjYxIiwidiI6Mn0]

import Definitions.Def_Yukon_6b36e8b98079a15273a544a3
import Definitions.Def_Yukon_e757298719adf05c20287f89

import Definitions.Def_Yukon_b9898b64429801647a447267











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: b0c234954263df6efac1a905544e4059cbb23b23859e77cf257074b06662288e.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR12B51T3746To3868Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def b24 : List (Rectangle × FastWitness) := [(r192,⟨63,46,46⟩),(r193,⟨63,46,46⟩),(r194,⟨63,46,46⟩),(r195,⟨63,46,46⟩),(r196,⟨63,46,46⟩),(r197,⟨63,46,46⟩),(r198,⟨63,46,46⟩),(r199,⟨63,46,46⟩)]
theorem checked24 : fastCheckList band b24=true := by decide +kernel

def b25 : List (Rectangle × FastWitness) := [(r200,⟨63,46,46⟩),(r201,⟨63,46,46⟩),(r202,⟨63,46,46⟩),(r203,⟨63,46,46⟩),(r204,⟨63,46,46⟩),(r205,⟨63,46,46⟩),(r206,⟨63,46,46⟩),(r207,⟨63,46,46⟩)]
theorem checked25 : fastCheckList band b25=true := by decide +kernel

def b26 : List (Rectangle × FastWitness) := [(r208,⟨63,46,46⟩),(r209,⟨63,46,46⟩),(r210,⟨63,46,46⟩),(r211,⟨63,46,46⟩),(r212,⟨63,46,46⟩),(r213,⟨63,46,46⟩),(r214,⟨63,46,46⟩),(r215,⟨63,46,46⟩)]
theorem checked26 : fastCheckList band b26=true := by decide +kernel

def b27 : List (Rectangle × FastWitness) := [(r216,⟨63,46,46⟩),(r217,⟨63,46,46⟩),(r218,⟨63,46,46⟩),(r219,⟨63,46,46⟩),(r220,⟨63,46,46⟩),(r221,⟨63,46,46⟩),(r222,⟨63,46,46⟩),(r223,⟨63,47,48⟩)]
theorem checked27 : fastCheckList band b27=true := by decide +kernel

def b28 : List (Rectangle × FastWitness) := [(r224,⟨63,47,48⟩),(r225,⟨63,47,48⟩),(r226,⟨63,47,48⟩),(r227,⟨63,47,48⟩),(r228,⟨63,47,48⟩),(r229,⟨63,47,48⟩),(r230,⟨63,47,48⟩),(r231,⟨63,47,48⟩)]
theorem checked28 : fastCheckList band b28=true := by decide +kernel

def b29 : List (Rectangle × FastWitness) := [(r232,⟨63,47,48⟩),(r233,⟨63,47,48⟩),(r234,⟨63,48,48⟩),(r235,⟨63,48,48⟩),(r236,⟨63,48,48⟩),(r237,⟨63,48,48⟩),(r238,⟨63,48,48⟩),(r239,⟨63,48,48⟩)]
theorem checked29 : fastCheckList band b29=true := by decide +kernel

def b30 : List (Rectangle × FastWitness) := [(r240,⟨63,48,48⟩),(r241,⟨63,48,48⟩),(r242,⟨63,48,48⟩),(r243,⟨63,48,48⟩),(r244,⟨63,48,48⟩),(r245,⟨63,48,48⟩),(r246,⟨63,48,48⟩),(r247,⟨63,48,48⟩)]
theorem checked30 : fastCheckList band b30=true := by decide +kernel

def b31 : List (Rectangle × FastWitness) := [(r248,⟨63,48,48⟩),(r249,⟨63,48,48⟩),(r250,⟨63,48,48⟩),(r251,⟨63,48,48⟩),(r252,⟨63,48,48⟩),(r253,⟨63,48,48⟩),(r254,⟨63,48,48⟩),(r255,⟨63,48,48⟩)]
theorem checked31 : fastCheckList band b31=true := by decide +kernel

def b32 : List (Rectangle × FastWitness) := [(r256,⟨63,48,48⟩),(r257,⟨63,48,48⟩),(r258,⟨63,48,48⟩),(r259,⟨63,48,48⟩),(r260,⟨63,48,48⟩),(r261,⟨63,48,48⟩),(r262,⟨63,48,48⟩),(r263,⟨63,48,48⟩)]
theorem checked32 : fastCheckList band b32=true := by decide +kernel

def b33 : List (Rectangle × FastWitness) := [(r264,⟨63,48,48⟩),(r265,⟨63,48,48⟩),(r266,⟨63,48,48⟩),(r267,⟨63,48,48⟩),(r268,⟨63,48,48⟩),(r269,⟨63,48,48⟩),(r270,⟨63,48,49⟩),(r271,⟨63,48,49⟩)]
theorem checked33 : fastCheckList band b33=true := by decide +kernel

def b34 : List (Rectangle × FastWitness) := [(r272,⟨63,48,49⟩),(r273,⟨63,49,49⟩),(r274,⟨63,49,49⟩),(r275,⟨63,49,49⟩),(r276,⟨63,49,49⟩),(r277,⟨63,49,49⟩),(r278,⟨63,49,49⟩),(r279,⟨63,49,49⟩)]
theorem checked34 : fastCheckList band b34=true := by decide +kernel

def b35 : List (Rectangle × FastWitness) := [(r280,⟨63,49,49⟩),(r281,⟨63,49,49⟩),(r282,⟨63,49,49⟩),(r283,⟨63,49,49⟩),(r284,⟨63,49,49⟩),(r285,⟨63,49,49⟩),(r286,⟨63,49,49⟩),(r287,⟨63,49,49⟩)]
theorem checked35 : fastCheckList band b35=true := by decide +kernel

def b36 : List (Rectangle × FastWitness) := [(r288,⟨63,49,49⟩),(r289,⟨63,49,49⟩),(r290,⟨63,49,49⟩),(r291,⟨63,49,49⟩),(r292,⟨63,49,49⟩),(r293,⟨63,49,49⟩),(r294,⟨63,49,49⟩),(r295,⟨63,49,49⟩)]
theorem checked36 : fastCheckList band b36=true := by decide +kernel

def b37 : List (Rectangle × FastWitness) := [(r296,⟨63,49,49⟩),(r297,⟨63,49,49⟩),(r298,⟨63,49,49⟩),(r299,⟨63,51,52⟩),(r300,⟨63,51,51⟩),(r301,⟨63,51,51⟩),(r302,⟨63,51,51⟩),(r303,⟨63,51,51⟩)]
theorem checked37 : fastCheckList band b37=true := by decide +kernel

def b38 : List (Rectangle × FastWitness) := [(r304,⟨63,51,51⟩),(r305,⟨63,51,51⟩),(r306,⟨63,51,51⟩),(r307,⟨63,51,51⟩),(r308,⟨63,51,52⟩),(r309,⟨63,51,52⟩),(r310,⟨63,52,52⟩),(r311,⟨63,52,52⟩)]
theorem checked38 : fastCheckList band b38=true := by decide +kernel

def b39 : List (Rectangle × FastWitness) := [(r312,⟨63,52,52⟩),(r313,⟨63,52,52⟩),(r314,⟨63,52,52⟩),(r315,⟨63,52,52⟩),(r316,⟨63,52,52⟩),(r317,⟨63,52,52⟩),(r318,⟨63,52,52⟩),(r319,⟨63,52,52⟩)]
theorem checked39 : fastCheckList band b39=true := by decide +kernel

def b40 : List (Rectangle × FastWitness) := [(r320,⟨63,52,52⟩),(r321,⟨63,52,52⟩),(r322,⟨63,52,52⟩),(r323,⟨63,52,52⟩),(r324,⟨63,52,52⟩),(r325,⟨63,52,52⟩),(r326,⟨63,52,52⟩),(r327,⟨63,52,52⟩)]
theorem checked40 : fastCheckList band b40=true := by decide +kernel

def b41 : List (Rectangle × FastWitness) := [(r328,⟨63,52,52⟩),(r329,⟨63,52,52⟩),(r330,⟨63,53,53⟩),(r331,⟨63,53,53⟩),(r332,⟨63,53,53⟩),(r333,⟨63,53,53⟩),(r334,⟨63,53,53⟩),(r335,⟨63,53,53⟩)]
theorem checked41 : fastCheckList band b41=true := by decide +kernel

def b42 : List (Rectangle × FastWitness) := [(r336,⟨63,53,53⟩),(r337,⟨63,53,53⟩),(r338,⟨63,53,53⟩),(r339,⟨63,53,53⟩),(r340,⟨63,53,53⟩),(r341,⟨63,53,53⟩),(r342,⟨63,53,53⟩),(r343,⟨63,53,53⟩)]
theorem checked42 : fastCheckList band b42=true := by decide +kernel

def b43 : List (Rectangle × FastWitness) := [(r344,⟨63,53,53⟩),(r345,⟨63,53,53⟩),(r346,⟨63,53,54⟩),(r347,⟨63,54,54⟩),(r348,⟨63,54,54⟩),(r349,⟨63,57,57⟩),(r350,⟨63,57,57⟩),(r351,⟨63,56,57⟩)]
theorem checked43 : fastCheckList band b43=true := by decide +kernel

def b44 : List (Rectangle × FastWitness) := [(r352,⟨63,56,57⟩),(r353,⟨63,56,57⟩),(r354,⟨63,57,57⟩),(r355,⟨63,57,57⟩),(r356,⟨63,57,57⟩),(r357,⟨63,57,57⟩),(r358,⟨63,57,57⟩),(r359,⟨63,57,57⟩)]
theorem checked44 : fastCheckList band b44=true := by decide +kernel

def b45 : List (Rectangle × FastWitness) := [(r360,⟨63,57,57⟩),(r361,⟨63,57,57⟩),(r362,⟨63,57,57⟩),(r363,⟨63,57,57⟩),(r364,⟨63,57,57⟩),(r365,⟨63,57,57⟩),(r366,⟨63,58,58⟩),(r367,⟨63,58,58⟩)]
theorem checked45 : fastCheckList band b45=true := by decide +kernel

def b46 : List (Rectangle × FastWitness) := [(r368,⟨63,58,58⟩),(r369,⟨63,58,58⟩),(r370,⟨63,58,58⟩),(r371,⟨63,58,58⟩),(r372,⟨63,58,58⟩),(r373,⟨63,58,58⟩),(r374,⟨63,58,58⟩),(r375,⟨63,59,59⟩)]
theorem checked46 : fastCheckList band b46=true := by decide +kernel

def b47 : List (Rectangle × FastWitness) := [(r376,⟨63,59,59⟩),(r377,⟨63,59,59⟩),(r378,⟨63,59,59⟩)]
theorem checked47 : fastCheckList band b47=true := by decide +kernel

def witnessedRows : List (Rectangle × FastWitness) := b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19++b20++b21++b22++b23++b24++b25++b26++b27++b28++b29++b30++b31++b32++b33++b34++b35++b36++b37++b38++b39++b40++b41++b42++b43++b44++b45++b46++b47
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
  exact joined47
theorem all_checked : checkList band rows=true := fastCheckList_sound band witnessedRows all_fast_checked
theorem tiled : covers (minimumWeight band) (tail band) rows=true := by decide +kernel
theorem verified : VerifiedCover band rows :=
  ⟨all_checked,tiled,by decide +kernel⟩

open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance  _root_.ProximityPrize.SubmissionLower.RelativeCertR12B51T3746To3868Fast.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 12)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 12≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤51)
    (hT0 : 3746≤T) (hT1 : T≤3868) (hnu : 6684609≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181255≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80889) :
    (RCN140.regularSeeds H selected Gamma F).card≤12456861955597707 :=
  regular_count_of_cover K I band rows verified F hbox hcode htotal hslope hB hT0 hT1 hnu
    nodes u0 u1 hcard selected Gamma hdegree hagreement hno



end
end ProximityPrize.SubmissionLower.RelativeCertR12B51T3746To3868Fast


