-- Prove2me | Definitions.Def_Yukon_fa5bff97534969439522af47
-- name    : Yukon_fa5bff97534969439522af47
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T10:41:57.260222+00:00
-- url     : https://prove2.me/theorems/d80d36a9-8d7f-4c11-9b37-b98ed14b5b7c
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeRecordCover6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeRecordCover6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeRecordCover6814.lean
--
--   yukon-proof-operation:foundation-direct-01298948e0a0d63a8515005d18581785cf69cb3a268528caa9f4f99d6287be66
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMGRkYmEzNDJlYTM4M2JmYjA4Y2I2NWQ3YjczN2EyZGQxZjE2MjY3Y2FlOThjMTNkNDBiZjE2NzUwM2UyNGZkYSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTAxMjk4OTQ4ZTBhMGQ2M2E4NTE1MDA1ZDE4NTgxNzg1Y2Y2OWNiM2EyNjg1MjhjYWE5ZjRmOTlkNjI4N2JlNjYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9mYTViZmY5NzUzNDk2OTQzOTUyMmFmNDciLCJ2IjoyfQ]

import Definitions.Def_Yukon_964429eea3e1d9a3c2850a3a










































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Checked interval tiling supplies a real count for the whole saved
band, including arbitrarily large factor code weight after saturation. -/
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def minimumWeight (b : Band) : ℕ := 131071*b.B-b.R
def checkList (b : Band) : List Rectangle → Bool
  | [] => true
  | d::ds => decide (Valid b d) && checkList b ds




theorem checkList_spec (b : Band) (xs : List Rectangle) (hc : checkList b xs=true) :
    ∀ d∈xs, Valid b d := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [checkList,Bool.and_eq_true,decide_eq_true_eq] at hc
    intro d hd
    rcases List.mem_cons.mp hd with he | he
    · simpa only [he] using hc.1
    · exact ih hc.2 d he

def covers (start stop : ℕ) : List Rectangle → Bool
  | [] => decide (stop+1=start)
  | d::ds => decide (d.lo=start ∧ d.lo≤d.hi) && covers (d.hi+1) stop ds

theorem covers_spec (xs : List Rectangle) (start stop : ℕ) (hc : covers start stop xs=true)
    (nu : ℕ) (hlo : start≤nu) (hhi : nu≤stop) :
    ∃ d∈xs, d.lo≤nu ∧ nu≤d.hi := by
  induction xs generalizing start with
  | nil => simp only [covers,decide_eq_true_eq] at hc; omega
  | cons d ds ih =>
    simp only [covers,Bool.and_eq_true,decide_eq_true_eq] at hc
    by_cases hn : nu≤d.hi
    · exact ⟨d,by simp,by omega,hn⟩
    · obtain ⟨e,he,hl,hh⟩ := ih (d.hi+1) hc.2 (by omega)
      exact ⟨e,List.mem_cons_of_mem _ he,hl,hh⟩

def VerifiedCover (b : Band) (xs : List Rectangle) : Prop :=
  checkList b xs=true ∧ covers (minimumWeight b) (tail b) xs=true ∧ minimumWeight b≤tail b

variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance  _root_.ProximityPrize.SubmissionLower.RelativeCertificate6814.instDecidableEq_proximityPrize_1 : DecidableEq K := Classical.decEq K

theorem regular_count_of_cover (b : Band) (xs : List Rectangle) (hc : VerifiedCover b xs)
    {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T b.R)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : b.R≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤b.B)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hnu : minimumWeight b≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181255≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80889) :
    (RCN140.regularSeeds H selected Gamma F).card≤b.count := by
  obtain ⟨d,hd,hlo,hhi⟩ := covers_spec xs (minimumWeight b) (tail b) hc.2.1
    (min nu (tail b)) (le_min hnu hc.2.2) (min_le_right _ _)
  exact regular_count_of_rectangle K I b d (checkList_spec b xs hc.1 d hd) F hbox hcode
    htotal hslope hB hT0 hT1 (hlo.trans (min_le_left _ _)) hhi nodes u0 u1 hcard
    selected Gamma hdegree hagreement hno



end
end ProximityPrize.SubmissionLower.RelativeCertificate6814


