-- Prove2me | Definitions.Def_Yukon_e757298719adf05c20287f89
-- name    : Yukon_e757298719adf05c20287f89
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T11:11:12.112581+00:00
-- url     : https://prove2.me/theorems/3d56c54f-37b8-400e-aa9c-98afc1aace79
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeFastRecordCover6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeFastRecordCover6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeFastRecordCover6814.lean
--
--   yukon-proof-operation:foundation-direct-2e2bc721d8b35f837501fb5264e0065557fd35e305496763e30440c345a206a9
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYWQ5MWJlMTBjNTRlMTY0OWJkYjZhZjE3MGQ4ZDM0NjQ0MjQ3MmZlNDM5ODBjZGU1M2E3NWQ4OGEzMjczYjdlMCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTJlMmJjNzIxZDhiMzVmODM3NTAxZmI1MjY0ZTAwNjU1NTdmZDM1ZTMwNTQ5Njc2M2UzMDQ0MGMzNDVhMjA2YTkiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9lNzU3Mjk4NzE5YWRmMDVjMjAyODdmODkiLCJ2IjoyfQ]

import Definitions.Def_Yukon_9fa208960027472611de2bc4













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! A small cubic certificate plus explicitly checked exceptional contacts
implies the original full row checker. The count theorem is unchanged. -/
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 25000

structure FastWitness where
  normalEnd : ℕ
  firstExact : ℕ
  lastExact : ℕ

def checkRange (b : Band) (d : Rectangle) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => checkRange b d start n && decide (rowGood b d (start+n))

theorem checkRange_spec (b : Band) (d : Rectangle) (start n : ℕ)
    (hc : checkRange b d start n=true) (mu : ℕ) (h0 : start≤mu) (h1 : mu<start+n) : rowGood b d mu := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [checkRange,Bool.and_eq_true,decide_eq_true_eq] at hc
    by_cases hmu : mu<start+n
    · exact ih hc.1 hmu
    · have he : mu=start+n := by omega
      simpa only [he] using hc.2

def corners (b : Band) (d : Rectangle) (a z : ℕ) : Prop :=
  (marginPolynomial b d b.T0 d.L0).Check a z ∧
  (marginPolynomial b d b.T0 (d.L0+1)).Check a z ∧
  (marginPolynomial b d b.T1 d.L1).Check a z ∧
  (marginPolynomial b d b.T1 (d.L1+1)).Check a z

instance cornersDecidable (b : Band) (d : Rectangle) (a z : ℕ) : Decidable (corners b d a z) := by
  unfold corners
  infer_instance

theorem rowGood_of_corners (b : Band) (d : Rectangle) (a z mu : ℕ)
    (hR : b.R≤d.s) (hc : corners b d a z) (ha : a≤mu) (hz : mu≤z) (hmu : 1≤mu)
    (hm : mu≤d.alpha-d.beta*(mu-1))
    (hs : 2*d.s≤d.alpha-d.beta*(mu-1))
    (hs' : 2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu) : rowGood b d mu := by
  have h0 := Cubic.check_positive _ _ _ mu hc.1 ha hz
  have h0' := Cubic.check_positive _ _ _ mu hc.2.1 ha hz
  have h1 := Cubic.check_positive _ _ _ mu hc.2.2.1 ha hz
  have h1' := Cubic.check_positive _ _ _ mu hc.2.2.2 ha hz
  rw [marginPolynomial_eval b d b.T0 d.L0 mu hmu hR hm hs hs'] at h0
  rw [marginPolynomial_eval b d b.T0 (d.L0+1) mu hmu hR hm hs hs'] at h0'
  rw [marginPolynomial_eval b d b.T1 d.L1 mu hmu hR hm hs hs'] at h1
  rw [marginPolynomial_eval b d b.T1 (d.L1+1) mu hmu hR hm hs hs'] at h1'
  simp only [Nat.cast_add,Nat.cast_one] at h0' h1'
  unfold rowGood
  constructor
  · exact max_lt h0 (by nlinarith only [h0'])
  · exact max_lt h1 (by nlinarith only [h1'])

def FastRows (b : Band) (d : Rectangle) (w : FastWitness) : Prop :=
  1≤w.firstExact ∧ w.firstExact≤w.lastExact ∧ w.lastExact≤w.normalEnd ∧ w.normalEnd≤b.B+b.R ∧
  w.normalEnd≤d.alpha-d.beta*(w.normalEnd-1) ∧
  2*d.s≤d.alpha-d.beta*(w.normalEnd-1) ∧
  2*(d.s-b.R)≤d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd ∧
  corners b d 1 (w.firstExact-1) ∧ corners b d (w.lastExact+1) w.normalEnd ∧
  rowGood b d 0 ∧ checkRange b d w.firstExact (w.lastExact+1-w.firstExact)=true ∧
  checkRange b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)=true

instance fastRowsDecidable (b : Band) (d : Rectangle) (w : FastWitness) : Decidable (FastRows b d w) := by
  unfold FastRows
  infer_instance

theorem checkRows_of_all (b : Band) (d : Rectangle) (n : ℕ)
    (h : ∀ mu<n, rowGood b d mu) : checkRows b d n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [checkRows,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨ih (fun mu hm => h mu (by omega)),h n (by omega)⟩

theorem fastRows_sound (b : Band) (d : Rectangle) (w : FastWitness)
    (hR : b.R≤d.s) (h : FastRows b d w) : checkRows b d (b.B+b.R+1)=true := by
  rcases h with ⟨hfirst,hlast,hend,hmax,hlevel,hs,hs',hleft,hright,hzero,hcenter,htail⟩
  apply checkRows_of_all
  intro mu hmu
  by_cases hz : mu=0
  · simpa only [hz] using hzero
  have hmu1 : 1≤mu := by omega
  by_cases hn : mu≤w.normalEnd
  · have hmono : d.alpha-d.beta*(w.normalEnd-1)≤d.alpha-d.beta*(mu-1) :=
      Nat.sub_le_sub_left (Nat.mul_le_mul_left d.beta (Nat.sub_le_sub_right hn 1)) d.alpha
    have hm : mu≤d.alpha-d.beta*(mu-1) := by omega
    have hms : 2*d.s≤d.alpha-d.beta*(mu-1) := by omega
    have hms' : 2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu := by omega
    by_cases hbefore : mu<w.firstExact
    · exact rowGood_of_corners b d 1 (w.firstExact-1) mu hR hleft hmu1 (by omega) hmu1 hm hms hms'
    by_cases hwithin : mu≤w.lastExact
    · exact checkRange_spec _ _ _ _ hcenter mu (by omega) (by omega)
    · exact rowGood_of_corners b d (w.lastExact+1) w.normalEnd mu hR hright (by omega) hn hmu1 hm hms hms'
  · exact checkRange_spec _ _ _ _ htail mu (by omega) (by omega)

def Header (b : Band) (d : Rectangle) : Prop :=
  Shape b d ∧ 1≤b.R ∧ b.B<2130706433 ∧ b.R<2130706433 ∧ b.T1<2130706433 ∧
  cutoff b d≤131071*(d.U+1) ∧
  (pair b d).mixedCost.y<2130706433 ∧ (pair b d).mixedCost.r<2130706433 ∧
  (pair b d).mixedCost.z<2130706433 ∧ AsymmetricHelper.leftRegularCountCap (pair b d)≤b.count

def FastValid (b : Band) (dw : Rectangle × FastWitness) : Prop := Header b dw.1 ∧ FastRows b dw.1 dw.2

instance fastValidDecidable (b : Band) (dw : Rectangle × FastWitness) : Decidable (FastValid b dw) := by
  unfold FastValid Header
  infer_instance

theorem fastValid_sound (b : Band) (dw : Rectangle × FastWitness) (h : FastValid b dw) : Valid b dw.1 := by
  rcases h with ⟨⟨hs,hR,hB,hRc,hTc,hU,hgY,hgR,hgZ,hprice⟩,hf⟩
  exact ⟨hs,hR,hB,hRc,hTc,hU,hgY,hgR,hgZ,hprice,fastRows_sound b dw.1 dw.2 hs.2.1 hf⟩

def fastCheckList (b : Band) : List (Rectangle × FastWitness) → Bool
  | [] => true
  | d::ds => decide (FastValid b d) && fastCheckList b ds

theorem fastCheckList_append (b : Band) (xs ys : List (Rectangle × FastWitness)) :
    fastCheckList b (xs++ys)=(fastCheckList b xs && fastCheckList b ys) := by
  induction xs with
  | nil => simp [fastCheckList]
  | cons x xs ih => simp only [List.cons_append,fastCheckList,ih,Bool.and_assoc]

theorem fastCheckList_sound (b : Band) (xs : List (Rectangle × FastWitness))
    (hc : fastCheckList b xs=true) : checkList b (xs.map Prod.fst)=true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [fastCheckList,Bool.and_eq_true,decide_eq_true_eq] at hc
    simp only [List.map_cons,checkList,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨fastValid_sound b x hc.1,ih hc.2⟩



end
end ProximityPrize.SubmissionLower.RelativeCertificate6814


