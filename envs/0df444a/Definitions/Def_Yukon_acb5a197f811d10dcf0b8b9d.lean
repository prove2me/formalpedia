-- Prove2me | Definitions.Def_Yukon_acb5a197f811d10dcf0b8b9d
-- name    : Yukon_acb5a197f811d10dcf0b8b9d
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T10:19:50.087764+00:00
-- url     : https://prove2.me/theorems/00e6b4f0-b743-47de-8a5e-343f3e7d79f6
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeRectangleRows6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeRectangleRows6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeRectangleRows6814.lean
--
--   yukon-proof-operation:foundation-direct-fd92d68da15a44a60261ebeb9b540bfbf641c297bf71d198f103bf6be39c6441
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZTgyNTJmYWMyNDA0OWZmM2I4ZWM5ODM0MjhkYmM4ZmQwZTg3ZjQ3ZWY1YTdiMDY0NjM5NmIyZmNiMmQwMGVhMCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWZkOTJkNjhkYTE1YTQ0YTYwMjYxZWJlYjliNTQwYmZiZjY0MWMyOTdiZjcxZDE5OGYxMDNiZjZiZTM5YzY0NDEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9hY2I1YTE5N2Y4MTFkMTBkY2YwYjhiOWQiLCJ2IjoyfQ]

import Definitions.Def_Yukon_4a8c90d24b1f86cf5eea4561










































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Soundness of a saved total/weight rectangle's finite row certificate.
The endpoint checks yield the actual dimension inequality at every total
in the band; nothing is inferred from sampled interior points. -/
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open RCN100 RelativeBounded6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 20000

structure Band where
  R : ℕ
  B : ℕ
  T0 : ℕ
  T1 : ℕ
  count : ℕ
  deriving DecidableEq

structure Rectangle where
  lo : ℕ
  hi : ℕ
  alpha : ℕ
  beta : ℕ
  s : ℕ
  L0 : ℕ
  L1 : ℕ
  U : ℕ
  deriving DecidableEq

def tail (b : Band) : ℕ := (b.B+b.R-1)*181255+131071-1
def cutoff (b : Band) (d : Rectangle) : ℕ :=
  d.alpha*181255-d.beta*min (d.hi-131071+1) ((b.B+b.R-1)*181255)
def lowerTotal (b : Band) (d : Rectangle) (T : ℕ) : ℕ :=
  max (T+d.alpha+d.s) (max (cutoff b d/131071+1) (T+(cutoff b d-d.lo)/131071+1))
def total (b : Band) (d : Rectangle) (T : ℕ) : ℕ :=
  if b.T0=b.T1 then d.L0 else ceilBlend b.T0 b.T1 d.L0 d.L1 T

def Shape (b : Band) (d : Rectangle) : Prop :=
  b.T0≤b.T1 ∧ b.R≤d.s ∧ d.s<131071 ∧ 131071≤d.lo ∧ d.lo≤d.hi ∧
  d.hi≤tail b ∧ 0<cutoff b d ∧ d.s≤cutoff b d/131071 ∧
  d.s-b.R≤(cutoff b d-d.lo)/131071 ∧
  lowerTotal b d b.T0≤d.L0 ∧ lowerTotal b d b.T1≤d.L1

def rowGood (b : Band) (d : Rectangle) (mu : ℕ) : Prop :=
  let m := d.alpha-d.beta*(mu-1)
  let a := marginA (cutoff b d) d.lo d.s b.R m mu
  let v := marginB (cutoff b d) d.lo d.s b.R m mu
  let c := marginC (cutoff b d) d.lo d.s b.R m mu
  max 0 (-a)<a*d.L0+v*b.T0+c ∧ max 0 (-a)<a*d.L1+v*b.T1+c

instance shapeDecidable (b : Band) (d : Rectangle) : Decidable (Shape b d) := by
  unfold Shape
  infer_instance
instance rowGoodDecidable (b : Band) (d : Rectangle) (mu : ℕ) : Decidable (rowGood b d mu) := by
  unfold rowGood
  infer_instance

def checkRows (b : Band) (d : Rectangle) : ℕ → Bool
  | 0 => true
  | n+1 => checkRows b d n && decide (rowGood b d n)

theorem checkRows_spec (b : Band) (d : Rectangle) (n : ℕ) (hc : checkRows b d n=true) :
    ∀ mu<n, rowGood b d mu := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [checkRows,Bool.and_eq_true,decide_eq_true_eq] at hc
    intro mu hmu
    rcases Nat.lt_or_eq_of_le (show mu≤n by omega) with h | h
    · exact ih hc.1 mu h
    · simpa only [h] using hc.2

theorem total_lower (b : Band) (d : Rectangle) (T : ℕ) (hshape : Shape b d)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) : lowerTotal b d T≤total b d T := by
  rcases hshape with ⟨h01,_,_,_,_,_,_,_,_,hL0,hL1⟩
  unfold total
  split_ifs with he
  · have ht : T=b.T0 := by omega
    simpa only [ht] using hL0
  · have hstrict : b.T0<b.T1 := by omega
    simp only [lowerTotal,max_le_iff] at hL0 hL1 ⊢
    refine ⟨?_,?_,?_⟩
    · simpa only [Nat.add_assoc] using ceilBlend_affine_lower b.T0 b.T1 d.L0 d.L1 T (d.alpha+d.s)
        hstrict hT0 hT1 (by omega) (by omega)
    · exact ceilBlend_const_lower _ _ _ _ _ _ hstrict hT0 hT1 hL0.2.1 hL1.2.1
    · simpa only [Nat.add_assoc] using ceilBlend_affine_lower b.T0 b.T1 d.L0 d.L1 T
        ((cutoff b d-d.lo)/131071+1) hstrict hT0 hT1 (by omega) (by omega)

theorem total_upper (b : Band) (d : Rectangle) (T : ℕ) (hshape : Shape b d)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) : total b d T≤max d.L0 d.L1 := by
  unfold total
  split_ifs with he
  · exact le_max_left _ _
  · exact ceilBlend_upper _ _ _ _ _ (by have := hshape.1; omega) hT0 hT1

theorem margin_positive (b : Band) (d : Rectangle) (T mu : ℕ) (hshape : Shape b d)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hgood : rowGood b d mu) :
    0<marginA (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu*total b d T+
      marginB (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu*T+
      marginC (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu := by
  unfold rowGood at hgood
  unfold total
  split_ifs with he
  · have ht : T=b.T0 := by omega
    rw [ht]
    exact lt_of_le_of_lt (le_max_left _ _) hgood.1
  · have hstrict : b.T0<b.T1 := by have := hshape.1; omega
    let p := b.T1-T
    let q := T-b.T0
    have hsum : p+q=b.T1-b.T0 := by dsimp [p,q]; omega
    have ht : (p+q)*T=p*b.T0+q*b.T1 := by
      rw [hsum]
      exact total_blend_identity _ _ _ hT0 hT1
    have hb := ceilBlend_bounds b.T0 b.T1 d.L0 d.L1 T hstrict hT0 hT1
    apply rounded_affine_positive (p : ℤ) (q : ℤ) d.L0 d.L1 b.T0 b.T1
      (ceilBlend b.T0 b.T1 d.L0 d.L1 T) T _ _ _
      (by exact_mod_cast Nat.zero_le p) (by exact_mod_cast Nat.zero_le q)
      (by exact_mod_cast (show 0<p+q by omega)) (by exact_mod_cast ht) ?_ ?_ hgood.1 hgood.2
    · exact_mod_cast (show p*d.L0+q*d.L1≤(p+q)*ceilBlend b.T0 b.T1 d.L0 d.L1 T by simpa only [hsum] using hb.1)
    · exact_mod_cast (show (p+q)*ceilBlend b.T0 b.T1 d.L0 d.L1 T≤p*d.L0+q*d.L1+(p+q) by simpa only [hsum] using hb.2.le)

theorem rectangle_rows (b : Band) (d : Rectangle) (T : ℕ) (hshape : Shape b d)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hcheck : checkRows b d (b.B+b.R+1)=true) :
    ∀ mu≤b.B+b.R, coefficientCount (cutoff b d-d.lo) 131071 (total b d T-T) (d.s-b.R)+
      262144*profileRowRank d.alpha d.beta (total b d T) d.s T b.R mu <
        coefficientCount (cutoff b d) 131071 (total b d T) d.s := by
  intro mu hmu
  have hmargin := margin_positive b d T mu hshape hT0 hT1 (checkRows_spec _ _ _ hcheck mu (by omega))
  have hl := total_lower b d T hshape hT0 hT1
  rcases hshape with ⟨_,hR,hs,hlo,_,_,hD,hsq,hsq',_,_⟩
  simp only [lowerTotal,max_le_iff] at hl
  exact row_test_of_margin _ _ _ _ _ _ _ _ hD (by omega) hs hR (by omega)
    hsq hsq' hl.2.1 (by omega) (by omega) (by omega) hmargin



end
end ProximityPrize.SubmissionLower.RelativeCertificate6814


