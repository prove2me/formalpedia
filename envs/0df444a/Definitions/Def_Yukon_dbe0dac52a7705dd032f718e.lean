-- Prove2me | Definitions.Def_Yukon_dbe0dac52a7705dd032f718e
-- name    : Yukon_dbe0dac52a7705dd032f718e
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T09:44:33.729046+00:00
-- url     : https://prove2.me/theorems/b509a0c9-b641-4d5b-88b5-89479c5b3d7d
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeRoundedAffine6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeRoundedAffine6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeRoundedAffine6814.lean
--
--   yukon-proof-operation:foundation-direct-d758b62c8a12bbc9cccc50e9d0f43ee6703fe66b1c99e49e700049c9c3582a7d
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMDhkZTAyMGJjODhkYWY4MmE4Nzk5NGRhMTViNDBlZTkyZmRmNzliYzNjNDhkNWUxNjc5ODM2YmM3YWQ2ODIxMSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWQ3NThiNjJjOGExMmJiYzljY2NjNTBlOWQwZjQzZWU2NzAzZmU2NmIxYzk5ZTQ5ZTcwMDA0OWM5YzM1ODJhN2QiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9kYmUwZGFjNTJhNzcwNWRkMDMyZjcxOGUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_f60f8771f49612b2e4c0149e







































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The saved certificates interpolate helper totals and round upward.
This lemma pays exactly their one-column reserve, for either sign of
the dimension-margin slope. -/
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem rounded_affine_positive
    (p q L0 L1 T0 T1 L T a b c : ℤ)
    (hp : 0≤p) (hq : 0≤q) (hn : 0<p+q)
    (hT : (p+q)*T=p*T0+q*T1)
    (hlo : p*L0+q*L1≤(p+q)*L)
    (hhi : (p+q)*L≤p*L0+q*L1+(p+q))
    (h0 : max 0 (-a)<a*L0+b*T0+c)
    (h1 : max 0 (-a)<a*L1+b*T1+c) :
    0<a*L+b*T+c := by
  let e := (p+q)*L-(p*L0+q*L1)
  let d := max 0 (-a)
  have he0 : 0≤e := by dsimp [e]; omega
  have he1 : e≤p+q := by dsimp [e]; omega
  have h0' : d+1≤a*L0+b*T0+c := by dsimp [d]; omega
  have h1' : d+1≤a*L1+b*T1+c := by dsimp [d]; omega
  have hsum := add_le_add (mul_le_mul_of_nonneg_left h0' hp) (mul_le_mul_of_nonneg_left h1' hq)
  have hround : -(p+q)*d≤a*e := by
    by_cases ha : 0≤a
    · have hd : d=0 := by dsimp [d]; omega
      rw [hd,mul_zero]
      exact mul_nonneg ha he0
    · have hd : d= -a := by dsimp [d]; omega
      have hh := mul_le_mul_of_nonpos_left he1 (show a≤0 by omega)
      rw [hd]
      nlinarith only [hh]
  have hidentity : (p+q)*(a*L+b*T+c)=
      p*(a*L0+b*T0+c)+q*(a*L1+b*T1+c)+a*e := by
    dsimp [e]
    have hh := congrArg (fun x : ℤ => b*x) hT
    nlinarith only [hh]
  have hpositive : 0<(p+q)*(a*L+b*T+c) := by
    nlinarith only [hsum,hround,hidentity,hn]
  exact pos_of_mul_pos_right hpositive (le_of_lt hn)

def ceilBlend (T0 T1 L0 L1 T : ℕ) : ℕ :=
  ((T1-T)*L0+(T-T0)*L1+(T1-T0)-1)/(T1-T0)

theorem ceilBlend_bounds (T0 T1 L0 L1 T : ℕ)
    (h01 : T0<T1) (h0 : T0≤T) (h1 : T≤T1) :
    (T1-T)*L0+(T-T0)*L1≤(T1-T0)*ceilBlend T0 T1 L0 L1 T ∧
    (T1-T0)*ceilBlend T0 T1 L0 L1 T <
      (T1-T)*L0+(T-T0)*L1+(T1-T0) := by
  have hn : 0<T1-T0 := by omega
  have hq := Nat.div_add_mod ((T1-T)*L0+(T-T0)*L1+(T1-T0)-1) (T1-T0)
  have hm := Nat.mod_lt ((T1-T)*L0+(T-T0)*L1+(T1-T0)-1) hn
  unfold ceilBlend
  omega

theorem total_blend_identity (T0 T1 T : ℕ) (h0 : T0≤T) (h1 : T≤T1) :
    (T1-T0)*T=(T1-T)*T0+(T-T0)*T1 := by
  have h01 : T0≤T1 := by omega
  have ha := Nat.sub_add_cancel h0
  have hb := Nat.sub_add_cancel h1
  have hc := Nat.sub_add_cancel h01
  nlinarith

theorem ceilBlend_affine_lower (T0 T1 L0 L1 T k : ℕ)
    (h01 : T0<T1) (h0 : T0≤T) (h1 : T≤T1)
    (hL0 : T0+k≤L0) (hL1 : T1+k≤L1) :
    T+k≤ceilBlend T0 T1 L0 L1 T := by
  have hn : 0<T1-T0 := by omega
  have hsum : (T1-T)+(T-T0)=T1-T0 := by omega
  have hT := total_blend_identity T0 T1 T h0 h1
  have hL := (ceilBlend_bounds T0 T1 L0 L1 T h01 h0 h1).1
  have hscale := Nat.add_le_add (Nat.mul_le_mul_left (T1-T) hL0) (Nat.mul_le_mul_left (T-T0) hL1)
  have hk := congrArg (fun n : ℕ => n*k) hsum
  have hp : (T1-T0)*(T+k)≤(T1-T0)*ceilBlend T0 T1 L0 L1 T := by
    nlinarith only [hT,hL,hscale,hk]
  exact Nat.le_of_mul_le_mul_left hp hn

theorem ceilBlend_const_lower (T0 T1 L0 L1 T k : ℕ)
    (h01 : T0<T1) (h0 : T0≤T) (h1 : T≤T1) (hL0 : k≤L0) (hL1 : k≤L1) :
    k≤ceilBlend T0 T1 L0 L1 T := by
  have hn : 0<T1-T0 := by omega
  have hsum : (T1-T)+(T-T0)=T1-T0 := by omega
  have hL := (ceilBlend_bounds T0 T1 L0 L1 T h01 h0 h1).1
  have hscale := Nat.add_le_add (Nat.mul_le_mul_left (T1-T) hL0) (Nat.mul_le_mul_left (T-T0) hL1)
  have hp : (T1-T0)*k≤(T1-T0)*ceilBlend T0 T1 L0 L1 T := by
    nlinarith only [hL,hscale,congrArg (fun n : ℕ => n*k) hsum]
  exact Nat.le_of_mul_le_mul_left hp hn

theorem ceilBlend_upper (T0 T1 L0 L1 T : ℕ)
    (h01 : T0<T1) (h0 : T0≤T) (h1 : T≤T1) :
    ceilBlend T0 T1 L0 L1 T≤max L0 L1 := by
  have hn : 0<T1-T0 := by omega
  have hsum : (T1-T)+(T-T0)=T1-T0 := by omega
  have hL := (ceilBlend_bounds T0 T1 L0 L1 T h01 h0 h1).2
  have hscale := Nat.add_le_add (Nat.mul_le_mul_left (T1-T) (le_max_left L0 L1))
    (Nat.mul_le_mul_left (T-T0) (le_max_right L0 L1))
  have hp : (T1-T0)*ceilBlend T0 T1 L0 L1 T<(T1-T0)*(max L0 L1+1) := by
    nlinarith only [hL,hscale,congrArg (fun n : ℕ => n*max L0 L1) hsum]
  have hh := Nat.lt_of_mul_lt_mul_left hp
  omega





end ProximityPrize.SubmissionLower.RelativeCertificate6814


