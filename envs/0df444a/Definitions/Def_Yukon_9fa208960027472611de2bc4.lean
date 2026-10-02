-- Prove2me | Definitions.Def_Yukon_9fa208960027472611de2bc4
-- name    : Yukon_9fa208960027472611de2bc4
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T10:56:35.37308+00:00
-- url     : https://prove2.me/theorems/709ac91a-264b-4a01-9580-9c4ead0d5a1d
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeCubicArithmetic6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCubicArithmetic6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCubicArithmetic6814.lean
--
--   yukon-proof-operation:foundation-direct-e1b781e7ae41055ebf57f841aab6275e7da1e7b1e4f55380b84d8ef0f6e74d1a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiM2M5ZjUwMjU4MTU2N2IzNDM3MmFlY2U1NDUwNDc3NjM1NGVmZDE3YmVhMGEwOGEwYTRjNGZhNjJjNjkxZTQwOCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWUxYjc4MWU3YWU0MTA1NWViZjU3Zjg0MWFhYjYyNzVlN2RhMWU3YjFlNGY1NTM4MGI4NGQ4ZWYwZjZlNzRkMWEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl85ZmEyMDg5NjAwMjc0NzI2MTFkZTJiYzQiLCJ2IjoyfQ]

import Definitions.Def_Yukon_fa5bff97534969439522af47










































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Cubic Bernstein certificates replace a scan over contact orders.
The identities and positivity implication are proved over integers. -/
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 25000

structure Cubic where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ

def Cubic.eval (p : Cubic) (x : ℤ) : ℤ := ((p.c3*x+p.c2)*x+p.c1)*x+p.c0
def Cubic.deriv (p : Cubic) (x : ℤ) : ℤ := (3*p.c3*x+2*p.c2)*x+p.c1

theorem cubic_bernstein_identity (p : Cubic) (a b x : ℤ) :
    (b-a)^3*p.eval x=p.eval a*(b-x)^3+
      (3*p.eval a+(b-a)*p.deriv a)*(b-x)^2*(x-a)+
      (3*p.eval b-(b-a)*p.deriv b)*(b-x)*(x-a)^2+p.eval b*(x-a)^3 := by
  unfold Cubic.eval Cubic.deriv
  ring

theorem cubic_positive (p : Cubic) (a b x : ℤ)
    (ha : a≤x) (hb : x≤b) (h0 : 0<p.eval a) (h3 : 0<p.eval b)
    (h1 : 0≤3*p.eval a+(b-a)*p.deriv a)
    (h2 : 0≤3*p.eval b-(b-a)*p.deriv b) : 0<p.eval x := by
  by_cases he : a=b
  · have hx : x=a := by omega
    simpa only [hx] using h0
  have hw : 0<b-a := by omega
  have hu : 0≤b-x := by omega
  have hv : 0≤x-a := by omega
  have ht1 := mul_nonneg (mul_nonneg h1 (sq_nonneg (b-x))) hv
  have ht2 := mul_nonneg (mul_nonneg h2 hu) (sq_nonneg (x-a))
  have ht0 := mul_nonneg h0.le (pow_nonneg hu 3)
  have ht3 := mul_nonneg h3.le (pow_nonneg hv 3)
  have hid := cubic_bernstein_identity p a b x
  have hp : 0<(b-a)^3*p.eval x := by
    by_cases hx : x=b
    · have hs := mul_pos h3 (pow_pos (show 0<x-a by omega) 3)
      nlinarith only [hid,ht0,ht1,ht2,hs]
    · have hs := mul_pos h0 (pow_pos (show 0<b-x by omega) 3)
      nlinarith only [hid,hs,ht1,ht2,ht3]
  exact pos_of_mul_pos_right hp (pow_nonneg hw.le 3)

def Cubic.Check (p : Cubic) (a b : ℕ) : Prop :=
  b<a ∨ (0<p.eval a ∧ 0<p.eval b ∧
    0≤3*p.eval a+((b : ℤ)-a)*p.deriv a ∧
    0≤3*p.eval b-((b : ℤ)-a)*p.deriv b)

instance cubicCheckDecidable (p : Cubic) (a b : ℕ) : Decidable (p.Check a b) := by
  unfold Cubic.Check
  infer_instance

theorem Cubic.check_positive (p : Cubic) (a b x : ℕ) (hc : p.Check a b)
    (ha : a≤x) (hb : x≤b) : 0<p.eval x := by
  rcases hc with h | ⟨h0,h3,h1,h2⟩
  · omega
  · exact cubic_positive p a b x (by exact_mod_cast ha) (by exact_mod_cast hb) h0 h3 h1 h2

def rankPolynomial (base rate L s : ℤ) : Cubic :=
  let a0 := s*(s+1)*((4*s+2)*L-s*s+5*s+2)
  let a1 := -2*(s+1)*(3*L*s-3*L+6*s-4)
  let a2 := 6*(L+1)*(s+1)
  let a3 := -2*(s+1)
  ⟨a0+a1*base+a2*base^2+a3*base^3,
    -rate*(a1+2*a2*base+3*a3*base^2),
    rate^2*(a2+3*a3*base),-a3*rate^3⟩

theorem rankPolynomial_eval (base rate L s x : ℤ) :
    (rankPolynomial base rate L s).eval x=
      ClosedRank.sourceTwelve (base-rate*x) L s-
        ClosedRank.removedPartialTwelve (base-rate*x) L s s := by
  unfold rankPolynomial Cubic.eval ClosedRank.sourceTwelve ClosedRank.removedPartialTwelve
  ring

def marginPolynomial (b : Band) (d : Rectangle) (T L : ℕ) : Cubic :=
  let p := rankPolynomial ((d.alpha : ℤ)+d.beta) d.beta L d.s
  let q := rankPolynomial ((d.alpha : ℤ)+d.beta) ((d.beta : ℤ)+1) ((L : ℤ)-T) ((d.s : ℤ)-b.R)
  let c := 12*((countSlope (cutoff b d) d.s-countSlope (cutoff b d-d.lo) (d.s-b.R))*L+
    countSlope (cutoff b d-d.lo) (d.s-b.R)*T+
    countIntercept (cutoff b d) d.s-countIntercept (cutoff b d-d.lo) (d.s-b.R))
  ⟨c-262144*(p.c0-q.c0),-262144*(p.c1-q.c1),-262144*(p.c2-q.c2),-262144*(p.c3-q.c3)⟩

theorem marginPolynomial_eval (b : Band) (d : Rectangle) (T L mu : ℕ)
    (hmu : 1≤mu) (hR : b.R≤d.s)
    (hmmu : mu≤d.alpha-d.beta*(mu-1))
    (hs : 2*d.s≤d.alpha-d.beta*(mu-1))
    (hs' : 2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu) :
    (marginPolynomial b d T L).eval mu=
      marginA (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu*L+
      marginB (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu*T+
      marginC (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu := by
  let m := d.alpha-d.beta*(mu-1)
  have hmcast : (m : ℤ)=(d.alpha : ℤ)+d.beta-(d.beta : ℤ)*mu := by
    have hle : d.beta*(mu-1)≤d.alpha := by omega
    have hh : (m : ℤ)+(d.beta : ℤ)*(mu-1 : ℕ)=d.alpha := by
      exact_mod_cast Nat.sub_add_cancel hle
    rw [Nat.cast_sub hmu,Nat.cast_one] at hh
    nlinarith only [hh]
  have hinner : (d.alpha : ℤ)+d.beta-((d.beta : ℤ)+1)*mu=(m-mu : ℕ) := by
    rw [Nat.cast_sub hmmu]
    nlinarith only [hmcast]
  have hk : min d.s (m/2)=d.s := min_eq_left (by omega)
  have hk' : min (d.s-b.R) ((m-mu)/2)=d.s-b.R := min_eq_left (by omega)
  have ho := rankAffine_eq m d.s L
  have hi := rankAffine_eq (m-mu) (d.s-b.R) ((L : ℤ)-T)
  simp only [rankAffine,hk,hk'] at ho hi
  have he : (marginPolynomial b d T L).eval mu=
      12*((countSlope (cutoff b d) d.s-countSlope (cutoff b d-d.lo) (d.s-b.R))*L+
        countSlope (cutoff b d-d.lo) (d.s-b.R)*T+countIntercept (cutoff b d) d.s-
        countIntercept (cutoff b d-d.lo) (d.s-b.R))-
      262144*((rankPolynomial ((d.alpha : ℤ)+d.beta) d.beta L d.s).eval mu-
        (rankPolynomial ((d.alpha : ℤ)+d.beta) ((d.beta : ℤ)+1) ((L : ℤ)-T) ((d.s : ℤ)-b.R)).eval mu) := by
    unfold marginPolynomial Cubic.eval
    ring
  rw [he,rankPolynomial_eval,rankPolynomial_eval,←hmcast,hinner,←Nat.cast_sub hR,ho,hi]
  unfold marginA marginB marginC
  dsimp only [m] at *
  ring





end ProximityPrize.SubmissionLower.RelativeCertificate6814


