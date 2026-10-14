-- Prove2me | solution 1 for Apery.PotentialCertificate.table_sound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T15:09:02.965985+00:00
-- url     : https://prove2.me/submissions/d3f4cc12-bdef-4fb3-9915-3b13e776ed34

import Definitions.Def_Zeta5_PotentialTableData
import Definitions.Def_Zeta5_SourceTable2Data

-- From PotentialCertificateSound.lean
/-! The one-way adapter: light rational certificates imply real analytic bounds. -/

open Finset
namespace Apery.PotentialCertificate

theorem sumRange_eq (n : ℕ) (f : ℕ → ℚ) :
    sumRange n f = ∑ j ∈ range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRange, Finset.sum_range_succ, ih]

def Certificate.Interpret (c : Certificate) : Prop :=
  match c.kind with
  | .logUpper => Real.log (c.argument : ℝ) ≤ (c.bound : ℝ)
  | .logLower => (c.bound : ℝ) ≤ Real.log (c.argument : ℝ)
  | .arctanUpper => Real.arctan (c.argument : ℝ) ≤ (c.bound : ℝ)
  | .arctanLower => (c.bound : ℝ) ≤ Real.arctan (c.argument : ℝ)

theorem sound (c : Certificate) (hc : c.Valid) : c.Interpret := by
  rcases c with ⟨kind, x, b, k, m⟩
  cases kind with
  | logUpper =>
    rcases hc with ⟨hx, hk, hb⟩
    change Real.log (x : ℝ) ≤ (b : ℝ)
    refine (log_le_of_pow_two_upper (by exact_mod_cast hx) k m
      (by exact_mod_cast hk)).trans ?_
    have hcast : ((logUpper x k m : ℚ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    dsimp [logUpper] at hcast
    rw [sumRange_eq] at hcast
    push_cast at hcast
    exact hcast
  | logLower =>
    rcases hc with ⟨hx, hk, hb⟩
    change (b : ℝ) ≤ Real.log (x : ℝ)
    refine le_trans ?_ (log_ge_of_pow_two (by exact_mod_cast hx) k m
      (by exact_mod_cast hk))
    have hcast : (b : ℝ) ≤ ((logLower x k m : ℚ) : ℝ) := by exact_mod_cast hb
    dsimp [logLower] at hcast
    rw [sumRange_eq] at hcast
    push_cast at hcast
    exact hcast
  | arctanUpper =>
    rcases hc with ⟨hx0, hx1, hb⟩
    change Real.arctan (x : ℝ) ≤ (b : ℝ)
    refine (arctan_le_partial (by exact_mod_cast hx0) (by exact_mod_cast hx1) m).trans ?_
    have hcast : ((arctanPartial x (2 * m + 1) : ℚ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    dsimp [arctanPartial] at hcast
    rw [sumRange_eq] at hcast
    push_cast at hcast
    exact hcast
  | arctanLower =>
    rcases hc with ⟨hx0, hx1, hb⟩
    change (b : ℝ) ≤ Real.arctan (x : ℝ)
    refine le_trans ?_ (arctan_ge_partial (by exact_mod_cast hx0) (by exact_mod_cast hx1) m)
    have hcast : (b : ℝ) ≤ ((arctanPartial x (2 * m) : ℚ) : ℝ) := by exact_mod_cast hb
    dsimp [arctanPartial] at hcast
    rw [sumRange_eq] at hcast
    push_cast at hcast
    exact hcast

theorem interpret_get {cs : List Certificate} (h : check cs = true)
    (i : Nat) (hi : i < cs.length) : cs[i].Interpret :=
  sound _ (valid_get h i hi)

end Apery.PotentialCertificate

-- From PotentialTableUSound.lean
namespace Apery.PotentialCertificate

theorem LogCertificate.upper_sound (c : LogCertificate) (x : ℚ)
    (h : c.UpperValid x) : Real.log (x : ℝ) ≤ (c.bound : ℝ) :=
  sound ⟨.logUpper, x, c.bound, c.scale, c.order⟩ h

theorem LogCertificate.lower_sound (c : LogCertificate) (x : ℚ)
    (h : c.LowerValid x) : (c.bound : ℝ) ≤ Real.log (x : ℝ) :=
  sound ⟨.logLower, x, c.bound, c.scale, c.order⟩ h

theorem OmegaCertificate.sound (c : OmegaCertificate) (p a b : ℚ)
    (hc : c.Valid p a b) : Uω (a : ℝ) (b : ℝ) (p : ℝ) ≤ (c.log.bound : ℝ) := by
  rcases c with ⟨position, s, l⟩
  cases position with
  | left =>
      rcases hc with ⟨hab, hp, hs0, hs, hl⟩
      have hl' := l.upper_sound _ hl
      push_cast at hl'
      exact Uω_le_left (by exact_mod_cast hab) (by exact_mod_cast hp)
        (by exact_mod_cast hs0) (by exact_mod_cast hs) hl'
  | inside =>
      rcases hc with ⟨ha, hb, hl⟩
      have hl' := l.upper_sound _ hl
      push_cast at hl'
      exact Uω_le_inside (by exact_mod_cast ha) (by exact_mod_cast hb) hl'
  | right =>
      rcases hc with ⟨hab, hp, hs0, hs, hl⟩
      have hl' := l.upper_sound _ hl
      push_cast at hl'
      exact Uω_le_right (by exact_mod_cast hab) (by exact_mod_cast hp)
        (by exact_mod_cast hs0) (by exact_mod_cast hs) hl'

private theorem table2WeightedUpper {t : ℝ}
    {u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 : ℝ}
    (h1 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) t ≤ u1)
    (h2 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) t ≤ u2)
    (h3 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) t ≤ u3)
    (h4 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) t ≤ u4)
    (h5 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) t ≤ u5)
    (h6 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) t ≤ u6)
    (h7 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) t ≤ u7)
    (h8 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) t ≤ u8)
    (h9 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) t ≤ u9)
    (h10 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) t ≤ u10)
    (h11 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) t ≤ u11)
    (h12 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) t ≤ u12)
    (h13 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) t ≤ u13)
    (h14 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) t ≤ u14)
    (h15 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) t ≤ u15)
    (h16 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) t ≤ u16)
    : Uρ t ≤ (525779809 / 50000000000 : ℝ) * u1 +
      (29471737793 / 1000000000000 : ℝ) * u2 +
      (42934365099 / 1000000000000 : ℝ) * u3 +
      (29102115983 / 500000000000 : ℝ) * u4 +
      (6903762131 / 100000000000 : ℝ) * u5 +
      (78873099189 / 1000000000000 : ℝ) * u6 +
      (84856120711 / 1000000000000 : ℝ) * u7 +
      (88396082127 / 1000000000000 : ℝ) * u8 +
      (706427057 / 8000000000 : ℝ) * u9 +
      (17094464251 / 200000000000 : ℝ) * u10 +
      (39449592119 / 500000000000 : ℝ) * u11 +
      (35176735959 / 500000000000 : ℝ) * u12 +
      (11767795323 / 200000000000 : ℝ) * u13 +
      (22210660553 / 500000000000 : ℝ) * u14 +
      (30462865791 / 1000000000000 : ℝ) * u15 +
      (5959622577 / 1000000000000 : ℝ) * u16 := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num1)) (mul_le_mul_of_nonneg_left h2 (by norm_num1))) (mul_le_mul_of_nonneg_left h3 (by norm_num1))) (mul_le_mul_of_nonneg_left h4 (by norm_num1))) (mul_le_mul_of_nonneg_left h5 (by norm_num1))) (mul_le_mul_of_nonneg_left h6 (by norm_num1))) (mul_le_mul_of_nonneg_left h7 (by norm_num1))) (mul_le_mul_of_nonneg_left h8 (by norm_num1))) (mul_le_mul_of_nonneg_left h9 (by norm_num1))) (mul_le_mul_of_nonneg_left h10 (by norm_num1))) (mul_le_mul_of_nonneg_left h11 (by norm_num1))) (mul_le_mul_of_nonneg_left h12 (by norm_num1))) (mul_le_mul_of_nonneg_left h13 (by norm_num1))) (mul_le_mul_of_nonneg_left h14 (by norm_num1))) (mul_le_mul_of_nonneg_left h15 (by norm_num1))) (mul_le_mul_of_nonneg_left h16 (by norm_num1)))

theorem UCertificate.sound (c : UCertificate) (hc : c.Valid) :
    Uρ (c.point : ℝ) ≤ (c.upper : ℝ) := by
  rcases hc with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
  have h1 := OmegaCertificate.sound _ _ _ _ h1
  have h2 := OmegaCertificate.sound _ _ _ _ h2
  have h3 := OmegaCertificate.sound _ _ _ _ h3
  have h4 := OmegaCertificate.sound _ _ _ _ h4
  have h5 := OmegaCertificate.sound _ _ _ _ h5
  have h6 := OmegaCertificate.sound _ _ _ _ h6
  have h7 := OmegaCertificate.sound _ _ _ _ h7
  have h8 := OmegaCertificate.sound _ _ _ _ h8
  have h9 := OmegaCertificate.sound _ _ _ _ h9
  have h10 := OmegaCertificate.sound _ _ _ _ h10
  have h11 := OmegaCertificate.sound _ _ _ _ h11
  have h12 := OmegaCertificate.sound _ _ _ _ h12
  have h13 := OmegaCertificate.sound _ _ _ _ h13
  have h14 := OmegaCertificate.sound _ _ _ _ h14
  have h15 := OmegaCertificate.sound _ _ _ _ h15
  have h16 := OmegaCertificate.sound _ _ _ _ h16
  push_cast at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  unfold UCertificate.upper
  push_cast
  exact table2WeightedUpper h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16


end Apery.PotentialCertificate

-- From PotentialTableAtanSound.lean
namespace Apery.PotentialCertificate

def AtanCertificate.Interpret (c : AtanCertificate) (upper : Bool) (x : ℚ) : Prop :=
  if upper then Real.arctan (x : ℝ) ≤ (c.bound : ℝ)
  else (c.bound : ℝ) ≤ Real.arctan (x : ℝ)

theorem AtanCertificate.sound (c : AtanCertificate) (upper : Bool) (x : ℚ)
    (hc : c.Valid upper x) : c.Interpret upper x := by
  induction c generalizing upper x with
  | direct b m =>
      cases upper
      · exact PotentialCertificate.sound ⟨.arctanLower, x, b, 0, m⟩ hc
      · exact PotentialCertificate.sound ⟨.arctanUpper, x, b, 0, m⟩ hc
  | reciprocal b inner ih =>
      cases upper
      · rcases hc with ⟨hx, hi, hb⟩
        simp only [Bool.false_eq_true, if_false] at hb
        have hi' := ih true (1 / x) hi
        change Real.arctan ((1 / x : ℚ) : ℝ) ≤ (inner.bound : ℝ) at hi'
        push_cast at hi'
        have hb' := (Rat.cast_le (K := ℝ)).mpr hb
        push_cast at hb'
        norm_num1 at hb'
        change (b : ℝ) ≤ Real.arctan (x : ℝ)
        rw [arctan_eq_pi_div_two_sub (by exact_mod_cast hx)]
        linarith [Real.pi_gt_d20]
      · rcases hc with ⟨hx, hi, hb⟩
        simp only [if_true] at hb
        have hi' := ih false (1 / x) hi
        change (inner.bound : ℝ) ≤ Real.arctan ((1 / x : ℚ) : ℝ) at hi'
        push_cast at hi'
        have hb' := (Rat.cast_le (K := ℝ)).mpr hb
        push_cast at hb'
        norm_num1 at hb'
        change Real.arctan (x : ℝ) ≤ (b : ℝ)
        rw [arctan_eq_pi_div_two_sub (by exact_mod_cast hx)]
        linarith [Real.pi_lt_d20]
  | half b w inner ih =>
      cases upper
      · rcases hc with ⟨hx, hw, hs, hi, hb⟩
        have hi' := ih false (x / (1 + w)) hi
        change (inner.bound : ℝ) ≤ Real.arctan ((x / (1 + w) : ℚ) : ℝ) at hi'
        push_cast at hi'
        have hb' : (b : ℝ) ≤ 2 * (inner.bound : ℝ) := by exact_mod_cast hb
        have hs' : Real.sqrt (1 + (x : ℝ) ^ 2) ≤ (w : ℝ) :=
          sqrt_le_of_sq_le (by exact_mod_cast hw) (by exact_mod_cast hs)
        have hh := arctan_ge_half (by exact_mod_cast hx) hs'
        change (b : ℝ) ≤ Real.arctan (x : ℝ)
        linarith
      · rcases hc with ⟨hx, hw, hs, hi, hb⟩
        have hi' := ih true (x / (1 + w)) hi
        change Real.arctan ((x / (1 + w) : ℚ) : ℝ) ≤ (inner.bound : ℝ) at hi'
        push_cast at hi'
        have hb' : 2 * (inner.bound : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
        have hw' : (0 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
        have hs' : (w : ℝ) ≤ Real.sqrt (1 + (x : ℝ) ^ 2) :=
          le_sqrt_of_sq_le hw' (by exact_mod_cast hs)
        have hh := arctan_le_half (by exact_mod_cast hx) hw' hs'
        change Real.arctan (x : ℝ) ≤ (b : ℝ)
        linarith

end Apery.PotentialCertificate

-- From PotentialTableVSound.lean
namespace Apery.PotentialCertificate

/-- The same template covers both point bounds and the narrow interval around
the minimum of V; no separate numerical Vstar proof is needed. -/
theorem VCertificate.sound (c : VCertificate) (hc : c.Valid) {t : ℝ}
    (ht1 : (c.left : ℝ) ≤ t) (ht2 : t ≤ (c.right : ℝ)) :
    (c.lower : ℝ) ≤ Vfield t := by
  rcases hc with ⟨hp, _, hslo, hs1, hshi, hs2, hl1, hl2, ha1, ha2, hsign⟩
  have hp' : (0 : ℝ) < (c.left : ℝ) := by exact_mod_cast hp
  have ht : 0 < t := hp'.trans_le ht1
  have hslo' : (0 : ℝ) < (c.sqrtLower : ℝ) := by exact_mod_cast hslo
  have hsq : (c.sqrtLower : ℝ) ^ 2 ≤ (c.left : ℝ) := by exact_mod_cast hs1
  have hs1' : (c.sqrtLower : ℝ) ≤ Real.sqrt t :=
    le_sqrt_of_sq_le hslo'.le (hsq.trans ht1)
  have hs2' : Real.sqrt t ≤ (c.sqrtUpper : ℝ) :=
    sqrt_le_of_sq_le (by exact_mod_cast hshi) (ht2.trans (by exact_mod_cast hs2))
  have hl1' := c.logLower.lower_sound _ hl1
  have hl2' := c.logUpper.upper_sound _ hl2
  push_cast at hl1' hl2'
  have hl1t : (c.logLower.bound : ℝ) ≤ Real.log (1 + t) :=
    hl1'.trans (Real.log_le_log (by linarith) (by linarith))
  have hl2t : Real.log (t + (3 / 40) ^ 2) ≤ (c.logUpper.bound : ℝ) :=
    (Real.log_le_log (by positivity) (by linarith)).trans hl2'
  have ha1' := c.atanLower.sound false _ ha1
  have ha2' := c.atanUpper.sound true _ ha2
  change (c.atanLower.bound : ℝ) ≤ Real.arctan ((1 / c.sqrtUpper : ℚ) : ℝ) at ha1'
  change Real.arctan (((3 / 40) / c.sqrtLower : ℚ) : ℝ) ≤ (c.atanUpper.bound : ℝ) at ha2'
  push_cast at ha1' ha2'
  cases hpos : c.positive with
  | false =>
      simp only [hpos, Bool.false_eq_true, if_false] at hsign
      have hsign' : 3.14159265358979323846 + (c.atanLower.bound : ℝ) -
          6 * (c.atanUpper.bound : ℝ) ≤ 0 := by
        have hcast := (Rat.cast_le (K := ℝ)).mpr hsign
        dsimp [VCertificate.parenthesis] at hcast
        push_cast at hcast
        norm_num1 at hcast ⊢
        exact hcast
      simp only [VCertificate.lower, hpos, Bool.false_eq_true, if_false,
        VCertificate.parenthesis]
      push_cast
      exact Vfield_ge_of_bounds_neg ht hslo' hs1' hs2' hl1t hl2t ha1' ha2' hsign'
  | true =>
      simp only [hpos, if_true] at hsign
      have hsign' : (0 : ℝ) ≤ 3.14159265358979323846 + (c.atanLower.bound : ℝ) -
          6 * (c.atanUpper.bound : ℝ) := by
        have hcast := (Rat.cast_le (K := ℝ)).mpr hsign
        dsimp [VCertificate.parenthesis] at hcast
        push_cast at hcast
        norm_num1 at hcast ⊢
        exact hcast
      simp only [VCertificate.lower, hpos, if_true, VCertificate.parenthesis]
      push_cast
      exact Vfield_ge_of_bounds_pos ht hslo' hs1' hs2' hl1t hl2t ha1' ha2' hsign'

end Apery.PotentialCertificate

-- From PotentialTableSound.lean
namespace Apery.PotentialCertificate

theorem IntervalCertificate.u_sound (c : IntervalCertificate)
    (hu : c.u.Valid) (hp : c.UValid) {t : ℝ}
    (ht1 : (c.left : ℝ) ≤ t) (ht2 : t ≤ (c.right : ℝ)) :
    Uρ t ≤ (c.u.upper : ℝ) := by
  have hu' := c.u.sound hu
  cases hpos : c.uPosition with
  | left =>
      simp only [UValid, hpos] at hp
      rcases hp with ⟨hp, hr⟩
      have hp' : (c.u.point : ℝ) ≤ (c.left : ℝ) := by exact_mod_cast hp
      have hr' : (c.right : ℝ) ≤ aρ 1 := by
        rw [aρ_1]
        have h := (Rat.cast_le (K := ℝ)).mpr hr
        push_cast at h
        exact h
      have hpt := hp'.trans ht1
      have hta := ht2.trans hr'
      exact (Uρ_antitoneOn (hpt.trans hta) hta hpt).trans hu'
  | inside =>
      simp only [UValid, hpos] at hp
      rcases hp with ⟨hl, hr, hpl, hpr⟩
      have hl' : aρ 1 ≤ (c.left : ℝ) := by
        rw [aρ_1]
        have h := (Rat.cast_le (K := ℝ)).mpr hl
        push_cast at h
        exact h
      have hr' : (c.right : ℝ) ≤ bρ 1 := by
        rw [bρ_1]
        have h := (Rat.cast_le (K := ℝ)).mpr hr
        push_cast at h
        exact h
      have hpl' : aρ 1 ≤ (c.u.point : ℝ) := by
        rw [aρ_1]
        have h := (Rat.cast_le (K := ℝ)).mpr hpl
        push_cast at h
        exact h
      have hpr' : (c.u.point : ℝ) ≤ bρ 1 := by
        rw [bρ_1]
        have h := (Rat.cast_le (K := ℝ)).mpr hpr
        push_cast at h
        exact h
      rw [Uρ_of_mem (hl'.trans ht1) (ht2.trans hr')]
      rwa [Uρ_of_mem hpl' hpr'] at hu'
  | right =>
      simp only [UValid, hpos] at hp
      rcases hp with ⟨hl, hp⟩
      have hl' : bρ 1 ≤ (c.left : ℝ) := by
        rw [bρ_1]
        have h := (Rat.cast_le (K := ℝ)).mpr hl
        push_cast at h
        exact h
      have hp' : (c.right : ℝ) ≤ (c.u.point : ℝ) := by exact_mod_cast hp
      have hbt := hl'.trans ht1
      have htp := ht2.trans hp'
      exact (Uρ_monotoneOn hbt (hbt.trans htp) htp).trans hu'

theorem IntervalCertificate.v_sound (c : IntervalCertificate)
    (hv : c.v.Valid) (hp : c.VValid) {t : ℝ} (ht : 0 < t)
    (ht1 : (c.left : ℝ) ≤ t) (ht2 : t ≤ (c.right : ℝ)) :
    (c.v.lower : ℝ) ≤ Vfield t := by
  cases hpos : c.vPosition with
  | left =>
      simp only [VValid, hpos] at hp
      rcases hp with ⟨he, hr, hq⟩
      have hr' : (c.right : ℝ) ≤ (c.v.left : ℝ) := by exact_mod_cast hr
      have hq' : (c.v.left : ℝ) ≤ qm := by
        have h := (Rat.cast_le (K := ℝ)).mpr hq
        push_cast at h
        exact h
      have htp := ht2.trans hr'
      have hp0 : (0 : ℝ) < (c.v.left : ℝ) := by exact_mod_cast hv.1
      have hb := c.v.sound hv (t := (c.v.left : ℝ)) le_rfl (by rw [he])
      exact hb.trans (Vfield_antitoneOn ⟨ht, htp.trans hq'⟩ ⟨hp0, hq'⟩ htp)
  | box =>
      simp only [VValid, hpos] at hp
      have hl : (c.v.left : ℝ) ≤ (c.left : ℝ) := by exact_mod_cast hp.1
      have hr : (c.right : ℝ) ≤ (c.v.right : ℝ) := by exact_mod_cast hp.2
      exact c.v.sound hv (hl.trans ht1) (ht2.trans hr)
  | right =>
      simp only [VValid, hpos] at hp
      rcases hp with ⟨he, hq, hl⟩
      have hq' : qp ≤ (c.v.left : ℝ) := by
        have h := (Rat.cast_le (K := ℝ)).mpr hq
        push_cast at h
        exact h
      have hl' : (c.v.left : ℝ) ≤ (c.left : ℝ) := by exact_mod_cast hl
      have hpt := hl'.trans ht1
      have hb := c.v.sound hv (t := (c.v.left : ℝ)) le_rfl (by rw [he])
      exact hb.trans (Vfield_monotoneOn hq' (hq'.trans hpt) hpt)

theorem IntervalCertificate.sound (c : IntervalCertificate) (hc : c.Valid)
    {t : ℝ} (ht : 0 < t) (ht1 : (c.left : ℝ) ≤ t) (ht2 : t ≤ (c.right : ℝ)) :
    2 * Uρ t - Vfield t ≤ M0 := by
  rcases hc with ⟨_, _, hu, hv, hup, hvp, hbound⟩
  have hu' := c.u_sound hu hup ht1 ht2
  have hv' := c.v_sound hv hvp ht ht1 ht2
  have hbound' : 2 * (c.u.upper : ℝ) - (c.v.lower : ℝ) ≤ -1329 / 200 := by
    exact_mod_cast hbound
  change _ ≤ -1329 / 200
  linarith

/-- A single analytic theorem interprets any size of checked table. -/
theorem TableCertificate.sound (c : TableCertificate) (hc : c.Valid)
    {t : ℝ} (ht : 0 < t) (ht1 : (c.left : ℝ) ≤ t) (ht2 : t ≤ (c.right : ℝ)) :
    2 * Uρ t - Vfield t ≤ M0 := by
  induction c with
  | leaf c => exact c.sound hc ht ht1 ht2
  | join a b ha hb =>
      rcases hc with ⟨hva, hvb, hjoin⟩
      by_cases hm : t ≤ (a.right : ℝ)
      · exact ha hva ht1 hm
      · have hm' : (a.right : ℝ) < t := lt_of_not_ge hm
        have hj : (b.left : ℝ) ≤ (a.right : ℝ) := by exact_mod_cast hjoin
        exact hb hvb (hj.trans hm'.le) ht2

end Apery.PotentialCertificate

open Apery Apery.PotentialCertificate

/-- Generic adapter target: the statement exposes no helpers from this proof. -/
theorem solution (c : TableCertificate) (hc : c.Valid)
    (t : ℝ) (ht : 0 < t) (ht1 : (c.left : ℝ) ≤ t) (ht2 : t ≤ (c.right : ℝ)) :
    2 * Uρ t - Vfield t ≤ M0 :=
  TableCertificate.sound c hc ht ht1 ht2

#print axioms solution
