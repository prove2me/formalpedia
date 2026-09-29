-- Prove2me | solution 1 for AlgebraicCurve.Place.ord_eq_mul_or_eq_mul_of_modular_support
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cc92eecf-36ab-5b10-9c04-d13ebf790107

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_eq_mul_or_eq_mul_of_modular_support
set_option autoImplicit false
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_ord_eq_mul_or_eq_mul_of_modular_support.AlgebraicCurve Polynomial WithZero"

namespace S09CD

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem adicValuation_eq_exp (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.adicValuation f = WithZero.exp (-v.ord f) := by
  simp only [Place.ord, neg_neg]
  exact (WithZero.exp_log (v.adicValuation_ne_zero hf)).symm

private theorem adicValuation_intCast_le_one (v : Place K F) (n : ℤ) :
    v.adicValuation ((n : ℤ) : F) ≤ 1 := by
  have h : ((n : v.toValuationSubring) : F) = ((n : ℤ) : F) := by norm_cast
  rw [← h, v.adicValuation_coe]
  exact v.heightOneSpectrum.intValuation_le_one _

private theorem val_eval₂_lt (v : Place K F) (T : Polynomial (Polynomial ℤ)) (x y : F)
    (M : ℤᵐ⁰) (hM : M ≠ 0)
    (h : ∀ b a : ℕ, (T.coeff b).coeff a ≠ 0 →
      v.adicValuation x ^ a * v.adicValuation y ^ b < M) :
    v.adicValuation (T.eval₂ (eval₂RingHom (Int.castRingHom F) x) y) < M := by
  rw [eval₂_eq_sum_range]
  refine Valuation.map_sum_lt _ hM fun b _ => ?_
  rw [coe_eval₂RingHom, eval₂_eq_sum_range, Finset.sum_mul]
  refine Valuation.map_sum_lt _ hM fun a _ => ?_
  by_cases hc : (T.coeff b).coeff a = 0
  · simp only [hc, map_zero, zero_mul]
    exact zero_lt_iff.mpr hM
  · have hle : v.adicValuation ((Int.castRingHom F) ((T.coeff b).coeff a)) ≤ 1 := by
      rw [eq_intCast]
      exact adicValuation_intCast_le_one v _
    calc v.adicValuation ((Int.castRingHom F) ((T.coeff b).coeff a) * x ^ a * y ^ b)
        = v.adicValuation ((Int.castRingHom F) ((T.coeff b).coeff a)) *
            (v.adicValuation x ^ a * v.adicValuation y ^ b) := by
          rw [map_mul, map_mul, map_pow, map_pow, mul_assoc]
      _ ≤ 1 * (v.adicValuation x ^ a * v.adicValuation y ^ b) := mul_le_mul_left hle _
      _ = v.adicValuation x ^ a * v.adicValuation y ^ b := one_mul _
      _ < M := h b a hc

private theorem eq_zero_contra (v : Place K F) {u g₁ g₂ g₃ : F} (heq : u + g₁ + g₂ + g₃ = 0)
    (h₁ : v.adicValuation g₁ < v.adicValuation u)
    (h₂ : v.adicValuation g₂ < v.adicValuation u)
    (h₃ : v.adicValuation g₃ < v.adicValuation u) : False := by
  have hu : u = -g₁ + -g₂ + -g₃ := by linear_combination heq
  have h₁' : v.adicValuation (-g₁) < v.adicValuation u := by
    rw [Valuation.map_neg]; exact h₁
  have h₂' : v.adicValuation (-g₂) < v.adicValuation u := by
    rw [Valuation.map_neg]; exact h₂
  have h₃' : v.adicValuation (-g₃) < v.adicValuation u := by
    rw [Valuation.map_neg]; exact h₃
  have h := Valuation.map_add_lt _ (Valuation.map_add_lt _ h₁' h₂') h₃'
  rw [← hu] at h
  exact lt_irrefl _ h

private theorem newton_cases {P s t : ℤ} (hP : 1 ≤ P) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hst : s ≠ P * t) (hts : t ≠ P * s) :
    ((P + 1) * s > (P + 1) * t ∧ (P + 1) * s > P * (s + t)) ∨
      ((P + 1) * t > (P + 1) * s ∧ (P + 1) * t > P * (s + t)) ∨
      (P * (s + t) > (P + 1) * s ∧ P * (s + t) > (P + 1) * t) := by
  rcases lt_trichotomy s t with h | rfl | h
  · rcases lt_trichotomy t (P * s) with h2 | h2 | h2
    · have hPt : t ≤ P * t := le_mul_of_one_le_left (by omega) hP
      exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    · exact absurd h2 hts
    · have hPst : P * s < P * t := mul_lt_mul_of_pos_left h (by omega)
      exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
  · rcases eq_or_lt_of_le hP with h1 | h1
    · exact absurd (by rw [← h1, one_mul]) hst
    · have hs2 : s < P * s := lt_mul_of_one_lt_left (by omega) h1
      exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
  · rcases lt_trichotomy s (P * t) with h2 | h2 | h2
    · have hPs : s ≤ P * s := le_mul_of_one_le_left (by omega) hP
      exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    · exact absurd h2 hst
    · have hPts : P * t < P * s := mul_lt_mul_of_pos_left h (by omega)
      exact Or.inl ⟨by linarith, by linarith⟩

end S09CD

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Place.ord" namespace Place p2m_export "AlgebraicCurve.Place" "heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe ord toValuationSubring" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in
private theorem AlgebraicCurve.Place.ord_eq_mul_or_eq_mul_of_modular_support {K F : Type*} [Field K] [Field F] [Algebra K F] (U : Place K F) {p : ℕ} (hp : 0 < p) (Φ : Polynomial (Polynomial ℤ)) (hΦ₁ : ∀ b a : ℕ, ((Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 → 1 * a + p * b ≤ p ^ 2 + p - 1) (hΦ₂ : ∀ b a : ℕ, ((Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 → p * a + 1 * b ≤ p ^ 2 + p - 1) {x y : F} (hrel : Φ.eval₂ (eval₂RingHom (Int.castRingHom F) x) y = 0) (hx : U.ord x < 0) : U.ord y < 0 ∧ (U.ord x = p * U.ord y ∨ U.ord y = p * U.ord x) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨s, hs'⟩ : ∃ s : ℤ, U.ord x = -s := ⟨-U.ord x, by ring⟩
  have hs1 : (1 : ℤ) ≤ s := by omega
  have hA : U.adicValuation x = WithZero.exp s := by
    rw [S09CD.adicValuation_eq_exp U hx0, hs', neg_neg]
  have hApow : ∀ n : ℕ, U.adicValuation x ^ n = WithZero.exp ((n : ℤ) * s) := fun n => by
    rw [hA, ← WithZero.exp_nsmul, nsmul_eq_mul]
  have hvx : U.adicValuation (x ^ (p + 1)) = WithZero.exp (((p + 1 : ℕ) : ℤ) * s) := by
    rw [map_pow, hApow]
  obtain ⟨T, hT⟩ : ∃ T' : Polynomial (Polynomial ℤ),
      T' = Φ - X ^ (p + 1) - C (X ^ (p + 1)) + C (X ^ p) * X ^ p := ⟨_, rfl⟩

  have hTsupp : ∀ b a : ℕ, (T.coeff b).coeff a ≠ 0 → a ≤ p ∧ b ≤ p ∧ ¬(a = p ∧ b = p) := by
    intro b a hc
    have h₁ : ¬(a = p + 1 ∧ b = 0) → 1 * a + p * b ≤ p ^ 2 + p - 1 := by
      intro hne
      refine hΦ₁ b a ?_
      have heq2 : T = Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p) - C (X ^ (p + 1)) := by
        rw [hT]; ring
      have hz : (((C (X ^ (p + 1)) : Polynomial (Polynomial ℤ))).coeff b).coeff a = 0 := by
        rw [coeff_C]
        by_cases hb : b = 0
        · rw [if_pos hb, coeff_X_pow, if_neg fun ha => hne ⟨ha, hb⟩]
        · rw [if_neg hb, coeff_zero]
      have hc' := hc
      rw [heq2, coeff_sub, coeff_sub, hz, sub_zero] at hc'
      exact hc'
    have h₂ : ¬(a = 0 ∧ b = p + 1) → p * a + 1 * b ≤ p ^ 2 + p - 1 := by
      intro hne
      refine hΦ₂ b a ?_
      have heq2 : T = Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p) - X ^ (p + 1) := by
        rw [hT]; ring
      have hz : (((X ^ (p + 1) : Polynomial (Polynomial ℤ))).coeff b).coeff a = 0 := by
        rw [coeff_X_pow]
        by_cases hb : b = p + 1
        · rw [if_pos hb, coeff_one, if_neg fun ha => hne ⟨ha, hb⟩]
        · rw [if_neg hb, coeff_zero]
      have hc' := hc
      rw [heq2, coeff_sub, coeff_sub, hz, sub_zero] at hc'
      exact hc'
    refine ⟨?_, ?_, ?_⟩
    · by_contra hap
      have h := h₂ (by omega)
      have hmul : p * (p + 1) ≤ p * a := Nat.mul_le_mul_left p (by omega)
      have hsq : p ^ 2 + p = p * (p + 1) := by ring
      omega
    · by_contra hbp
      have h := h₁ (by omega)
      have hmul : p * (p + 1) ≤ p * b := Nat.mul_le_mul_left p (by omega)
      have hsq : p ^ 2 + p = p * (p + 1) := by ring
      omega
    · rintro ⟨ha', hb'⟩
      have h := h₁ (by omega)
      have hmul : p * b = p * p := by rw [hb']
      have hsq : p ^ 2 = p * p := by ring
      omega

  have heval : T.eval₂ (eval₂RingHom (Int.castRingHom F) x) y + y ^ (p + 1) + x ^ (p + 1)
      - x ^ p * y ^ p = 0 := by
    have hΦeq : Φ = T + X ^ (p + 1) + C (X ^ (p + 1)) - C (X ^ p) * X ^ p := by rw [hT]; ring
    rw [hΦeq] at hrel
    simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
      coe_eval₂RingHom] at hrel
    linear_combination hrel

  have hBgt : 1 < U.adicValuation y := by
    by_contra hBc
    rw [not_lt] at hBc
    refine S09CD.eq_zero_contra U (u := x ^ (p + 1)) (g₁ := y ^ (p + 1))
      (g₂ := -(x ^ p * y ^ p)) (g₃ := T.eval₂ (eval₂RingHom (Int.castRingHom F) x) y)
      ?_ ?_ ?_ ?_
    · linear_combination heval
    · rw [hvx, map_pow]
      calc U.adicValuation y ^ (p + 1) ≤ 1 := pow_le_one' hBc _
        _ < WithZero.exp (((p + 1 : ℕ) : ℤ) * s) := by
            rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
            push_cast
            exact mul_pos (by positivity) (by omega)
    · rw [hvx]
      calc U.adicValuation (-(x ^ p * y ^ p))
          = WithZero.exp ((p : ℤ) * s) * U.adicValuation y ^ p := by
            rw [Valuation.map_neg, map_mul, map_pow, map_pow, hApow]
        _ ≤ WithZero.exp ((p : ℤ) * s) * 1 := mul_le_mul_right (pow_le_one' hBc p) _
        _ = WithZero.exp ((p : ℤ) * s) := mul_one _
        _ < WithZero.exp (((p + 1 : ℕ) : ℤ) * s) := by
            rw [WithZero.exp_lt_exp]
            push_cast
            linarith
    · rw [hvx]
      refine S09CD.val_eval₂_lt U T x y _ WithZero.exp_ne_zero fun b a hc => ?_
      obtain ⟨ha, -, -⟩ := hTsupp b a hc
      calc U.adicValuation x ^ a * U.adicValuation y ^ b
          ≤ U.adicValuation x ^ a * 1 := mul_le_mul_right (pow_le_one' hBc b) _
        _ = WithZero.exp ((a : ℤ) * s) := by rw [mul_one, hApow]
        _ < WithZero.exp (((p + 1 : ℕ) : ℤ) * s) := by
            rw [WithZero.exp_lt_exp]
            have haz : (a : ℤ) ≤ (p : ℤ) := by exact_mod_cast ha
            have h2 : (a : ℤ) * s ≤ (p : ℤ) * s := mul_le_mul_of_nonneg_right haz (by omega)
            push_cast
            linarith
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hBgt
    exact absurd hBgt (not_lt.mpr zero_le')
  have hordy : U.ord y < 0 := by
    have h := hBgt
    rw [S09CD.adicValuation_eq_exp U hy0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    omega
  refine ⟨hordy, ?_⟩
  obtain ⟨t, ht'⟩ : ∃ t : ℤ, U.ord y = -t := ⟨-U.ord y, by ring⟩
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hB : U.adicValuation y = WithZero.exp t := by
    rw [S09CD.adicValuation_eq_exp U hy0, ht', neg_neg]
  have hBpow : ∀ n : ℕ, U.adicValuation y ^ n = WithZero.exp ((n : ℤ) * t) := fun n => by
    rw [hB, ← WithZero.exp_nsmul, nsmul_eq_mul]
  have hvy : U.adicValuation (y ^ (p + 1)) = WithZero.exp (((p + 1 : ℕ) : ℤ) * t) := by
    rw [map_pow, hBpow]
  have hvxy : U.adicValuation (-(x ^ p * y ^ p))
      = WithZero.exp ((p : ℤ) * s + (p : ℤ) * t) := by
    rw [Valuation.map_neg, map_mul, map_pow, map_pow, hApow, hBpow, ← WithZero.exp_add]

  have hr : U.adicValuation (T.eval₂ (eval₂RingHom (Int.castRingHom F) x) y)
      < WithZero.exp ((p : ℤ) * s + (p : ℤ) * t) := by
    refine S09CD.val_eval₂_lt U T x y _ WithZero.exp_ne_zero fun b a hc => ?_
    obtain ⟨ha, hb, hab⟩ := hTsupp b a hc
    rw [hApow, hBpow, ← WithZero.exp_add, WithZero.exp_lt_exp]
    rcases Nat.lt_or_ge a p with h | h
    · have h1 : (a : ℤ) * s < (p : ℤ) * s :=
        mul_lt_mul_of_pos_right (by exact_mod_cast h) (by omega)
      have h2 : (b : ℤ) * t ≤ (p : ℤ) * t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hb) (by omega)
      linarith
    · have ha' : a = p := le_antisymm ha h
      have hb' : b < p := by
        rcases Nat.lt_or_ge b p with h' | h'
        · exact h'
        · exact absurd ⟨ha', le_antisymm hb h'⟩ hab
      have h1 : (b : ℤ) * t < (p : ℤ) * t :=
        mul_lt_mul_of_pos_right (by exact_mod_cast hb') (by omega)
      have h2 : (a : ℤ) * s ≤ (p : ℤ) * s :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast ha) (by omega)
      linarith

  rw [hs', ht']
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have hst : s ≠ (p : ℤ) * t := by
    intro h
    exact hc1 (by rw [h]; ring)
  have hts : t ≠ (p : ℤ) * s := by
    intro h
    exact hc2 (by rw [h]; ring)
  rcases S09CD.newton_cases (P := (p : ℤ)) (by exact_mod_cast hp) hs1 ht1 hst hts with
    ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
  ·
    refine S09CD.eq_zero_contra U (u := x ^ (p + 1)) (g₁ := y ^ (p + 1))
      (g₂ := -(x ^ p * y ^ p)) (g₃ := T.eval₂ (eval₂RingHom (Int.castRingHom F) x) y)
      ?_ ?_ ?_ ?_
    · linear_combination heval
    · rw [hvx, hvy, WithZero.exp_lt_exp]; push_cast; linarith
    · rw [hvx, hvxy, WithZero.exp_lt_exp]; push_cast; linarith
    · rw [hvx]
      exact hr.trans_le (WithZero.exp_le_exp.mpr (by push_cast; linarith))
  ·
    refine S09CD.eq_zero_contra U (u := y ^ (p + 1)) (g₁ := x ^ (p + 1))
      (g₂ := -(x ^ p * y ^ p)) (g₃ := T.eval₂ (eval₂RingHom (Int.castRingHom F) x) y)
      ?_ ?_ ?_ ?_
    · linear_combination heval
    · rw [hvy, hvx, WithZero.exp_lt_exp]; push_cast; linarith
    · rw [hvy, hvxy, WithZero.exp_lt_exp]; push_cast; linarith
    · rw [hvy]
      exact hr.trans_le (WithZero.exp_le_exp.mpr (by push_cast; linarith))
  ·
    refine S09CD.eq_zero_contra U (u := -(x ^ p * y ^ p)) (g₁ := y ^ (p + 1))
      (g₂ := x ^ (p + 1)) (g₃ := T.eval₂ (eval₂RingHom (Int.castRingHom F) x) y)
      ?_ ?_ ?_ ?_
    · linear_combination heval
    · rw [hvxy, hvy, WithZero.exp_lt_exp]; push_cast; linarith
    · rw [hvxy, hvx, WithZero.exp_lt_exp]; push_cast; linarith
    · rw [hvxy]; exact hr

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_ord_eq_mul_or_eq_mul_of_modular_support.AlgebraicCurve Polynomial in
theorem solution : ∀ {K F : Type*} [Field K] [Field F] [Algebra K F] (U : Place K F) {p : ℕ} (hp : 0 < p) (Φ : Polynomial (Polynomial ℤ)) (hΦ₁ : ∀ b a : ℕ, ((Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 → 1 * a + p * b ≤ p ^ 2 + p - 1) (hΦ₂ : ∀ b a : ℕ, ((Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 → p * a + 1 * b ≤ p ^ 2 + p - 1) {x y : F} (hrel : Φ.eval₂ (eval₂RingHom (Int.castRingHom F) x) y = 0) (hx : U.ord x < 0), U.ord y < 0 ∧ (U.ord x = p * U.ord y ∨ U.ord y = p * U.ord x) :=
  @AlgebraicCurve.Place.ord_eq_mul_or_eq_mul_of_modular_support

end S_AlgebraicCurve_Place_ord_eq_mul_or_eq_mul_of_modular_support
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_eq_mul_or_eq_mul_of_modular_support (solution)
