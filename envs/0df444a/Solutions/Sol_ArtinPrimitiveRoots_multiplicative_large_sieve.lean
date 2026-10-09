-- Prove2me | solution 1 for ArtinPrimitiveRoots.multiplicative_large_sieve
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T16:44:32.786915+00:00
-- url     : https://prove2.me/submissions/1000a438-323f-412a-9300-1eaf8c3fe01e

import Mathlib
import Definitions.Def_ArtinBV
import Theorems.Thm_LargeSieve_analytic_large_sieve

section

end

section
/-!
# Gauss sums and Parseval identities for the multiplicative large sieve
-/

namespace ArtinPrimitiveRoots.BV

open Finset ComplexConjugate

variable {d : ℕ} [NeZero d]

/-- Additive Parseval identity on `ZMod d`. -/
theorem add_parseval (f : ZMod d → ℂ) :
    ∑ a : ZMod d, ‖∑ x, f x * ZMod.stdAddChar (a * x)‖ ^ 2 = d * ∑ x, ‖f x‖ ^ 2 := by
  suffices h : ((∑ a : ZMod d, ‖∑ x, f x * ZMod.stdAddChar (a * x)‖ ^ 2 : ℝ) : ℂ) =
      ((d * ∑ x, ‖f x‖ ^ 2 : ℝ) : ℂ) by exact_mod_cast h
  push_cast
  simp_rw [← Complex.conj_mul', map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  have key : ∀ x y : ZMod d, ∑ a : ZMod d, conj (ZMod.stdAddChar (a * y)) * ZMod.stdAddChar (a * x)
      = if x = y then (d : ℂ) else 0 := by
    intro x y
    have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod d) ℂ)) (x - y)
      (ZMod.isPrimitive_stdAddChar d)
    rw [← sub_eq_zero]
    have : ∀ a : ZMod d, conj (ZMod.stdAddChar (a * y)) * ZMod.stdAddChar (a * x) =
        ZMod.stdAddChar (a * (x - y)) := by
      intro a
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
      ring_nf
    simp_rw [this]
    rw [h]
    simp [sub_eq_zero, ZMod.card]
  rw [Finset.sum_comm]
  calc ∑ y, ∑ a, ∑ x, conj (f y) * conj (ZMod.stdAddChar (a * y)) * (f x * ZMod.stdAddChar (a * x))
      = ∑ y, ∑ x, conj (f y) * f x *
          ∑ a, conj (ZMod.stdAddChar (a * y)) * ZMod.stdAddChar (a * x) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
    _ = ∑ y, (d : ℂ) * (conj (f y) * f y) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        simp_rw [key]
        simp [mul_comm]

/-- Orthogonality of Dirichlet characters, conjugate form. -/
theorem sum_char_mul_conj (x y : ZMod d) :
    ∑ χ : DirichletCharacter ℂ d, χ x * conj (χ y) =
      if IsUnit y ∧ x = y then (d.totient : ℂ) else 0 := by
  have h1 : ∀ χ : DirichletCharacter ℂ d, χ x * conj (χ y) = χ (x * Ring.inverse y) := by
    intro χ
    rw [map_mul, ← MulChar.inv_apply, ← MulChar.star_apply']
    rfl
  simp_rw [h1]
  rw [DirichletCharacter.sum_characters_eq]
  by_cases hy : IsUnit y
  · have : x * Ring.inverse y = 1 ↔ x = y := by
      constructor
      · intro h
        have := congrArg (· * y) h
        simp only [mul_assoc, Ring.inverse_mul_cancel y hy, mul_one, one_mul] at this
        exact this
      · rintro rfl; exact Ring.mul_inverse_cancel x hy
    simp [this, hy]
  · have hnt : Nontrivial (ZMod d) := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      exact hy (isUnit_of_subsingleton y)
    simp [hy]

/-- Multiplicative Parseval identity. -/
theorem mult_parseval (g : ZMod d → ℂ) :
    ∑ χ : DirichletCharacter ℂ d, ‖∑ x, χ x * g x‖ ^ 2 =
      d.totient * ∑ x ∈ univ.filter IsUnit, ‖g x‖ ^ 2 := by
  suffices h : ((∑ χ : DirichletCharacter ℂ d, ‖∑ x, χ x * g x‖ ^ 2 : ℝ) : ℂ) =
      ((d.totient * ∑ x ∈ univ.filter IsUnit, ‖g x‖ ^ 2 : ℝ) : ℂ) by exact_mod_cast h
  push_cast
  simp_rw [← Complex.conj_mul', map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  calc ∑ y, ∑ χ : DirichletCharacter ℂ d, ∑ x, conj (χ y) * conj (g y) * (χ x * g x)
      = ∑ y, ∑ x, conj (g y) * g x * ∑ χ : DirichletCharacter ℂ d, χ x * conj (χ y) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
    _ = ∑ y, if IsUnit y then (d.totient : ℂ) * (conj (g y) * g y) else 0 := by
        refine Finset.sum_congr rfl fun y _ => ?_
        simp_rw [sum_char_mul_conj]
        by_cases hy : IsUnit y
        · simp [hy, mul_comm]
        · simp [hy]
    _ = ∑ x ∈ univ.filter IsUnit, (d.totient : ℂ) * (conj (g x) * g x) := by
        rw [Finset.sum_filter]

/-- The Gauss sum of a primitive character has absolute value `√d`. -/
theorem norm_gaussSum_sq {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = d := by
  have h := add_parseval (d := d) (fun x => χ x)
  have hL : ∀ a : ZMod d, ‖∑ x, χ x * ZMod.stdAddChar (a * x)‖ ^ 2 =
      ‖χ⁻¹ a‖ ^ 2 * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 := by
    intro a
    have := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar : AddChar (ZMod d) ℂ) hχ a
    simp only [gaussSum, AddChar.mulShift_apply] at this
    rw [this, norm_mul, mul_pow]
    rfl
  have hnorm : ∀ (ξ : DirichletCharacter ℂ d) (a : ZMod d),
      ‖ξ a‖ ^ 2 = if IsUnit a then 1 else 0 := by
    intro ξ a
    by_cases ha : IsUnit a
    · rw [if_pos ha]
      have := DirichletCharacter.unit_norm_eq_one ξ ha.unit
      rw [IsUnit.unit_spec] at this
      rw [this, one_pow]
    · rw [if_neg ha, MulChar.map_nonunit _ ha, norm_zero]
      norm_num
  simp_rw [hL, hnorm] at h
  rw [← Finset.sum_mul] at h
  have hcount : (0 : ℝ) < ∑ x : ZMod d, (if IsUnit x then (1 : ℝ) else 0) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_one]
    exact_mod_cast Finset.card_pos.mpr ⟨1, by simp⟩
  have : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * ∑ x : ZMod d, (if IsUnit x then (1 : ℝ) else 0) =
      d * ∑ x : ZMod d, (if IsUnit x then (1 : ℝ) else 0) := by
    rw [mul_comm]; exact h
  exact mul_right_cancel₀ hcount.ne' this

end ArtinPrimitiveRoots.BV
end

section
/-!
# From primitive characters to additive characters
-/

namespace ArtinPrimitiveRoots.BV

open Finset ComplexConjugate

/-- The additive character `b/d`, evaluated at `n`. -/
theorem stdAddChar_natCast_mul {d : ℕ} [NeZero d] (n b : ℕ) :
    ZMod.stdAddChar ((n : ZMod d) * (b : ZMod d)) =
      Complex.exp (2 * Real.pi * Complex.I * (((n : ℝ) : ℂ) * (((b : ℝ) / (d : ℝ) : ℝ) : ℂ))) := by
  rw [← Nat.cast_mul, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  congr 1
  push_cast
  ring

/-- Per-modulus inequality: primitive characters are controlled by the additive characters
`b/d` with `(b, d) = 1`. -/
theorem prim_gauss_bound (d : ℕ) [NeZero d] (s : Finset ℕ) (c : ℕ → ℂ) :
    (d : ℝ) * ∑ χ ∈ primChars d, ‖∑ n ∈ s, c n * χ n‖ ^ 2 ≤
      d.totient * ∑ b ∈ (range d).filter (fun b => b.Coprime d),
        ‖∑ n ∈ s, c n * Complex.exp (2 * Real.pi * Complex.I * (((n : ℝ) : ℂ) * (((b : ℝ) / (d : ℝ) : ℝ) : ℂ)))‖ ^ 2 := by
  set T : ZMod d → ℂ := fun x => ∑ n ∈ s, c n * ZMod.stdAddChar ((n : ZMod d) * x) with hT
  -- Step 1: replace χ by χ⁻¹
  have h1 : ∑ χ ∈ primChars d, ‖∑ n ∈ s, c n * χ n‖ ^ 2 =
      ∑ χ ∈ primChars d, ‖∑ n ∈ s, c n * χ⁻¹ n‖ ^ 2 := by
    refine Finset.sum_bij' (fun χ _ => χ⁻¹) (fun χ _ => χ⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro χ hχ
      simp only [primChars, Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
      rw [DirichletCharacter.conductor_inv, hχ]
    · intro χ hχ
      simp only [primChars, Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
      rw [DirichletCharacter.conductor_inv, hχ]
    · intro χ _; simp
    · intro χ _; simp
    · intro χ _; simp
  -- Step 2: Gauss sum identity
  have h2 : ∀ χ ∈ primChars d, (d : ℝ) * ‖∑ n ∈ s, c n * χ⁻¹ n‖ ^ 2 = ‖∑ x, χ x * T x‖ ^ 2 := by
    intro χ hχ
    have hprim : χ.IsPrimitive := by
      simp only [primChars, Finset.mem_filter, Finset.mem_univ, true_and] at hχ
      exact hχ
    have hid : (∑ n ∈ s, c n * χ⁻¹ n) * gaussSum χ ZMod.stdAddChar = ∑ x, χ x * T x := by
      rw [Finset.sum_mul]
      simp_rw [hT, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      have := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar : AddChar (ZMod d) ℂ) hprim
        (n : ZMod d)
      simp only [gaussSum, AddChar.mulShift_apply] at this
      have this' : ∑ a, χ a * ZMod.stdAddChar ((n : ZMod d) * a) =
          χ⁻¹ n * gaussSum χ ZMod.stdAddChar := this
      rw [mul_assoc, ← this', Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [← hid, norm_mul, mul_pow, norm_gaussSum_sq hprim, mul_comm]
  -- Step 3: drop primitivity and use Parseval
  have h3 : ∑ χ ∈ primChars d, ‖∑ x, χ x * T x‖ ^ 2 ≤
      d.totient * ∑ x ∈ univ.filter IsUnit, ‖T x‖ ^ 2 := by
    rw [← mult_parseval T]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => by positivity)
  -- Step 4: units of `ZMod d` are the reduced residues
  have h4 : ∑ x ∈ univ.filter IsUnit, ‖T x‖ ^ 2 =
      ∑ b ∈ (range d).filter (fun b => b.Coprime d),
        ‖∑ n ∈ s, c n * Complex.exp (2 * Real.pi * Complex.I * (((n : ℝ) : ℂ) * (((b : ℝ) / (d : ℝ) : ℝ) : ℂ)))‖ ^ 2 := by
    symm
    refine Finset.sum_bij' (fun b _ => (b : ZMod d)) (fun x _ => x.val) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hb ⊢
      exact (ZMod.isUnit_iff_coprime b d).mpr hb.2
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨ZMod.val_lt x, ?_⟩
      exact (ZMod.isUnit_iff_coprime x.val d).mp (by simpa using hx)
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      exact ZMod.val_natCast_of_lt hb.1
    · intro x _
      simp
    · intro b _
      simp only [hT]
      congr 2
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [stdAddChar_natCast_mul]
  rw [h1, Finset.mul_sum, Finset.sum_congr rfl h2, ← h4]
  exact h3

end ArtinPrimitiveRoots.BV
end

section
/-!
# The multiplicative large sieve
-/

namespace ArtinPrimitiveRoots.BV

open Finset

/-- Distinct reduced fractions with denominators `≤ R` are `1/(2R²)`-separated modulo one. -/
theorem farey_sep {R d b d' b' : ℕ} (hd : 1 ≤ d) (hdR : d ≤ R) (hb : b < d) (hc : b.Coprime d)
    (hd' : 1 ≤ d') (hdR' : d' ≤ R) (hb' : b' < d') (hc' : b'.Coprime d')
    (hne : ¬(d = d' ∧ b = b')) :
    1 / (2 * (R : ℝ) ^ 2) ≤
      |(b : ℝ) / d - b' / d' - round ((b : ℝ) / d - b' / d')| := by
  set x : ℝ := (b : ℝ) / d - b' / d' with hx
  set m : ℤ := round x with hm
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hdpos' : (0 : ℝ) < d' := by exact_mod_cast hd'
  set N : ℤ := (b : ℤ) * d' - b' * d - m * d * d' with hN
  have hxN : (x - m) * (d * d') = N := by
    rw [hx, hN]; push_cast; field_simp
  have hN0 : N ≠ 0 := by
    intro h0
    have hxm : x = m := by
      have : (x - m) * (d * d') = 0 := by rw [hxN, h0]; simp
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h (by positivity)
    have hx1 : |x| < 1 := by
      have h1 : (b : ℝ) / d < 1 := by rw [div_lt_one hdpos]; exact_mod_cast hb
      have h2 : (b' : ℝ) / d' < 1 := by rw [div_lt_one hdpos']; exact_mod_cast hb'
      have h3 : 0 ≤ (b : ℝ) / d := by positivity
      have h4 : 0 ≤ (b' : ℝ) / d' := by positivity
      rw [abs_lt]; constructor <;> linarith
    have hm0 : m = 0 := by
      rw [hxm] at hx1
      have : |m| < 1 := by exact_mod_cast hx1
      exact Int.abs_lt_one_iff.mp this
    rw [hm0] at hxm
    simp only [Int.cast_zero] at hxm
    have hcross : b * d' = b' * d := by
      have : (b : ℝ) / d = b' / d' := by linarith
      rw [div_eq_div_iff hdpos.ne' hdpos'.ne'] at this
      exact_mod_cast this
    have h1 : d ∣ d' := by
      have : d ∣ b * d' := ⟨b', by rw [hcross]; ring⟩
      exact (Nat.Coprime.symm hc).dvd_of_dvd_mul_left this
    have h2 : d' ∣ d := by
      have : d' ∣ b' * d := ⟨b, by rw [← hcross]; ring⟩
      exact (Nat.Coprime.symm hc').dvd_of_dvd_mul_left this
    have hdd : d = d' := Nat.dvd_antisymm h1 h2
    subst hdd
    have : b = b' := by
      have := hcross
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    exact hne ⟨rfl, this⟩
  have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := by
    have : (1 : ℤ) ≤ |N| := Int.one_le_abs hN0
    exact_mod_cast this
  have hdd : (d : ℝ) * d' ≤ (R : ℝ) ^ 2 := by
    rw [sq]; exact mul_le_mul (by exact_mod_cast hdR) (by exact_mod_cast hdR')
      (by positivity) (by positivity)
  have hpos : (0 : ℝ) < d * d' := by positivity
  have habs : |x - m| = |(N : ℝ)| / (d * d') := by
    rw [← hxN, abs_mul, abs_of_pos hpos]; field_simp
  rw [habs]
  have hR : (0 : ℝ) < (R : ℝ) ^ 2 := lt_of_lt_of_le hpos hdd
  calc 1 / (2 * (R : ℝ) ^ 2) ≤ 1 / (d * d') := by
        rw [div_le_div_iff₀ (by positivity) hpos]; linarith
    _ ≤ |(N : ℝ)| / (d * d') := by
        rw [div_le_div_iff_of_pos_right hpos]; exact hN1

/-- The additive large sieve for the Farey fractions of order `R`. -/
theorem farey_large_sieve (R H : ℕ) (hR : 1 ≤ R) (a : ℕ → ℂ) :
    ∑ d ∈ Icc 1 R, ∑ b ∈ (range d).filter (fun b => b.Coprime d),
        ‖∑ n ∈ range H, a n *
          Complex.exp (2 * Real.pi * Complex.I * (((n : ℝ) : ℂ) * (((b : ℝ) / (d : ℝ) : ℝ) : ℂ)))‖ ^ 2
      ≤ (2 * (R : ℝ) ^ 2 + 13 * H) * ∑ n ∈ range H, ‖a n‖ ^ 2 := by
  set F : Finset (Σ _ : ℕ, ℕ) := (Icc 1 R).sigma (fun d => (range d).filter (fun b => b.Coprime d))
    with hF
  set e := F.equivFin
  set α : Fin F.card → ℝ := fun r => ((e.symm r).1.2 : ℝ) / (e.symm r).1.1 with hα
  have hδ : (0 : ℝ) < 1 / (2 * (R : ℝ) ^ 2) := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    positivity
  have hδ2 : 1 / (2 * (R : ℝ) ^ 2) ≤ 1 / 2 := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hsp : ∀ r s, r ≠ s → 1 / (2 * (R : ℝ) ^ 2) ≤ |α r - α s - round (α r - α s)| := by
    intro r s hrs
    have hp := (e.symm r).2
    have hq := (e.symm s).2
    simp only [hF, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hp hq
    refine farey_sep hp.1.1 hp.1.2 hp.2.1 hp.2.2 hq.1.1 hq.1.2 hq.2.1 hq.2.2 ?_
    rintro ⟨h1, h2⟩
    apply hrs
    apply e.symm.injective
    apply Subtype.ext
    exact Sigma.ext h1 (heq_of_eq h2)
  have hLS := LargeSieve.analytic_large_sieve (N := H) a hsp hδ hδ2
  rw [one_div, inv_inv] at hLS
  refine le_trans (le_of_eq ?_) hLS
  rw [Finset.sum_sigma']
  rw [← Finset.sum_coe_sort F]
  refine (Fintype.sum_equiv e.symm _ _ ?_).symm
  intro r
  rfl

/-- **Multiplicative large sieve.** -/
theorem multiplicative_large_sieve (R K H : ℕ) (hR : 1 ≤ R) (a : ℕ → ℂ) :
    ∑ d ∈ Icc 1 R, ((d : ℝ) / d.totient) *
        ∑ χ ∈ primChars d, ‖∑ n ∈ Ioc K (K + H), a n * χ n‖ ^ 2
      ≤ (2 * (R : ℝ) ^ 2 + 13 * H) * ∑ n ∈ Ioc K (K + H), ‖a n‖ ^ 2 := by
  set a' : ℕ → ℂ := fun j => a (K + 1 + j) with ha'
  have hshift : ∀ {M : Type} [AddCommMonoid M] (g : ℕ → M),
      ∑ n ∈ Ioc K (K + H), g n = ∑ j ∈ range H, g (K + 1 + j) := by
    intro M _ g
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range,
      show K + H + 1 - (K + 1) = H by omega]
  have hstep : ∀ d ∈ Icc 1 R, ((d : ℝ) / d.totient) *
      ∑ χ ∈ primChars d, ‖∑ n ∈ Ioc K (K + H), a n * χ n‖ ^ 2 ≤
      ∑ b ∈ (range d).filter (fun b => b.Coprime d),
        ‖∑ j ∈ range H, a' j *
          Complex.exp (2 * Real.pi * Complex.I * (((j : ℝ) : ℂ) * (((b : ℝ) / (d : ℝ) : ℝ) : ℂ)))‖ ^ 2 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have : NeZero d := ⟨by omega⟩
    have hphi : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have h := prim_gauss_bound d (Ioc K (K + H)) a
    rw [div_mul_eq_mul_div, div_le_iff₀ hphi, mul_comm _ (d.totient : ℝ)]
    refine h.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hshift]
    have : ∀ j : ℕ, a (K + 1 + j) *
        Complex.exp (2 * Real.pi * Complex.I * ((((K + 1 + j : ℕ) : ℝ) : ℂ) * (((b : ℝ) / (d : ℝ) : ℝ) : ℂ))) =
        Complex.exp (2 * Real.pi * Complex.I * ((((K + 1 : ℕ) : ℝ) : ℂ) * (((b : ℝ) / (d : ℝ) : ℝ) : ℂ))) *
          (a' j * Complex.exp (2 * Real.pi * Complex.I * (((j : ℝ) : ℂ) * (((b : ℝ) / (d : ℝ) : ℝ) : ℂ)))) := by
      intro j
      rw [show (a' j) = a (K + 1 + j) from rfl]
      rw [show ∀ (B C z : ℂ), Complex.exp B * (z * Complex.exp C) = z * Complex.exp (B + C) by
        intro B C z; rw [Complex.exp_add]; ring]
      congr 2
      push_cast
      ring
    simp_rw [this]
    rw [← Finset.mul_sum, norm_mul]
    have hexp : ‖Complex.exp (2 * Real.pi * Complex.I *
        ((((K + 1 : ℕ) : ℝ) : ℂ) * (((b : ℝ) / (d : ℝ) : ℝ) : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [hexp, one_mul]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [hshift (fun n => (‖a n‖ ^ 2 : ℝ))]
  exact farey_large_sieve R H hR a'

end ArtinPrimitiveRoots.BV
end

open ArtinPrimitiveRoots Finset in
theorem solution (R K H : ℕ) (hR : 1 ≤ R) (a : ℕ → ℂ) :
    ∑ d ∈ Icc 1 R, ((d : ℝ) / d.totient) *
        ∑ χ ∈ primChars d, ‖∑ n ∈ Ioc K (K + H), a n * χ n‖ ^ 2
      ≤ (2 * (R : ℝ) ^ 2 + 13 * H) * ∑ n ∈ Ioc K (K + H), ‖a n‖ ^ 2 :=
  ArtinPrimitiveRoots.BV.multiplicative_large_sieve R K H hR a
