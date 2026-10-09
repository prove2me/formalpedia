-- Prove2me | solution 1 for ArtinPrimitiveRoots.psi_bombieri_vinogradov
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T16:47:14.361365+00:00
-- url     : https://prove2.me/submissions/5cef7639-0a6a-4df5-bbd6-e9fdceda4360

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_psi_large_conductor_bound
import Theorems.Thm_ArtinPrimitiveRoots_psi_small_conductor_bound
import Theorems.Thm_ArtinPrimitiveRoots_psi_prime_number_theorem
import Definitions.Def_ArtinBV

section

end

section
/-!
# Discrete partial summation and bounds for character sums
-/

namespace ArtinPrimitiveRoots.BV

open Finset

end ArtinPrimitiveRoots.BV
end

section
/-!
# Elementary divisor-sum estimates
-/

namespace ArtinPrimitiveRoots.BV

open Finset

theorem conv_sum {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) (X : ℕ) :
    ∑ n ∈ Ioc 0 X, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2 =
      ∑ a ∈ Ioc 0 X, ∑ b ∈ Ioc 0 (X / a), F a b := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => ⟨p.2.1, p.2.2⟩) (fun p _ => ⟨p.1 * p.2, (p.1, p.2)⟩)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨n, a, b⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisorsAntidiagonal] at h ⊢
    obtain ⟨⟨hn0, hnX⟩, hab, -⟩ := h
    subst hab
    have ha : 0 < a := Nat.pos_of_mul_pos_right hn0
    have hb : 0 < b := Nat.pos_of_mul_pos_left hn0
    refine ⟨⟨ha, le_trans (Nat.le_mul_of_pos_right a hb) hnX⟩, hb, ?_⟩
    rw [Nat.le_div_iff_mul_le ha]
    linarith [mul_comm a b]
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisorsAntidiagonal] at h ⊢
    obtain ⟨⟨ha, haX⟩, hb, hbX⟩ := h
    rw [Nat.le_div_iff_mul_le ha] at hbX
    refine ⟨⟨Nat.mul_pos ha hb, by linarith [mul_comm a b]⟩, trivial, by positivity⟩
  · rintro ⟨n, a, b⟩ h
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at h
    obtain ⟨-, hab, -⟩ := h
    subst hab
    rfl
  · rintro ⟨a, b⟩ _
    rfl

/-- The harmonic sum over `(0, X]`. -/
theorem harm_le (X : ℕ) : ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) ≤ 1 + Real.log X := by
  have h := harmonic_le_one_add_log X
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have : Icc 1 X = Ioc 0 X := by ext i; simp; omega
  rw [this] at h
  simpa [one_div] using h

theorem harm_nonneg (X : ℕ) : 0 ≤ ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) :=
  Finset.sum_nonneg fun i _ => by positivity

/-- `n ≤ φ(n) d(n)`. -/
theorem le_totient_mul_card_divisors (n : ℕ) (hn : n ≠ 0) :
    n ≤ n.totient * n.divisors.card := by
  rw [Nat.totient_eq_prod_factorization hn, Nat.card_divisors hn, Finsupp.prod,
    Nat.support_factorization, ← Finset.prod_mul_distrib]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_le_prod' fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have he : 1 ≤ n.factorization p :=
    (Nat.Prime.factorization_pos_of_dvd hpp hn (Nat.dvd_of_mem_primeFactors hp))
  obtain ⟨k, hk⟩ : ∃ k, n.factorization p = k + 1 := ⟨n.factorization p - 1, by omega⟩
  rw [hk]
  have hp2 := hpp.two_le
  simp only [Nat.add_sub_cancel, pow_succ]
  rw [mul_assoc]
  refine Nat.mul_le_mul_left _ ?_
  have : p ≤ (p - 1) * 2 := by omega
  calc p ≤ (p - 1) * 2 := this
    _ ≤ (p - 1) * (k + 1 + 1) := Nat.mul_le_mul_left _ (by omega)

/-- `∑_{m ≤ Q} 1/φ(m) ≤ (1 + log Q)^2`. -/
theorem sum_inv_totient_le (Q : ℕ) :
    ∑ m ∈ Ioc 0 Q, (1 / (m.totient : ℝ)) ≤ (1 + Real.log Q) ^ 2 := by
  have h1 : ∀ m ∈ Ioc 0 Q, (1 / (m.totient : ℝ)) ≤
      ∑ x ∈ m.divisorsAntidiagonal, (1 / (x.1 : ℝ)) * (1 / (x.2 : ℝ)) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm0 : m ≠ 0 := hm.1.ne'
    have hcard : (m.divisorsAntidiagonal).card = m.divisors.card := by
      rw [← Nat.map_div_right_divisors, Finset.card_map]
    have hval : ∀ x ∈ m.divisorsAntidiagonal, (1 / (x.1 : ℝ)) * (1 / (x.2 : ℝ)) = 1 / m := by
      intro x hx
      rw [Nat.mem_divisorsAntidiagonal] at hx
      rw [one_div_mul_one_div, ← Nat.cast_mul, hx.1]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, hcard, nsmul_eq_mul]
    have ht : 0 < m.totient := Nat.totient_pos.mpr hm.1
    have key := le_totient_mul_card_divisors m hm0
    have key' : (m : ℝ) ≤ m.totient * m.divisors.card := by exact_mod_cast key
    rw [div_le_iff₀ (by exact_mod_cast ht)]
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm.1
    calc (1 : ℝ) = m * (1 / m) := by field_simp
      _ ≤ (m.totient * m.divisors.card) * (1 / m) :=
          mul_le_mul_of_nonneg_right key' (by positivity)
      _ = ↑(m.divisors.card) * (1 / ↑m) * ↑m.totient := by ring
  refine (Finset.sum_le_sum h1).trans ?_
  rw [conv_sum (fun a b => (1 / (a : ℝ)) * (1 / (b : ℝ))) Q]
  calc ∑ a ∈ Ioc 0 Q, ∑ b ∈ Ioc 0 (Q / a), (1 / (a : ℝ)) * (1 / (b : ℝ))
      ≤ ∑ a ∈ Ioc 0 Q, ∑ b ∈ Ioc 0 Q, (1 / (a : ℝ)) * (1 / (b : ℝ)) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ioc_subset_Ioc_right (Nat.div_le_self _ _)) (fun _ _ _ => by positivity)
    _ = (∑ i ∈ Ioc 0 Q, (1 / (i : ℝ))) ^ 2 := by rw [sq, Finset.sum_mul_sum]
    _ ≤ (1 + Real.log Q) ^ 2 := pow_le_pow_left₀ (harm_nonneg Q) (harm_le Q) 2

end ArtinPrimitiveRoots.BV
end

section
/-!
# A bilinear form estimate with a hyperbolic cut-off

An abstract consequence of a large-sieve inequality for a family of completely multiplicative
functions: the bilinear sum `∑_{mr ≤ X} a_m b_r χ(mr)` is controlled after cutting the
`m`-range into `K` blocks; the pairs near the hyperbola `mr = X` are handled by the large
sieve in the single variable `k = mr` on a short interval.
-/

namespace ArtinPrimitiveRoots.BV

open Finset

end ArtinPrimitiveRoots.BV
end

section
namespace ArtinPrimitiveRoots.BV

open Finset

section
variable {ι : Type*} (s : Finset ι) (w : ι → ℝ) (χ : ι → ℕ → ℂ)

end

end ArtinPrimitiveRoots.BV
end

section
namespace ArtinPrimitiveRoots.BV

open Finset

end ArtinPrimitiveRoots.BV
end

section
/-!
# Vaughan's identity and the resulting decomposition of `ψ(X, χ)`
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

end ArtinPrimitiveRoots.BV
end

section
/-!
# Type I bounds in Vaughan's decomposition
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

theorem log_le_of_mem {X n : ℕ} (hn : n ∈ Ioc 0 X) : Real.log n ≤ Real.log X := by
  rw [Finset.mem_Ioc] at hn
  exact Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)

end ArtinPrimitiveRoots.BV
end

section
/-!
# The Type II sums over primitive characters: dyadic decomposition
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

theorem card_primChars_le (d : ℕ) [NeZero d] : ((primChars d).card : ℝ) ≤ d.totient := by
  have h1 : (primChars d).card ≤ Fintype.card (DirichletCharacter ℂ d) := by
    rw [primChars]; exact Finset.card_filter_le _ _
  have h2 : Fintype.card (DirichletCharacter ℂ d) = d.totient := by
    rw [Fintype.card_eq_nat_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
  exact_mod_cast h2 ▸ h1

theorem sum_dyadic {β : Type*} [AddCommMonoid β] (F : ℕ → β) (U : ℕ) (I : ℕ) :
    ∑ m ∈ Ioc U (U * 2 ^ I), F m = ∑ i ∈ range I, ∑ m ∈ Ioc (U * 2 ^ i) (2 * (U * 2 ^ i)), F m := by
  induction I with
  | zero => simp
  | succ I ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Ioc_consecutive _ (by
      calc U = U * 1 := (mul_one U).symm
        _ ≤ U * 2 ^ I := Nat.mul_le_mul_left _ (Nat.one_le_two_pow)) (by omega),
      show U * 2 ^ (I + 1) = 2 * (U * 2 ^ I) by ring]

end ArtinPrimitiveRoots.BV
end

section
/-!
# Reduction of `ψ(X; q, a)` to primitive characters
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt

/-- The contribution of `n` not coprime to `q`. -/
noncomputable def nuX (X q : ℕ) : ℝ := ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ n.Coprime q), Λ n

theorem nuX_nonneg (X q : ℕ) : 0 ≤ nuX X q :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- The nontrivial characters modulo `q`. -/
noncomputable def nontrivChars (q : ℕ) : Finset (DirichletCharacter ℂ q) := by
  classical exact univ.filter (· ≠ 1)

theorem mem_nontrivChars {q : ℕ} (χ : DirichletCharacter ℂ q) : χ ∈ nontrivChars q ↔ χ ≠ 1 := by
  classical
  simp [nontrivChars]

theorem prim_apply_nat {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) (h : n.Coprime q) :
    χ.primitiveCharacter n = χ n := by
  have := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.mpr h)
  simpa using this

theorem char_apply_noncoprime {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) (h : ¬ n.Coprime q) :
    χ n = 0 := MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])

theorem norm_psiChar_sub_prim {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) :
    ‖psiChar χ X - psiChar χ.primitiveCharacter X‖ ≤ nuX X q := by
  rw [psiChar, psiChar, ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not (Ioc 0 X) (fun n => n.Coprime q)]
  have h0 : ∑ n ∈ (Ioc 0 X).filter (fun n => n.Coprime q),
      ((Λ n : ℂ) * χ n - (Λ n : ℂ) * χ.primitiveCharacter n) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_filter] at hn
    rw [prim_apply_nat χ n hn.2, sub_self]
  rw [h0, zero_add, nuX]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  rw [char_apply_noncoprime χ n hn.2, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
    (DirichletCharacter.norm_le_one _ _)

theorem psiChar_one (q X : ℕ) :
    psiChar (1 : DirichletCharacter ℂ q) X = (((∑ n ∈ Ioc 0 X, Λ n) - nuX X q : ℝ) : ℂ) := by
  rw [psiChar, nuX, ← Finset.sum_filter_add_sum_filter_not (Ioc 0 X) (fun n => n.Coprime q),
    ← Finset.sum_filter_add_sum_filter_not (Ioc 0 X) (fun n => n.Coprime q)]
  have h1 : ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ n.Coprime q),
      (Λ n : ℂ) * (1 : DirichletCharacter ℂ q) n = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_filter] at hn
    rw [char_apply_noncoprime _ n hn.2, mul_zero]
  have h2 : ∑ n ∈ (Ioc 0 X).filter (fun n => n.Coprime q),
      (Λ n : ℂ) * (1 : DirichletCharacter ℂ q) n =
        ∑ n ∈ (Ioc 0 X).filter (fun n => n.Coprime q), (Λ n : ℂ) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_filter] at hn
    rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn.2), mul_one]
  rw [h1, h2]
  push_cast
  ring

theorem psiAP_eq (q a X : ℕ) [NeZero q] (ha : a.Coprime q) :
    (q.totient : ℂ) * (psiAP X q a : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * psiChar χ X := by
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  simp_rw [psiChar, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ n ∈ Ioc 0 X, ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * ((Λ n : ℂ) * χ n) =
      (Λ n : ℂ) * (if n ≡ a [MOD q] then (q.totient : ℂ) else 0) := by
    intro n _
    have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (n : ZMod q)
    rw [show (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * ((Λ n : ℂ) * χ n)) =
      (Λ n : ℂ) * ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * χ n by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun χ _ => by ring), h]
    congr 2
    simp only [ZMod.natCast_eq_natCast_iff]
    exact propext ⟨Nat.ModEq.symm, Nat.ModEq.symm⟩
  rw [Finset.sum_congr rfl this, psiAP]
  push_cast
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> ring

/-- **Orthogonality**: `|ψ(X;q,a) - X/φ(q)|` in terms of primitive characters. -/
theorem abs_psiAP_sub_le (q a X : ℕ) (hq : 1 ≤ q) (ha : a.Coprime q) :
    |psiAP X q a - X / q.totient| ≤
      |(∑ n ∈ Ioc 0 X, Λ n) - X| / q.totient + 2 * nuX X q +
        (1 / (q.totient : ℝ)) * ∑ χ ∈ nontrivChars q,
          ‖psiChar χ.primitiveCharacter X‖ := by
  have : NeZero q := ⟨by omega⟩
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hu' : IsUnit ((a : ZMod q)⁻¹) := by
    rw [← hu.unit_spec, ZMod.inv_coe_unit]; exact Units.isUnit _
  set ν := nuX X q with hν
  have hν0 : 0 ≤ ν := nuX_nonneg X q
  set ψX := ∑ n ∈ Ioc 0 X, Λ n with hψX
  -- the identity
  have hid : Complex.ofReal ((q.totient : ℝ) * (psiAP X q a - X / q.totient)) =
      ((ψX - ν - X : ℝ) : ℂ) + ∑ χ ∈ nontrivChars q,
        χ ((a : ZMod q)⁻¹) * psiChar χ X := by
    have h1 := psiAP_eq q a X ha
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)),
      MulChar.one_apply hu', one_mul, psiChar_one] at h1
    have e : (univ : Finset (DirichletCharacter ℂ q)).erase 1 = nontrivChars q := by
      ext χ; rw [mem_nontrivChars]; simp
    rw [e, ← hψX, ← hν] at h1
    push_cast
    rw [mul_sub, h1, mul_div_cancel₀ _ (by exact_mod_cast hφ.ne')]
    push_cast
    ring
  -- bounding the character terms
  have hchar : ‖∑ χ ∈ nontrivChars q,
      χ ((a : ZMod q)⁻¹) * psiChar χ X‖ ≤
      ∑ χ ∈ nontrivChars q,
        ‖psiChar χ.primitiveCharacter X‖ + q.totient * ν := by
    refine (norm_sum_le _ _).trans ?_
    have hcard : ((nontrivChars q).card : ℝ) ≤ q.totient := by
      have h1 : (nontrivChars q).card ≤ (univ : Finset (DirichletCharacter ℂ q)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      have h2 : (univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
        rw [Finset.card_univ, Fintype.card_eq_nat_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      exact_mod_cast h2 ▸ h1
    calc ∑ χ ∈ nontrivChars q,
          ‖χ ((a : ZMod q)⁻¹) * psiChar χ X‖
        ≤ ∑ χ ∈ nontrivChars q,
          (‖psiChar χ.primitiveCharacter X‖ + ν) := by
          refine Finset.sum_le_sum fun χ _ => ?_
          rw [norm_mul]
          have h1 := DirichletCharacter.norm_le_one χ ((a : ZMod q)⁻¹)
          have h2 : ‖psiChar χ X‖ ≤ ‖psiChar χ.primitiveCharacter X‖ + ν := by
            have := norm_psiChar_sub_prim χ X
            have h3 := norm_sub_norm_le (psiChar χ X) (psiChar χ.primitiveCharacter X)
            linarith
          calc ‖χ ((a : ZMod q)⁻¹)‖ * ‖psiChar χ X‖ ≤ 1 * ‖psiChar χ X‖ :=
                mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
            _ ≤ _ := by rw [one_mul]; exact h2
      _ = ∑ χ ∈ nontrivChars q,
            ‖psiChar χ.primitiveCharacter X‖ +
            ((nontrivChars q).card : ℝ) * ν := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr
  have hmain : (q.totient : ℝ) * |psiAP X q a - X / q.totient| ≤
      |ψX - X| + ν + (∑ χ ∈ nontrivChars q,
        ‖psiChar χ.primitiveCharacter X‖ + q.totient * ν) := by
    have := congrArg (‖·‖) hid
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hφ] at this
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add ?_ hchar)
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc |ψX - ν - X| = |(ψX - X) - ν| := by ring_nf
      _ ≤ |ψX - X| + |ν| := abs_sub _ _
      _ = |ψX - X| + ν := by rw [abs_of_nonneg hν0]
  have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  rw [← mul_le_mul_iff_of_pos_left hφ]
  set S := ∑ χ ∈ nontrivChars q,
    ‖psiChar χ.primitiveCharacter X‖ with hS
  have e : (q.totient : ℝ) * (|ψX - X| / q.totient + 2 * ν + (1 / (q.totient : ℝ)) * S) =
      |ψX - X| + 2 * q.totient * ν + S := by
    field_simp
  rw [e]
  have : ν ≤ q.totient * ν := le_mul_of_one_le_left hν0 hφ1
  linarith

end ArtinPrimitiveRoots.BV
end

section
/-!
# Prime powers dividing `q`, and regrouping by conductor
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt

theorem nuX_le (X q : ℕ) (hq : 1 ≤ q) : nuX X q ≤ q * (Nat.log 2 X) * Real.log X := by
  rw [nuX]
  set S := (Ioc 0 X).filter (fun n => ¬ n.Coprime q)
  rw [← Finset.sum_filter_ne_zero]
  set S' := S.filter (fun n => Λ n ≠ 0)
  have hsub : S' ⊆ (q.primeFactors ×ˢ Icc 1 (Nat.log 2 X)).image (fun pk => pk.1 ^ pk.2) := by
    intro n hn
    simp only [S', S, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨⟨hn0, hnX⟩, hcop⟩, hΛ⟩ := hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_Icc, Prod.exists]
    refine ⟨p, k, ⟨?_, hk, ?_⟩, rfl⟩
    · rw [Nat.coprime_pow_left_iff hk, hp.coprime_iff_not_dvd, not_not] at hcop
      exact Nat.mem_primeFactors.mpr ⟨hp, hcop, by omega⟩
    · have : 2 ^ k ≤ X := le_trans (Nat.pow_le_pow_left hp.two_le k) hnX
      exact Nat.le_log_of_pow_le (by norm_num) this
  have hcard : (S'.card : ℝ) ≤ q * Nat.log 2 X := by
    have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_product, Nat.card_Icc] at h1
    have h2 : q.primeFactors.card ≤ q := by
      calc q.primeFactors.card ≤ (Icc 1 q).card := by
            refine Finset.card_le_card fun p hp => ?_
            have := Nat.mem_primeFactors.mp hp
            simp only [Finset.mem_Icc]
            exact ⟨this.1.one_lt.le, Nat.le_of_dvd (by omega) this.2.1⟩
        _ = q := by simp
    have h3 : S'.card ≤ q * Nat.log 2 X := by
      calc S'.card ≤ q.primeFactors.card * (Nat.log 2 X + 1 - 1) := h1
        _ ≤ q * Nat.log 2 X := by
            rw [Nat.add_sub_cancel]; exact Nat.mul_le_mul_right _ h2
    exact_mod_cast h3
  calc ∑ n ∈ S', Λ n ≤ ∑ n ∈ S', Real.log X := by
        refine Finset.sum_le_sum fun n hn => ?_
        simp only [S', S, Finset.mem_filter] at hn
        exact ArithmeticFunction.vonMangoldt_le_log.trans (log_le_of_mem hn.1.1)
    _ = S'.card * Real.log X := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ q * Nat.log 2 X * Real.log X :=
        mul_le_mul_of_nonneg_right hcard (Real.log_natCast_nonneg X)

theorem heq_apply {d1 d2 : ℕ} (h : d1 = d2) {f1 : DirichletCharacter ℂ d1}
    {f2 : DirichletCharacter ℂ d2} (hf : HEq f1 f2) (n : ℕ) : f1 n = f2 n := by
  subst h; rw [eq_of_heq hf]

/-- Nontrivial characters mod `q` inject into primitive characters of conductor `d ∣ q`, `d ≥ 2`. -/
theorem sum_nontriv_le (q : ℕ) (hq : 1 ≤ q) (F : (Σ d : ℕ, DirichletCharacter ℂ d) → ℝ)
    (hF : ∀ p, 0 ≤ F p) :
    ∑ χ ∈ nontrivChars q, F ⟨χ.conductor, χ.primitiveCharacter⟩ ≤
      ∑ d ∈ q.divisors.filter (2 ≤ ·), ∑ χ' ∈ primChars d, F ⟨d, χ'⟩ := by
  classical
  have : NeZero q := ⟨by omega⟩
  set φ : DirichletCharacter ℂ q → (Σ d : ℕ, DirichletCharacter ℂ d) :=
    fun χ => ⟨χ.conductor, χ.primitiveCharacter⟩ with hφ
  have hinj : Set.InjOn φ ↑(nontrivChars q) := by
    intro χ1 _ χ2 _ h
    simp only [hφ, Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    apply MulChar.ext
    intro u
    have hc := ZMod.val_coe_unit_coprime u
    have e : ((u : ZMod q).val : ZMod q) = (u : ZMod q) := ZMod.natCast_zmod_val _
    rw [← e, ← prim_apply_nat χ1 _ hc, ← prim_apply_nat χ2 _ hc]
    exact heq_apply h1 h2 _
  rw [Finset.sum_sigma']
  have himg : ∑ χ ∈ nontrivChars q, F (φ χ) = ∑ p ∈ (nontrivChars q).image φ, F p :=
    (Finset.sum_image hinj).symm
  rw [show ∑ χ ∈ nontrivChars q, F ⟨χ.conductor, χ.primitiveCharacter⟩ =
    ∑ χ ∈ nontrivChars q, F (φ χ) from rfl, himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hF p)
  intro p hp
  simp only [Finset.mem_image] at hp
  obtain ⟨χ, hχ, rfl⟩ := hp
  rw [mem_nontrivChars] at hχ
  simp only [hφ, Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors]
  refine ⟨⟨⟨χ.conductor_dvd_level, by omega⟩, ?_⟩, ?_⟩
  · have h0 := χ.conductor_ne_zero
    have h1 : χ.conductor ≠ 1 := fun h => hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
    omega
  · simp only [primChars, Finset.mem_filter, Finset.mem_univ, true_and]
    exact χ.primitiveCharacter_isPrimitive

end ArtinPrimitiveRoots.BV
end

section
/-!
# Regrouping the moduli by conductor
-/

namespace ArtinPrimitiveRoots.BV

open Finset

theorem sum_multiples_inv_totient (Q d : ℕ) (hd : 1 ≤ d) :
    ∑ q ∈ (Icc 1 Q).filter (d ∣ ·), (1 / (q.totient : ℝ)) ≤
      (1 / (d.totient : ℝ)) * ∑ m ∈ Ioc 0 Q, (1 / (m.totient : ℝ)) := by
  have hφd : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have h1 : ∀ q ∈ (Icc 1 Q).filter (d ∣ ·), (1 / (q.totient : ℝ)) ≤
      (1 / (d.totient : ℝ)) * (1 / ((q / d).totient : ℝ)) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, _⟩, hdq⟩ := hq
    have hqd : 1 ≤ q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdq) (by omega)
    have hφm : (0 : ℝ) < (q / d).totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hsup := Nat.totient_super_multiplicative d (q / d)
    rw [Nat.mul_div_cancel' hdq] at hsup
    have hsup' : (d.totient : ℝ) * (q / d).totient ≤ q.totient := by exact_mod_cast hsup
    have hφq : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    rw [one_div_mul_one_div, one_div_le_one_div hφq (by positivity)]
    exact hsup'
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hinj : Set.InjOn (fun q => q / d) ↑((Icc 1 Q).filter (d ∣ ·)) := by
    intro a ha b hb h
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
    simp only at h
    rw [← Nat.mul_div_cancel' ha.2, ← Nat.mul_div_cancel' hb.2, h]
  rw [← Finset.sum_image (f := fun m => 1 / (m.totient : ℝ)) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro m hm
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨q, ⟨⟨hq1, hqQ⟩, hdq⟩, rfl⟩ := hm
  simp only [Finset.mem_Ioc]
  exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdq) (by omega),
    (Nat.div_le_self q d).trans hqQ⟩

theorem regroup (Q : ℕ) (G : ℕ → ℝ) (hG : ∀ d, 0 ≤ G d) :
    ∑ q ∈ Icc 1 Q, (1 / (q.totient : ℝ)) * ∑ d ∈ q.divisors.filter (2 ≤ ·), G d ≤
      (∑ m ∈ Ioc 0 Q, (1 / (m.totient : ℝ))) *
        ∑ d ∈ Icc 2 Q, (1 / (d.totient : ℝ)) * G d := by
  have h1 : ∀ q ∈ Icc 1 Q, (1 / (q.totient : ℝ)) * ∑ d ∈ q.divisors.filter (2 ≤ ·), G d =
      ∑ d ∈ Icc 2 Q, (if d ∣ q then (1 / (q.totient : ℝ)) * G d else 0) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    rw [Finset.mul_sum, ← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdq, _⟩, h2⟩; exact ⟨⟨h2, (Nat.le_of_dvd (by omega) hdq).trans hq.2⟩, hdq⟩
    · rintro ⟨⟨h2, _⟩, hdq⟩; exact ⟨⟨hdq, by omega⟩, h2⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  have e : ∑ q ∈ Icc 1 Q, (if d ∣ q then (1 / (q.totient : ℝ)) * G d else 0) =
      (∑ q ∈ (Icc 1 Q).filter (d ∣ ·), (1 / (q.totient : ℝ))) * G d := by
    rw [Finset.sum_mul, Finset.sum_filter]
  rw [e]
  calc (∑ q ∈ (Icc 1 Q).filter (d ∣ ·), (1 / (q.totient : ℝ))) * G d
      ≤ ((1 / (d.totient : ℝ)) * ∑ m ∈ Ioc 0 Q, (1 / (m.totient : ℝ))) * G d :=
        mul_le_mul_of_nonneg_right (sum_multiples_inv_totient Q d (by omega)) (hG d)
    _ = _ := by ring

end ArtinPrimitiveRoots.BV
end

section
/-!
# Elementary asymptotic inequalities
-/

namespace ArtinPrimitiveRoots.BV

open Real

/-- Powers of `2 + log x` are dominated by any power of `x`. -/
theorem polylog_le (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → (2 + Real.log x) ^ a ≤ C * x ^ ε := by
  set δ := ε / (a + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨(2 + 1 / δ) ^ a, by positivity, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hxδ : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ0.le
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0 hδ0
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : 2 + Real.log x ≤ (2 + 1 / δ) * x ^ δ := by
    have : x ^ δ / δ = 1 / δ * x ^ δ := by ring
    nlinarith
  calc (2 + Real.log x) ^ a ≤ ((2 + 1 / δ) * x ^ δ) ^ a :=
        Real.rpow_le_rpow (by positivity) h1 ha
    _ = (2 + 1 / δ) ^ a * x ^ (δ * a) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hx0]
    _ ≤ (2 + 1 / δ) ^ a * x ^ ε := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ?_) (by positivity)
        rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

theorem log_two_gt : (0.69 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

theorem ell_le_four_log {x : ℝ} (hx : 2 ≤ x) : 2 + Real.log x ≤ 4 * Real.log x := by
  have h : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have := log_two_gt
  linarith

theorem log_pos_of_two_le {x : ℝ} (hx : 2 ≤ x) : 0.69 < Real.log x := by
  have h : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have := log_two_gt
  linarith

/-- `⌊log₂ X⌋ + 1 ≤ 2 (2 + log X)`. -/
theorem natLog_le (X : ℕ) (hX : 1 ≤ X) : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 2 * (2 + Real.log X) := by
  have h1 : 2 ^ Nat.log 2 X ≤ X := Nat.pow_log_le_self 2 (by omega)
  have h2 : (Nat.log 2 X : ℝ) * Real.log 2 ≤ Real.log X := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h1)
  have h3 := log_two_gt
  have h4 : (Nat.log 2 X : ℝ) ≤ Real.log X / 0.69 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [Real.log_natCast_nonneg X, (Nat.cast_nonneg (Nat.log 2 X) : (0:ℝ) ≤ _)]
  have h0 := Real.log_natCast_nonneg X
  have h5 : Real.log X / 0.69 ≤ 2 * Real.log X := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  push_cast
  linarith

end ArtinPrimitiveRoots.BV
end

section
/-!
# All primitive characters of conductor up to `X^{1/2-η}`
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real

theorem prim_ne_one {d : ℕ} (hd : 2 ≤ d) (χ : DirichletCharacter ℂ d) (hχ : χ ∈ primChars d) :
    χ ≠ 1 := by
  have : NeZero d := ⟨by omega⟩
  intro h1
  simp only [primChars, Finset.mem_filter, Finset.mem_univ, true_and] at hχ
  rw [h1, DirichletCharacter.conductor_one] at hχ
  omega

theorem conductor_sum_bound (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∑ d ∈ Icc 2 ⌊(X : ℝ) ^ (1 / 2 - η)⌋₊,
          (1 / (d.totient : ℝ)) * ∑ χ ∈ primChars d, ‖psiChar χ X‖ ≤
        C * (X * Real.log X ^ (-A)) := by
  obtain ⟨B, hB⟩ : ∃ B, B = A + 5 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; linarith
  obtain ⟨Cs, hCs⟩ := psi_small_conductor_bound (A + B) B (by linarith) hB0
  obtain ⟨Cl, hCl⟩ := psi_large_conductor_bound (A + 1) η (by linarith) hη
  set Cs' := max Cs 0
  set Cl' := max Cl 0
  have hCs'0 : 0 ≤ Cs' := le_max_right _ _
  have hCl'0 : 0 ≤ Cl' := le_max_right _ _
  refine ⟨Cs' + 24 * Cl', by positivity, fun X hX => ?_⟩
  have hx2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : (0 : ℝ) < X := by linarith
  set L := Real.log X with hLdef
  have hL69 : 0.69 < L := log_pos_of_two_le hx2
  have hL0 : 0 < L := by linarith
  have hℓ4 : 2 + L ≤ 4 * L := ell_le_four_log hx2
  set Q := ⌊(X : ℝ) ^ (1 / 2 - η)⌋₊ with hQdef
  have hQX : (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 - η) := Nat.floor_le (by positivity)
  have hQX' : Q ≤ X := by
    have : (X : ℝ) ^ (1 / 2 - η) ≤ X := by
      calc (X : ℝ) ^ (1 / 2 - η) ≤ (X : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = X := Real.rpow_one _
    exact_mod_cast hQX.trans this
  set f : ℕ → ℝ := fun d => (1 / (d.totient : ℝ)) * ∑ χ ∈ primChars d, ‖psiChar χ X‖ with hf
  have hf0 : ∀ d, 0 ≤ f d := fun d => by positivity
  set Q1 := max 1 ⌊L ^ B⌋₊ with hQ1
  have hQ11 : 1 ≤ Q1 := le_max_left _ _
  have hQ1L : (L ^ B) / 2 ≤ Q1 := by
    rcases Nat.lt_or_ge ⌊L ^ B⌋₊ 1 with h | h
    · have : L ^ B < 1 := by
        have := Nat.lt_one_iff.mp h
        rw [Nat.floor_eq_zero] at this; exact this
      have : (1 : ℝ) ≤ Q1 := by exact_mod_cast hQ11
      linarith
    · have h1 : L ^ B < ⌊L ^ B⌋₊ + 1 := Nat.lt_floor_add_one _
      have h2 : (1 : ℝ) ≤ ⌊L ^ B⌋₊ := by exact_mod_cast h
      have h3 : ((⌊L ^ B⌋₊ : ℕ) : ℝ) ≤ Q1 := by exact_mod_cast le_max_right 1 ⌊L ^ B⌋₊
      linarith
  -- splitting
  have hsplit : ∑ d ∈ Icc 2 Q, f d ≤ ∑ d ∈ Icc 2 Q1, f d + ∑ d ∈ Ioc Q1 Q, f d := by
    rw [← Finset.sum_union]
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => hf0 d)
      intro d hd
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc] at hd ⊢
      omega
    · rw [Finset.disjoint_left]
      intro d h1 h2
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
      omega
  -- small conductors
  have hsmall : ∑ d ∈ Icc 2 Q1, f d ≤ Cs' * (X * L ^ (-A)) := by
    have hpt : ∀ d ∈ Icc 2 Q1, f d ≤ Cs' * (X * L ^ (-(A + B))) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have : NeZero d := ⟨by omega⟩
      have hdQ : d ≤ ⌊L ^ B⌋₊ := by
        rcases Nat.lt_or_ge ⌊L ^ B⌋₊ 1 with h | h
        · exfalso; have : Q1 = 1 := by rw [hQ1]; omega
          omega
        · have : Q1 = ⌊L ^ B⌋₊ := by rw [hQ1]; omega
          omega
      have hdL : (d : ℝ) ≤ L ^ B := (Nat.le_floor_iff (by positivity)).mp hdQ
      have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
      have hχ : ∀ χ ∈ primChars d, ‖psiChar χ X‖ ≤ Cs' * (X * L ^ (-(A + B))) := by
        intro χ hχ
        refine (hCs X hX d (by omega) hdL χ (prim_ne_one hd.1 χ hχ)).trans ?_
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      calc f d ≤ (1 / (d.totient : ℝ)) * ∑ χ ∈ primChars d, Cs' * (X * L ^ (-(A + B))) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hχ) (by positivity)
        _ = ((primChars d).card / (d.totient : ℝ)) * (Cs' * (X * L ^ (-(A + B)))) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 1 * (Cs' * (X * L ^ (-(A + B)))) :=
            mul_le_mul_of_nonneg_right ((div_le_one hφ).mpr (card_primChars_le d)) (by positivity)
        _ = _ := one_mul _
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hcard : ((Q1 + 1 - 2 : ℕ) : ℝ) ≤ L ^ B := by
      have : Q1 + 1 - 2 ≤ ⌊L ^ B⌋₊ := by rw [hQ1]; omega
      exact ((Nat.cast_le.mpr this).trans (Nat.floor_le (by positivity)))
    have e : L ^ B * L ^ (-(A + B)) = L ^ (-A) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    calc ((Q1 + 1 - 2 : ℕ) : ℝ) * (Cs' * (X * L ^ (-(A + B))))
        ≤ L ^ B * (Cs' * (X * L ^ (-(A + B)))) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = Cs' * (X * (L ^ B * L ^ (-(A + B)))) := by ring
      _ = Cs' * (X * L ^ (-A)) := by rw [e]
  -- large conductors
  have hlarge : ∑ d ∈ Ioc Q1 Q, f d ≤ 24 * Cl' * (X * L ^ (-A)) := by
    set J := Nat.log 2 Q + 1 with hJ
    set F : ℕ → ℝ := fun d => if d ≤ Q then f d else 0 with hF
    have hQJ : Q ≤ Q1 * 2 ^ J := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) Q
      calc Q ≤ 2 ^ J := this.le
        _ ≤ Q1 * 2 ^ J := Nat.le_mul_of_pos_left _ (by omega)
    have h1 : ∑ d ∈ Ioc Q1 Q, f d = ∑ d ∈ Ioc Q1 (Q1 * 2 ^ J), F d := by
      have e : ∑ d ∈ Ioc Q1 Q, f d = ∑ d ∈ Ioc Q1 Q, F d := by
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [Finset.mem_Ioc] at hd
        simp only [hF]; rw [if_pos hd.2]
      rw [e]
      refine Finset.sum_subset (Finset.Ioc_subset_Ioc_right hQJ) fun d hd hdn => ?_
      simp only [Finset.mem_Ioc, not_and, not_le] at hd hdn
      simp only [hF]; rw [if_neg (by have := hdn hd.1; omega)]
    rw [h1, sum_dyadic F Q1 J]
    set M : ℝ := Cl' * X * (L ^ 4 / Q1 + L ^ (-(A + 1))) with hM
    have hM0 : 0 ≤ M := by positivity
    have hblock : ∀ j ∈ range J, ∑ d ∈ Ioc (Q1 * 2 ^ j) (2 * (Q1 * 2 ^ j)), F d ≤ M := by
      intro j _
      by_cases hR : Q1 * 2 ^ j ≤ Q
      · have hR1 : 1 ≤ Q1 * 2 ^ j := Nat.mul_pos (by omega) (by positivity)
        have hRX : ((Q1 * 2 ^ j : ℕ) : ℝ) ≤ (X : ℝ) ^ (1 / 2 - η) :=
          (Nat.cast_le.mpr hR).trans hQX
        have hb := hCl X hX (Q1 * 2 ^ j) hR1 hRX
        have hFf : ∑ d ∈ Ioc (Q1 * 2 ^ j) (2 * (Q1 * 2 ^ j)), F d ≤
            ∑ d ∈ Ioc (Q1 * 2 ^ j) (2 * (Q1 * 2 ^ j)), f d := by
          refine Finset.sum_le_sum fun d _ => ?_
          simp only [hF]; split_ifs
          · exact le_rfl
          · exact hf0 d
        refine hFf.trans (hb.trans ?_)
        have hQ1R : (Q1 : ℝ) ≤ ((Q1 * 2 ^ j : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_mul_of_pos_right Q1 (by positivity)
        have hQ10 : (0 : ℝ) < Q1 := by exact_mod_cast hQ11
        have h4 : L ^ 4 / ((Q1 * 2 ^ j : ℕ) : ℝ) ≤ L ^ 4 / Q1 :=
          div_le_div_of_nonneg_left (by positivity) hQ10 hQ1R
        have h5 : 0 ≤ L ^ 4 / ((Q1 * 2 ^ j : ℕ) : ℝ) + L ^ (-(A + 1)) := by positivity
        calc Cl * X * (L ^ 4 / ((Q1 * 2 ^ j : ℕ) : ℝ) + L ^ (-(A + 1)))
            ≤ Cl' * X * (L ^ 4 / ((Q1 * 2 ^ j : ℕ) : ℝ) + L ^ (-(A + 1))) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
                hx0.le) h5
          _ ≤ M := by rw [hM]; gcongr
      · push Not at hR
        have : ∑ d ∈ Ioc (Q1 * 2 ^ j) (2 * (Q1 * 2 ^ j)), F d = 0 := by
          refine Finset.sum_eq_zero fun d hd => ?_
          rw [Finset.mem_Ioc] at hd
          simp only [hF]; rw [if_neg (by omega)]
        rw [this]; exact hM0
    refine (Finset.sum_le_sum hblock).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hJL : (J : ℝ) ≤ 8 * L := by
      have h1 : J ≤ Nat.log 2 X + 1 := by rw [hJ]; exact Nat.succ_le_succ (Nat.log_mono_right hQX')
      have h2 := natLog_le X (by omega)
      have h3 : (J : ℝ) ≤ ((Nat.log 2 X + 1 : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    have hQ1' : L ^ 4 / Q1 ≤ 2 * (L ^ 4 / L ^ B) := by
      have hQ10 : (0 : ℝ) < Q1 := by exact_mod_cast hQ11
      rw [div_le_iff₀ hQ10]
      have : 0 < L ^ B := by positivity
      rw [mul_comm, ← mul_assoc, ← mul_div_assoc, le_div_iff₀ this]
      nlinarith [pow_pos hL0 4]
    have e1 : L * (L ^ 4 / L ^ B) = L ^ (-A) := by
      rw [← Real.rpow_natCast, mul_div_assoc', ← Real.rpow_one_add' hL0.le (by norm_num),
        ← Real.rpow_sub hL0]
      congr 1; rw [hB]; push_cast; ring
    have e2 : L * L ^ (-(A + 1)) = L ^ (-A) := by
      rw [← Real.rpow_one_add' hL0.le (by linarith)]; congr 1; ring
    calc (J : ℝ) * M ≤ 8 * L * M := mul_le_mul_of_nonneg_right hJL hM0
      _ = 8 * Cl' * X * (L * (L ^ 4 / Q1) + L * L ^ (-(A + 1))) := by rw [hM]; ring
      _ ≤ 8 * Cl' * X * (L * (2 * (L ^ 4 / L ^ B)) + L * L ^ (-(A + 1))) := by gcongr
      _ = 8 * Cl' * X * (2 * (L * (L ^ 4 / L ^ B)) + L * L ^ (-(A + 1))) := by ring
      _ = 24 * Cl' * (X * L ^ (-A)) := by rw [e1, e2]; ring
  calc ∑ d ∈ Icc 2 Q, f d ≤ ∑ d ∈ Icc 2 Q1, f d + ∑ d ∈ Ioc Q1 Q, f d := hsplit
    _ ≤ Cs' * (X * L ^ (-A)) + 24 * Cl' * (X * L ^ (-A)) := add_le_add hsmall hlarge
    _ = (Cs' + 24 * Cl') * (X * L ^ (-A)) := by ring

end ArtinPrimitiveRoots.BV
end

section
/-!
# Bombieri–Vinogradov for `ψ`
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

/-- **Bombieri–Vinogradov for `ψ`** at a single point, with one residue class per modulus. -/
theorem psi_bombieri_vinogradov (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
      ∑ q ∈ Icc 1 ⌊(X : ℝ) ^ (1 / 2 - η)⌋₊, |psiAP X q (a q) - X / q.totient|
        ≤ C * (X * log X ^ (-A)) := by
  obtain ⟨Cp, hCp⟩ := psi_prime_number_theorem (A + 2) (by linarith)
  obtain ⟨Cc, hCc0, hCc⟩ := conductor_sum_bound (A + 2) η (by linarith) hη
  obtain ⟨C0, hC00, hC0⟩ := polylog_le (A + 2) (2 * η) (by linarith) (by linarith)
  set Cp' := max Cp 0
  have hCp'0 : 0 ≤ Cp' := le_max_right _ _
  refine ⟨16 * Cp' + 4 * C0 + 16 * Cc, fun X hX a ha => ?_⟩
  have hx2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : (0 : ℝ) < X := by linarith
  set L := Real.log X with hLdef
  have hL69 : 0.69 < L := log_pos_of_two_le hx2
  have hL0 : 0 < L := by linarith
  have hℓ4 : 2 + L ≤ 4 * L := ell_le_four_log hx2
  set Q := ⌊(X : ℝ) ^ (1 / 2 - η)⌋₊ with hQdef
  have hQX : (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 - η) := Nat.floor_le (by positivity)
  have hQX' : Q ≤ X := by
    have : (X : ℝ) ^ (1 / 2 - η) ≤ X := by
      calc (X : ℝ) ^ (1 / 2 - η) ≤ (X : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = X := Real.rpow_one _
    exact_mod_cast hQX.trans this
  set ψX := ∑ n ∈ Ioc 0 X, Λ n with hψX
  set S : ℕ → ℝ := fun q => ∑ χ ∈ nontrivChars q, ‖psiChar χ.primitiveCharacter X‖ with hS
  -- the pointwise decomposition
  have hpt : ∀ q ∈ Icc 1 Q, |psiAP X q (a q) - X / q.totient| ≤
      |ψX - X| / q.totient + 2 * nuX X q + (1 / (q.totient : ℝ)) * S q := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    exact abs_psiAP_sub_le q (a q) X hq.1 (ha q)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hfirst : ∑ q ∈ Icc 1 Q, |ψX - X| / q.totient =
      |ψX - X| * ∑ q ∈ Icc 1 Q, (1 / (q.totient : ℝ)) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => ?_; ring
  rw [hfirst]
  -- harmonic-type sum
  have hH : ∑ q ∈ Icc 1 Q, (1 / (q.totient : ℝ)) ≤ (2 + L) ^ 2 := by
    have e : Icc 1 Q = Ioc 0 Q := by ext q; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [e]
    refine (sum_inv_totient_le Q).trans (pow_le_pow_left₀ ?_ ?_ 2)
    · have := Real.log_natCast_nonneg Q; linarith
    · have : Real.log Q ≤ L := by
        rcases Nat.eq_zero_or_pos Q with h | h
        · rw [h]; simp; linarith
        · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hQX')
      linarith
  have hH0 : 0 ≤ ∑ q ∈ Icc 1 Q, (1 / (q.totient : ℝ)) := Finset.sum_nonneg fun _ _ => by positivity
  have hℓL : (2 + L) ^ 2 ≤ 16 * L ^ 2 := by nlinarith
  have hLA2 : L ^ (-(A + 2)) * L ^ 2 = L ^ (-A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]; congr 1; push_cast; ring
  -- term (i)
  have hT1 : |ψX - X| * ∑ q ∈ Icc 1 Q, (1 / (q.totient : ℝ)) ≤ 16 * Cp' * (X * L ^ (-A)) := by
    have hp : |ψX - X| ≤ Cp' * (X * L ^ (-(A + 2))) :=
      (hCp X hX).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    calc |ψX - X| * ∑ q ∈ Icc 1 Q, (1 / (q.totient : ℝ))
        ≤ Cp' * (X * L ^ (-(A + 2))) * (16 * L ^ 2) :=
          mul_le_mul hp (hH.trans hℓL) hH0 (by positivity)
      _ = 16 * Cp' * (X * (L ^ (-(A + 2)) * L ^ 2)) := by ring
      _ = 16 * Cp' * (X * L ^ (-A)) := by rw [hLA2]
  -- term (ii)
  have hT2 : ∑ q ∈ Icc 1 Q, 2 * nuX X q ≤ 4 * C0 * (X * L ^ (-A)) := by
    have hν : ∀ q ∈ Icc 1 Q, 2 * nuX X q ≤ 2 * (Q * (2 * (2 + L)) * L) := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      have h1 := nuX_le X q hq.1
      have h2 := natLog_le X (by omega)
      push_cast at h2
      have h3 : (q : ℝ) ≤ Q := by exact_mod_cast hq.2
      have h4 : (Nat.log 2 X : ℝ) ≤ 2 * (2 + L) := by linarith
      have : (q : ℝ) * (Nat.log 2 X) * L ≤ Q * (2 * (2 + L)) * L := by gcongr
      linarith
    refine (Finset.sum_le_sum hν).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    have hQ2 : (Q : ℝ) ^ 2 * (X : ℝ) ^ (2 * η) ≤ X := by
      have h1 : (Q : ℝ) ^ 2 ≤ ((X : ℝ) ^ (1 / 2 - η)) ^ 2 := pow_le_pow_left₀ (by positivity) hQX 2
      have e : ((X : ℝ) ^ (1 / 2 - η)) ^ 2 * (X : ℝ) ^ (2 * η) = X := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
        rw [show (1 / 2 - η) * ((2 : ℕ) : ℝ) + 2 * η = (1 : ℝ) by push_cast; ring, Real.rpow_one]
      calc (Q : ℝ) ^ 2 * (X : ℝ) ^ (2 * η) ≤ ((X : ℝ) ^ (1 / 2 - η)) ^ 2 * (X : ℝ) ^ (2 * η) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = X := e
    have hpl := hC0 X (by linarith)
    have hLℓ : L ^ A * (2 + L) ^ 2 ≤ (2 + L) ^ (A + 2) := by
      rw [Real.rpow_add (by linarith), ← Real.rpow_natCast (2 + L) 2]
      push_cast
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hL0.le (by linarith) hA.le)
        (by positivity)
    have hLA : L ^ A * L ^ (-A) = 1 := by rw [← Real.rpow_add hL0]; simp
    have key : (Q : ℝ) ^ 2 * (2 + L) ^ 2 ≤ C0 * (X * L ^ (-A)) := by
      have h1 : (Q : ℝ) ^ 2 * (2 + L) ^ 2 * L ^ A ≤ C0 * X := by
        calc (Q : ℝ) ^ 2 * (2 + L) ^ 2 * L ^ A = (Q : ℝ) ^ 2 * (L ^ A * (2 + L) ^ 2) := by ring
          _ ≤ (Q : ℝ) ^ 2 * (2 + L) ^ (A + 2) := by gcongr
          _ ≤ (Q : ℝ) ^ 2 * (C0 * (X : ℝ) ^ (2 * η)) := by gcongr
          _ = C0 * ((Q : ℝ) ^ 2 * (X : ℝ) ^ (2 * η)) := by ring
          _ ≤ C0 * X := mul_le_mul_of_nonneg_left hQ2 hC00.le
      calc (Q : ℝ) ^ 2 * (2 + L) ^ 2 = (Q : ℝ) ^ 2 * (2 + L) ^ 2 * L ^ A * L ^ (-A) := by
            rw [mul_assoc _ (L ^ A), hLA, mul_one]
        _ ≤ C0 * X * L ^ (-A) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = C0 * (X * L ^ (-A)) := by ring
    have hL2 : 2 * ((2 + L) * L) ≤ 2 * (2 + L) ^ 2 := by nlinarith
    calc (Q : ℝ) * (2 * (Q * (2 * (2 + L)) * L)) = 2 * (Q : ℝ) ^ 2 * (2 * ((2 + L) * L)) := by ring
      _ ≤ 2 * (Q : ℝ) ^ 2 * (2 * (2 + L) ^ 2) := by gcongr
      _ = 4 * ((Q : ℝ) ^ 2 * (2 + L) ^ 2) := by ring
      _ ≤ 4 * (C0 * (X * L ^ (-A))) := by gcongr
      _ = 4 * C0 * (X * L ^ (-A)) := by ring
  -- term (iii)
  have hT3 : ∑ q ∈ Icc 1 Q, (1 / (q.totient : ℝ)) * S q ≤ 16 * Cc * (X * L ^ (-A)) := by
    set F : (Σ d : ℕ, DirichletCharacter ℂ d) → ℝ := fun p => ‖psiChar p.2 X‖ with hF
    set G : ℕ → ℝ := fun d => ∑ χ' ∈ primChars d, ‖psiChar χ' X‖ with hG
    have h1 : ∀ q ∈ Icc 1 Q, (1 / (q.totient : ℝ)) * S q ≤
        (1 / (q.totient : ℝ)) * ∑ d ∈ q.divisors.filter (2 ≤ ·), G d := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      exact mul_le_mul_of_nonneg_left (sum_nontriv_le q hq.1 F (fun _ => norm_nonneg _))
        (by positivity)
    refine (Finset.sum_le_sum h1).trans ?_
    refine (regroup Q G (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)).trans ?_
    have e : Ioc 0 Q = Icc 1 Q := by ext q; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [e]
    have hc := hCc X hX
    calc (∑ m ∈ Icc 1 Q, (1 / (m.totient : ℝ))) * ∑ d ∈ Icc 2 Q, (1 / (d.totient : ℝ)) * G d
        ≤ (16 * L ^ 2) * (Cc * (X * L ^ (-(A + 2)))) :=
          mul_le_mul (hH.trans hℓL) hc (Finset.sum_nonneg fun _ _ => by positivity)
            (by positivity)
      _ = 16 * Cc * (X * (L ^ (-(A + 2)) * L ^ 2)) := by ring
      _ = 16 * Cc * (X * L ^ (-A)) := by rw [hLA2]
  calc |ψX - X| * ∑ q ∈ Icc 1 Q, (1 / (q.totient : ℝ)) + ∑ q ∈ Icc 1 Q, 2 * nuX X q +
        ∑ q ∈ Icc 1 Q, (1 / (q.totient : ℝ)) * S q
      ≤ 16 * Cp' * (X * L ^ (-A)) + 4 * C0 * (X * L ^ (-A)) + 16 * Cc * (X * L ^ (-A)) := by
        linarith
    _ = (16 * Cp' + 4 * C0 + 16 * Cc) * (X * L ^ (-A)) := by ring

end ArtinPrimitiveRoots.BV
end

open ArtinPrimitiveRoots Finset Real in
theorem solution (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
      ∑ q ∈ Icc 1 ⌊(X : ℝ) ^ (1 / 2 - η)⌋₊, |psiAP X q (a q) - X / q.totient|
        ≤ C * (X * log X ^ (-A)) :=
  ArtinPrimitiveRoots.BV.psi_bombieri_vinogradov A η hA hη
