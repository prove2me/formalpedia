-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:32.863924+00:00
-- url     : https://prove2.me/theorems/d71c8534-3877-436a-a5f9-13d3b0134839
-- title:
--   Taylor Expansion
-- statement:
--   Definitions and structural lemmas for Taylor Expansion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansion.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace FunctorialResolution.EmbeddedResolution.TaylorExpansion
section
variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
theorem iterate_deriv_mul_eq_sum_nsmul (D : Derivation A R R) (n : ℕ) (f g : R) :
    (⇑D)^[n] (f * g) =
      ∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : ∀ i : ℕ,
        ⇑D (n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g))
          = n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g)
            + n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
      intro i
      rw [map_nsmul, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        ← Function.iterate_succ_apply' (⇑D) (n - i) g,
        ← Function.iterate_succ_apply' (⇑D) i f,
        mul_comm ((⇑D)^[n - i] g) ((⇑D)^[i + 1] f), smul_add]
    have e3 : ∑ i ∈ Finset.range (n + 1), n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g)
        = ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
      rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show n < n + 1 by omega), zero_smul,
        add_zero]
    have e1 : ∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g)
        = (∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
          + f * (⇑D)^[n + 1] g := by
      have inner : ∑ i ∈ Finset.range n,
            n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - (i + 1) + 1] g)
          = ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have h := Finset.mem_range.mp hi
        have hi' : n - (i + 1) + 1 = n - i := by omega
        rw [hi']
      rw [Finset.sum_range_succ', inner]
      simp only [Nat.choose_zero_right, one_smul, Function.iterate_zero_apply, Nat.sub_zero]
    have e2 : ∑ i ∈ Finset.range (n + 1 + 1),
          (n + 1).choose i • ((⇑D)^[i] f * (⇑D)^[n + 1 - i] g)
        = ((∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
            + ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
          + f * (⇑D)^[n + 1] g := by
      have inner2 : ∑ i ∈ Finset.range (n + 1),
            (n + 1).choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n + 1 - (i + 1)] g)
          = (∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
            + ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
        rw [← e3, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hc : (n + 1).choose (i + 1) = n.choose i + n.choose (i + 1) :=
          Nat.choose_succ_succ n i
        have hs : n + 1 - (i + 1) = n - i := by omega
        rw [hc, hs, add_smul]
      rw [Finset.sum_range_succ', inner2]
      simp only [Nat.choose_zero_right, one_smul, Function.iterate_zero_apply, Nat.sub_zero]
    calc (⇑D)^[n + 1] (f * g)
        = ⇑D ((⇑D)^[n] (f * g)) := Function.iterate_succ_apply' _ _ _
      _ = ⇑D (∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g)) := by
            rw [ih]
      _ = ∑ i ∈ Finset.range (n + 1), ⇑D (n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g)) := by
            rw [map_sum]
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g)
            + n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g)) :=
            Finset.sum_congr rfl fun i _ => key i
      _ = (∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g))
            + ∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) :=
            Finset.sum_add_distrib
      _ = ∑ i ∈ Finset.range (n + 1 + 1),
            (n + 1).choose i • ((⇑D)^[i] f * (⇑D)^[n + 1 - i] g) := by
            rw [e1, e2]; ring
theorem iterate_deriv_mul (D : Derivation A R R) (n : ℕ) (f g : R) :
    (⇑D)^[n] (f * g) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : R) * ((⇑D)^[i] f * (⇑D)^[n - i] g) := by
  rw [iterate_deriv_mul_eq_sum_nsmul D n f g]
  exact Finset.sum_congr rfl fun i _ => by rw [nsmul_eq_mul]
end
section
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]
def coeff (σ : R →+* S) (D : Derivation A R R) (i : ℕ) (f : R) : S :=
  algebraMap ℚ S ((i.factorial : ℚ)⁻¹) * σ ((⇑D)^[i] f)
def truncatedSeries (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f : R) : S :=
  ∑ j ∈ Finset.range N, algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j
@[simp]
theorem truncatedSeries_apply (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f : R) :
    truncatedSeries σ D β N f =
      ∑ j ∈ Finset.range N, algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j :=
  rfl
theorem truncatedSeries_of_deriv_eq_zero (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (hN : 1 ≤ N) (f : R) (hf : D f = 0) : truncatedSeries σ D β N f = σ f := by
  have hz : (⇑D) (0 : R) = 0 := by simp
  have key : ∀ k : ℕ, (⇑D)^[k + 1] f = 0 := by
    intro k
    rw [Function.iterate_succ_apply, hf]
    exact Function.iterate_fixed hz k
  rw [truncatedSeries_apply, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
    rw [key k]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega : 0 < N)) h
theorem factorial_inv_mul_choose {S' : Type*} [CommRing S'] [Algebra ℚ S'] (j i : ℕ)
    (h : i ≤ j) :
    algebraMap ℚ S' ((j.factorial : ℚ)⁻¹) * (j.choose i : S')
      = algebraMap ℚ S' ((i.factorial : ℚ)⁻¹) * algebraMap ℚ S' (((j - i).factorial : ℚ)⁻¹) := by
  have hj : ((j.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos j).ne'
  have hi : ((i.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos i).ne'
  have hji : (((j - i).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos (j - i)).ne'
  have h1 : (j.choose i : ℚ) * (i.factorial : ℚ) * ((j - i).factorial : ℚ)
      = (j.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  have key : ((j.factorial : ℚ))⁻¹ * (j.choose i : ℚ)
      = ((i.factorial : ℚ))⁻¹ * (((j - i).factorial : ℚ))⁻¹ := by
    field_simp
    linear_combination h1
  have h2 := congrArg (algebraMap ℚ S') key
  simpa only [map_mul, map_natCast] using h2
theorem coeff_eq {A' R' S' : Type*} [CommRing A'] [CommRing R'] [CommRing S']
    [Algebra A' R'] [Algebra ℚ S'] (σ : R' →+* S') (D : Derivation A' R' R') (i : ℕ) (f : R') :
    coeff σ D i f = algebraMap ℚ S' ((i.factorial : ℚ)⁻¹) * σ ((⇑D)^[i] f) := rfl
theorem truncatedSeries_mul (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f g : R) :
    truncatedSeries σ D β N (f * g) =
      ∑ j ∈ Finset.range N,
        β ^ j * ∑ i ∈ Finset.range (j + 1),
          coeff σ D i f * coeff σ D (j - i) g := by
  rw [truncatedSeries_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iterate_deriv_mul D j f g, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have key := factorial_inv_mul_choose (S' := S) j i hij
  simp only [coeff_eq, map_mul, map_natCast]
  linear_combination (σ ((⇑D)^[i] f) * σ ((⇑D)^[j - i] g) * β ^ j) * key
theorem truncatedSeries_zero (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) :
    truncatedSeries σ D β N 0 = 0 := by
  have hz : (⇑D) (0 : R) = 0 := by simp
  rw [truncatedSeries_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Function.iterate_fixed hz j]
  simp
theorem truncatedSeries_add (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f g : R) :
    truncatedSeries σ D β N (f + g) = truncatedSeries σ D β N f + truncatedSeries σ D β N g := by
  have key : ∀ j : ℕ, (⇑D)^[j] (f + g) = (⇑D)^[j] f + (⇑D)^[j] g := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      simp only [Function.iterate_succ_apply', ih, map_add]
  simp only [truncatedSeries_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key j, map_add]
  ring
theorem sum_range_sum_range_succ_eq_sum_sum_Ico {T : Type*} [AddCommMonoid T] (N : ℕ) (h : ℕ → ℕ → T) :
    ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), h i j
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i N, h i j := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hL : ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (j + 1), h i j
        = (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), h i j)
          + ∑ i ∈ Finset.range (N + 1), h i N :=
      Finset.sum_range_succ (fun j => ∑ i ∈ Finset.range (j + 1), h i j) N
    have hR1 : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.Ico i (N + 1), h i j
        = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i (N + 1), h i j)
          + ∑ j ∈ Finset.Ico N (N + 1), h N j :=
      Finset.sum_range_succ (fun i => ∑ j ∈ Finset.Ico i (N + 1), h i j) N
    have hR2 : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i (N + 1), h i j
        = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i N, h i j)
          + ∑ i ∈ Finset.range N, h i N := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiN : i ≤ N := le_of_lt (Finset.mem_range.mp hi)
      exact Finset.sum_Ico_succ_top hiN (fun j => h i j)
    have hR3 : ∑ j ∈ Finset.Ico N (N + 1), h N j = h N N := by
      rw [Finset.sum_Ico_succ_top (le_refl N) (fun j => h N j), Finset.Ico_self,
        Finset.sum_empty, zero_add]
    have hlast : ∑ i ∈ Finset.range (N + 1), h i N
        = (∑ i ∈ Finset.range N, h i N) + h N N :=
      Finset.sum_range_succ (fun i => h i N) N
    rw [hL, hR1, hR2, hR3, ih, hlast, add_assoc]
theorem sum_Ico_mul_pow_eq_sum_range {T : Type*} [CommRing T] (a b : ℕ → T) (β : T) (N i : ℕ) :
    ∑ j ∈ Finset.Ico i N, a i * b (j - i) * β ^ j
      = ∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k) := by
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : i + k - i = k := by omega
  simp only [hk]
theorem sum_convolution_sub_mul_mem {T : Type*} [CommRing T] (β : T) (N : ℕ) (J : Ideal T)
    (hβ : β ^ N ∈ J) (a b : ℕ → T) :
    (∑ j ∈ Finset.range N, β ^ j * ∑ i ∈ Finset.range (j + 1), a i * b (j - i))
      - (∑ j ∈ Finset.range N, a j * β ^ j) * (∑ j ∈ Finset.range N, b j * β ^ j) ∈ J := by
  have hprod : (∑ j ∈ Finset.range N, a j * β ^ j) * (∑ j ∈ Finset.range N, b j * β ^ j)
      = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have htri : (∑ j ∈ Finset.range N, β ^ j * ∑ i ∈ Finset.range (j + 1), a i * b (j - i))
      = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k) := by
    have e1 : (∑ j ∈ Finset.range N, β ^ j * ∑ i ∈ Finset.range (j + 1), a i * b (j - i))
        = ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), a i * b (j - i) * β ^ j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    refine e1.trans ((sum_range_sum_range_succ_eq_sum_sum_Ico N (fun i j => a i * b (j - i) * β ^ j)).trans ?_)
    exact Finset.sum_congr rfl fun i _ => sum_Ico_mul_pow_eq_sum_range a b β N i
  have hdist : (∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
      - (∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k))
      = ∑ i ∈ Finset.range N, ((∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
          - ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k)) := by
    refine (eq_sub_of_add_eq ?_).symm
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hprod, htri, hdist]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hiN : i < N := Finset.mem_range.mp hi
  have hsplit : ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k)
      = (∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
        + ∑ k ∈ Finset.Ico (N - i) N, a i * b k * β ^ (i + k) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le (N - i)) (Nat.sub_le N i)).symm
  rw [hsplit]
  have hre : (∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
      - ((∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
        + ∑ k ∈ Finset.Ico (N - i) N, a i * b k * β ^ (i + k))
      = -(∑ k ∈ Finset.Ico (N - i) N, a i * b k * β ^ (i + k)) := by ring
  rw [hre]
  refine neg_mem (Ideal.sum_mem _ fun k hk => ?_)
  have hk1 : N - i ≤ k := (Finset.mem_Ico.mp hk).1
  have hpow : β ^ (i + k) ∈ J := by
    have he : i + k = N + (i + k - N) := by omega
    rw [he, pow_add]
    exact Ideal.mul_mem_right _ _ hβ
  exact Ideal.mul_mem_left _ _ hpow
theorem truncatedSeries_mul_sub_mem (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) (hβ : β ^ N ∈ J) (f g : R) :
    truncatedSeries σ D β N (f * g) - truncatedSeries σ D β N f * truncatedSeries σ D β N g ∈ J := by
  have hf : truncatedSeries σ D β N f
      = ∑ j ∈ Finset.range N, coeff σ D j f * β ^ j := rfl
  have hg : truncatedSeries σ D β N g
      = ∑ j ∈ Finset.range N, coeff σ D j g * β ^ j := rfl
  rw [truncatedSeries_mul σ D β N f g, hf, hg]
  exact sum_convolution_sub_mul_mem β N J hβ (fun i => coeff σ D i f)
    (fun i => coeff σ D i g)
theorem mk_truncatedSeries_one (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) (hN : 1 ≤ N) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N 1) = 1 := by
  have h1 : D 1 = 0 := by simp
  rw [truncatedSeries_of_deriv_eq_zero σ D β N hN 1 h1]
  simp
theorem mk_truncatedSeries_mul (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) (hβ : β ^ N ∈ J) (f g : R) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N (f * g)) =
      Ideal.Quotient.mk J (truncatedSeries σ D β N f) *
        Ideal.Quotient.mk J (truncatedSeries σ D β N g) := by
  have h : truncatedSeries σ D β N (f * g)
      - truncatedSeries σ D β N f * truncatedSeries σ D β N g ∈ J :=
    truncatedSeries_mul_sub_mem σ D β N J hβ f g
  have h2 : Ideal.Quotient.mk J (truncatedSeries σ D β N (f * g))
      = Ideal.Quotient.mk J (truncatedSeries σ D β N f * truncatedSeries σ D β N g) :=
    Ideal.Quotient.eq.mpr h
  rw [h2, map_mul]
theorem mk_truncatedSeries_zero (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N 0) = 0 := by
  rw [truncatedSeries_zero, map_zero]
theorem mk_truncatedSeries_add (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) (f g : R) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N (f + g)) =
      Ideal.Quotient.mk J (truncatedSeries σ D β N f) +
        Ideal.Quotient.mk J (truncatedSeries σ D β N g) := by
  rw [truncatedSeries_add, map_add]
def truncatedSeriesRingHom (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (J : Ideal S)
    (hN : 1 ≤ N) (hβ : β ^ N ∈ J) : R →+* S ⧸ J :=
  { toFun := fun f => Ideal.Quotient.mk J (truncatedSeries σ D β N f)
    map_one' := mk_truncatedSeries_one σ D β N J hN
    map_mul' := mk_truncatedSeries_mul σ D β N J hβ
    map_zero' := mk_truncatedSeries_zero σ D β N J
    map_add' := mk_truncatedSeries_add σ D β N J }
end
end FunctorialResolution.EmbeddedResolution.TaylorExpansion


