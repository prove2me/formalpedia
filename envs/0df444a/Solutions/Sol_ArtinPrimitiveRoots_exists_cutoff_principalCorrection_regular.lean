-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_principalCorrection_regular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T11:06:23.397403+00:00
-- url     : https://prove2.me/submissions/610f6b27-4845-4457-b4bb-aab6f7ac8bbb

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe

section
namespace ArtinPrimitiveRoots

open NumberField

/-- The algebraic identity behind the local bound: `ℋ_P − 1` with `X = Q⁻¹`. -/
theorem T12C_alg (X D E : ℂ) (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    ((1 - X ^ 2) + (1 - X) ^ 2 * (1 + X) * (E - D) / (1 - E)) / (1 - D) - 1 =
      (-X ^ 2 + ((X + X ^ 2 - X ^ 3) * D + E * ((1 - X) ^ 2 * (1 + X) - D)) / (1 - E)) /
        (1 - D) := by
  field_simp
  ring

/-- The norm estimate behind the local bound. -/
theorem T12C_norm_bound (x t : ℝ) (D E : ℂ) (hx0 : 0 ≤ x) (hxt : x ≤ t) (ht : t ≤ 1 / 2)
    (hD : ‖D‖ ≤ t) (hE : ‖E‖ ≤ x * t) :
    ‖(-(x : ℂ) ^ 2 + (((x : ℂ) + (x : ℂ) ^ 2 - (x : ℂ) ^ 3) * D +
        E * ((1 - (x : ℂ)) ^ 2 * (1 + (x : ℂ)) - D)) / (1 - E)) / (1 - D)‖ ≤ 18 * (x * t) := by
  have hx1 : x ≤ 1 / 2 := hxt.trans ht
  have h1D : 1 / 2 ≤ ‖1 - D‖ := by
    have := norm_sub_norm_le (1 : ℂ) D
    simp only [norm_one] at this
    linarith
  have h1E : 1 / 2 ≤ ‖1 - E‖ := by
    have := norm_sub_norm_le (1 : ℂ) E
    simp only [norm_one] at this
    nlinarith
  have hc : ‖((1 - (x : ℂ)) ^ 2 * (1 + (x : ℂ)) - D)‖ ≤ 2 := by
    have : ((1 - (x : ℂ)) ^ 2 * (1 + (x : ℂ))) = (((1 - x) ^ 2 * (1 + x) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
    nlinarith
  have hb : ‖((x : ℂ) + (x : ℂ) ^ 2 - (x : ℂ) ^ 3)‖ ≤ 2 * x := by
    have : ((x : ℂ) + (x : ℂ) ^ 2 - (x : ℂ) ^ 3) = ((x + x ^ 2 - x ^ 3 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
    nlinarith
  have hnum : ‖((x : ℂ) + (x : ℂ) ^ 2 - (x : ℂ) ^ 3) * D +
      E * ((1 - (x : ℂ)) ^ 2 * (1 + (x : ℂ)) - D)‖ ≤ 4 * (x * t) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖((x : ℂ) + (x : ℂ) ^ 2 - (x : ℂ) ^ 3)‖ * ‖D‖ ≤ 2 * x * t :=
      mul_le_mul hb hD (norm_nonneg _) (by linarith)
    have h2 : ‖E‖ * ‖((1 - (x : ℂ)) ^ 2 * (1 + (x : ℂ)) - D)‖ ≤ x * t * 2 :=
      mul_le_mul hE hc (norm_nonneg _) (by nlinarith)
    linarith
  have hq : ‖(((x : ℂ) + (x : ℂ) ^ 2 - (x : ℂ) ^ 3) * D +
      E * ((1 - (x : ℂ)) ^ 2 * (1 + (x : ℂ)) - D)) / (1 - E)‖ ≤ 8 * (x * t) := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    have hxt0 : 0 ≤ x * t := mul_nonneg hx0 (hx0.trans hxt)
    nlinarith [mul_le_mul_of_nonneg_left h1E hxt0]
  have hx2 : ‖-(x : ℂ) ^ 2‖ ≤ x * t := by
    rw [norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    nlinarith
  rw [norm_div, div_le_iff₀ (by linarith)]
  have := (norm_add_le _ _).trans (add_le_add hx2 hq)
  have hxt0 : 0 ≤ x * t := mul_nonneg hx0 (hx0.trans hxt)
  nlinarith [mul_le_mul_of_nonneg_left h1D hxt0]

/-- The local factor `ℋ_P` at a prime of norm `Q ≥ 30`, for `‖e‖ ≤ 1`, `‖θ‖ ≤ 1`, `Re s > .998`:
`‖ℋ_P − 1‖ ≤ 18 Q^{-1998/1000}`. -/
theorem T12C_localFactor_sub_one (Q : ℕ) (hQ : 30 ≤ Q) (e θ s : ℂ) (he : ‖e‖ ≤ 1)
    (hθ : ‖θ‖ ≤ 1) (hs : 998 / 1000 < s.re) :
    ‖principalLocalFactor Q e θ s - 1‖ ≤ 18 * (Q : ℝ) ^ (-(1998 / 1000 : ℝ)) ∧
      1 - e * (Q : ℂ) ^ (-s) ≠ 0 ∧ 1 - θ * (Q : ℂ) ^ (3 - 6 * s) ≠ 0 := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  have hQ0 : (0 : ℝ) < Q := by linarith
  set x : ℝ := (Q : ℝ)⁻¹ with hxdef
  set t : ℝ := (Q : ℝ) ^ (-(998 / 1000 : ℝ)) with htdef
  have hx0 : 0 ≤ x := by positivity
  have hxt : x ≤ t := by
    rw [hxdef, htdef, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  have ht : t ≤ 1 / 2 := by
    have h1 : t ≤ (Q : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
    have h2 : (Q : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt Q)⁻¹ := by
      rw [Real.rpow_neg hQ0.le, Real.sqrt_eq_rpow]
    have h3 : (2 : ℝ) ≤ Real.sqrt Q := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 4 ≤ Q))
    rw [h2] at h1
    calc t ≤ (Real.sqrt Q)⁻¹ := h1
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h3
  have hxtQ : x * t = (Q : ℝ) ^ (-(1998 / 1000 : ℝ)) := by
    rw [hxdef, htdef, ← Real.rpow_neg_one, ← Real.rpow_add hQ0]
    norm_num
  have hD : ‖e * (Q : ℂ) ^ (-s)‖ ≤ t := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    calc ‖e‖ * (Q : ℝ) ^ (-s.re) ≤ 1 * (Q : ℝ) ^ (-s.re) := by gcongr
      _ ≤ t := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hE : ‖θ * (Q : ℂ) ^ (3 - 6 * s)‖ ≤ x * t := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), hxtQ]
    have hre : (3 - 6 * s).re = 3 - 6 * s.re := by simp
    rw [hre]
    calc ‖θ‖ * (Q : ℝ) ^ (3 - 6 * s.re) ≤ 1 * (Q : ℝ) ^ (3 - 6 * s.re) := by gcongr
      _ ≤ _ := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have h1D : 1 - e * (Q : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have : e * (Q : ℂ) ^ (-s) = 1 := by linear_combination -h
    rw [this, norm_one] at hD
    linarith
  have h1E : 1 - θ * (Q : ℂ) ^ (3 - 6 * s) ≠ 0 := by
    intro h
    have : θ * (Q : ℂ) ^ (3 - 6 * s) = 1 := by linear_combination -h
    rw [this, norm_one] at hE
    nlinarith
  refine ⟨?_, h1D, h1E⟩
  have hX : ((Q : ℂ) ^ 2)⁻¹ = ((x : ℝ) : ℂ) ^ 2 ∧ (Q : ℂ)⁻¹ = ((x : ℝ) : ℂ) := by
    constructor <;> simp [hxdef, inv_pow]
  simp only [principalLocalFactor]
  rw [hX.1, hX.2, T12C_alg _ _ _ h1D h1E, ← hxtQ]
  exact T12C_norm_bound x t _ _ hx0 hxt ht hD hE

/-- The local factor is holomorphic in `s` on `Re s > .998` (for `Q ≥ 30`, `‖e‖, ‖θ‖ ≤ 1`). -/
theorem T12C_localFactor_differentiableOn (Q : ℕ) (hQ : 30 ≤ Q) (e θ : ℂ) (he : ‖e‖ ≤ 1)
    (hθ : ‖θ‖ ≤ 1) :
    DifferentiableOn ℂ (fun s => principalLocalFactor Q e θ s) {s : ℂ | 998 / 1000 < s.re} := by
  intro s hs
  obtain ⟨-, h1D, h1E⟩ := T12C_localFactor_sub_one Q hQ e θ s he hθ hs
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  refine DifferentiableAt.differentiableWithinAt ?_
  simp only [principalLocalFactor]
  have hc1 : DifferentiableAt ℂ (fun s : ℂ => (Q : ℂ) ^ (-s)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hQ0)
  have hc2 : DifferentiableAt ℂ (fun s : ℂ => (Q : ℂ) ^ (3 - 6 * s)) s :=
    ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)).const_cpow
      (Or.inl hQ0)
  refine DifferentiableAt.div ?_ ((differentiableAt_const _).sub ((differentiableAt_const _).mul hc1))
    h1D
  refine (differentiableAt_const _).add (DifferentiableAt.div ?_ ?_ h1E)
  · exact (differentiableAt_const _).mul
      (((differentiableAt_const _).mul hc2).sub ((differentiableAt_const _).mul hc1))
  · exact (differentiableAt_const _).sub ((differentiableAt_const _).mul hc2)

theorem T12C_bound_lt_one (Q : ℕ) (hQ : 30 ≤ Q) : 18 * (Q : ℝ) ^ (-(1998 / 1000 : ℝ)) < 1 := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  have h1 : (Q : ℝ) ^ (-(1998 / 1000 : ℝ)) ≤ (Q : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  rw [Real.rpow_neg_one] at h1
  have h2 : (Q : ℝ)⁻¹ ≤ 1 / 30 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hQ)
  linarith

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField Filter Asymptotics Finset

/-- The partial sums of the ideal-counting function are `O(n)`. -/
theorem T12C_sum_card_isBigO (F : Type*) [Field F] [NumberField F] :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  have hT := (Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop
  have h1 := hT.isBigO_one ℝ
  have h2 := h1.mul (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
  simp only [one_mul] at h2
  refine (h2.congr' ?_ ?_)
  · filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [Function.comp_apply]
    rw [div_mul_cancel₀ _ (by exact_mod_cast hn)]
    norm_cast
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le)]
    classical
    rw [← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  · exact Eventually.of_forall fun n => by simp

/-- `∑_I N(I)^{-α}` converges for `α > 1` (all ideals; the zero ideal contributes `0`). -/
theorem T12C_summable_ideal (F : Type*) [Field F] [NumberField F] {α : ℝ} (hα : 1 < α) :
    Summable fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-α) := by
  set c : ℕ → ℝ := fun k => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ) with hc
  have hL : LSeriesSummable (fun n => (c n : ℂ)) (α : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg (T12C_sum_card_isBigO F)
      (fun n => by positivity) zero_le_one (by simpa using hα)
  have hR : Summable fun n : ℕ => c n * (n : ℝ) ^ (-α) := by
    refine (hL.norm).congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (by linarith : -α ≠ 0)]
    · rw [if_neg hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        Complex.ofReal_re, Real.rpow_neg (by positivity), div_eq_mul_inv]
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)).summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr ⟨fun n => ?_, ?_⟩
  · have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    exact Summable.of_finite
  · refine hR.congr fun n => ?_
    have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    haveI := Fintype.ofFinite {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
    rw [tsum_fintype]
    simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]
    rw [Finset.sum_congr rfl (fun y _ => by rw [y.2]), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    simp only [hc, Nat.card_eq_fintype_card]

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField
open scoped nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

theorem T12C_map_pow {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) (k : ℕ) :
    χ.toFun (I ^ k) = χ.toFun I ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    have := χ.map_principal' 1 one_ne_zero (by simp)
    rwa [Ideal.span_singleton_one, ← Ideal.one_eq_top] at this
  | succ k ih => rw [pow_succ, χ.map_mul', ih, pow_succ]

/-- A finite-order Hecke character has absolute value `1` on nonzero ideals coprime to `𝔪`. -/
theorem T12C_norm_eq_one {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤) : ‖χ.toFun I‖ = 1 := by
  classical
  by_cases h𝔪 : 𝔪 = ⊥
  · subst h𝔪
    rw [sup_bot_eq] at hcop
    subst hcop
    have := χ.map_principal' 1 one_ne_zero (by simp)
    rw [Ideal.span_singleton_one] at this
    rw [this, norm_one]
  have hI0 : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hmk : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have hI0h : I ^ h ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hI)
  have hprin : (I ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff hI0h).mp hmk
  obtain ⟨β, hβ⟩ := hprin.principal
  change I ^ h = Ideal.span {β} at hβ
  -- `hβ : I ^ h = span {β}`
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero] at hβ
    exact pow_ne_zero h hI hβ
  have hcop' : Ideal.span {β} ⊔ 𝔪 = ⊤ := by rw [← hβ]; exact Ideal.pow_sup_eq_top hcop
  have hunit : IsUnit (Ideal.Quotient.mk 𝔪 β) := by
    rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at hcop'
    obtain ⟨y, hy, z, hz, hyz⟩ := hcop'
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔪 r) ?_
    rw [← map_mul, mul_comm, ← map_one (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq]
    have : r * β - 1 = -z := by linear_combination hyz
    rw [this]
    exact 𝔪.neg_mem hz
  have hfin : Finite (𝓞 F ⧸ 𝔪) := Ring.HasFiniteQuotients.finiteQuotient h𝔪
  obtain ⟨m, hm, hum⟩ := (isOfFinOrder_of_finite hunit.unit).exists_pow_eq_one
  have hβm : Ideal.Quotient.mk 𝔪 (β ^ m) = 1 := by
    rw [map_pow]
    have := congrArg Units.val hum
    simpa using this
  have hχ : χ.toFun (Ideal.span {β ^ m}) = 1 := by
    refine χ.map_principal' _ (pow_ne_zero _ hβ0) ?_
    rw [← Ideal.Quotient.eq, map_one, hβm]
  rw [← Ideal.span_singleton_pow, ← hβ, ← pow_mul, T12C_map_pow] at hχ
  have hn := congrArg norm hχ
  rw [norm_pow, norm_one] at hn
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.mul_ne_zero hpos.ne' hm.ne')).mp hn

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

theorem T12C_pow_mod3 {M : Type*} [Monoid M] (z : M) (hz : z ^ 3 = 1) (m : ℕ) :
    z ^ m = z ^ (m % 3) := by
  conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hz, one_pow, one_mul]

/-- A prime of norm divisible by `3` has norm at most `3^[F:ℚ]`. -/
theorem T12C_absNorm_le_of_three_dvd {F : Type*} [Field F] [NumberField F] (P : Ideal (𝓞 F))
    (hP0 : P ≠ ⊥) [P.IsMaximal] (h3 : 3 ∣ Ideal.absNorm P) :
    Ideal.absNorm P ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
  letI := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  obtain ⟨f, hp, hpf⟩ := FiniteField.card (𝓞 F ⧸ P) (ringChar (𝓞 F ⧸ P))
  rw [hcard] at hpf
  rw [hpf] at h3
  have h3p : 3 = ringChar (𝓞 F ⧸ P) :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
  have h30 : ((3 : ℕ) : 𝓞 F ⧸ P) = 0 := by rw [h3p]; exact ringChar.Nat.cast_ringChar
  have hmem : (3 : 𝓞 F) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    simpa using h30
  have hle : Ideal.span {(3 : 𝓞 F)} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hn : Algebra.norm ℤ (3 : 𝓞 F) = 3 ^ Module.finrank ℤ (𝓞 F) := by
    rw [show (3 : 𝓞 F) = algebraMap ℤ (𝓞 F) 3 by simp, Algebra.norm_algebraMap]
  rw [hn, Int.natAbs_pow] at hdvd
  exact Nat.le_of_dvd (by positivity) hdvd

/-- `|J(ρ_P, ρ_P)|^6 / N P^3 = 1` for a prime `P` of norm `> 3^[F:ℚ]` of the cyclotomic field
`F = ℚ(μ_n)`, `3 ∣ n`. -/
theorem T12C_norm_jacobiPhaseSix (n : ℕ) (hn0 : 0 < n) (hn : 3 ∣ n) (F : Type*) [Field F]
    [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (P : Ideal (𝓞 F))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) :
    ‖jacobiPhaseSix ι P‖ = 1 := by
  classical
  haveI : P.IsMaximal := hP.isMaximal hP0
  letI := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P with hQdef
  have hcard : Fintype.card (𝓞 F ⧸ P) = Q := by
    rw [hQdef, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hQ4 : 4 ≤ Q := by
    have : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
      have : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h3Q : ¬ 3 ∣ Q := fun h => by
    have := T12C_absNorm_le_of_three_dvd P hP0 h
    omega
  have hcop : Q.Coprime 3 := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3Q))
  -- the cube root of unity
  haveI : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ3 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 3)) 3 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  set ω₀ : 𝓞 F := hζ3.toInteger with hω₀
  have hω : IsPrimitiveRoot ω₀ 3 := hζ3.toInteger_isPrimitiveRoot
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P ω₀) 3 :=
    hω.idealQuotient_mk (by omega) hcop
  set ψ : ℂ := ι (ω₀ : F) with hψdef
  have hψ : IsPrimitiveRoot ψ 3 :=
    (hω.map_of_injective RingOfIntegers.coe_injective).map_of_injective ι.injective
  set e := (Q - 1) / 3 with hedef
  have h3e : 3 * e = Q - 1 := by
    have h1 : Ideal.Quotient.mk P ω₀ ^ (Q - 1) = 1 := by
      rw [← hcard]; exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
    have := (hωb.pow_eq_one_iff_dvd _).mp h1
    omega
  -- key lemma
  have KL : ∀ x : 𝓞 F ⧸ P, x ≠ 0 → ∀ i : ℕ, x ^ e = Ideal.Quotient.mk P ω₀ ^ i →
      cubicResidueChar ι P x = ψ ^ i := by
    intro x hx i hi
    have hex : ∃ ω : 𝓞 F, ω ^ 3 = 1 ∧ Ideal.Quotient.mk P ω = x ^ ((Ideal.absNorm P - 1) / 3) :=
      ⟨ω₀ ^ i, by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], by
        rw [map_pow, ← hi]⟩
    simp only [cubicResidueChar, if_neg hx, dif_pos hex]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    obtain ⟨j, hj, hjω⟩ := hω.eq_pow_of_pow_eq_one h1
    have hmk : Ideal.Quotient.mk P ω₀ ^ j = Ideal.Quotient.mk P ω₀ ^ (i % 3) := by
      rw [← map_pow, hjω, h2, ← T12C_pow_mod3 _ hωb.pow_eq_one]
      exact hi
    have hji : j = i % 3 := hωb.pow_inj hj (Nat.mod_lt _ (by norm_num)) hmk
    rw [← hjω, show ((ω₀ ^ j : 𝓞 F) : F) = (ω₀ : F) ^ j by norm_cast, map_pow, hji, ← T12C_pow_mod3 _ hψ.pow_eq_one]
  have EX : ∀ x : 𝓞 F ⧸ P, x ≠ 0 → ∃ i : ℕ, x ^ e = Ideal.Quotient.mk P ω₀ ^ i := by
    intro x hx
    have : (x ^ e) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, h3e, ← hcard]
      exact FiniteField.pow_card_sub_one_eq_one x hx
    obtain ⟨i, -, hi⟩ := hωb.eq_pow_of_pow_eq_one this
    exact ⟨i, hi.symm⟩
  have Z : cubicResidueChar ι P 0 = 0 := by simp [cubicResidueChar]
  let ρ : MulChar (𝓞 F ⧸ P) ℂ :=
    { toFun := cubicResidueChar ι P
      map_one' := by
        rw [KL 1 one_ne_zero 0 (by simp)]
        simp
      map_mul' := by
        intro x y
        by_cases hx : x = 0
        · simp [hx, Z]
        by_cases hy : y = 0
        · simp [hy, Z]
        obtain ⟨i, hi⟩ := EX x hx
        obtain ⟨j, hj⟩ := EX y hy
        rw [KL x hx i hi, KL y hy j hj, KL (x * y) (mul_ne_zero hx hy) (i + j)
          (by rw [mul_pow, hi, hj, pow_add]), pow_add]
      map_nonunit' := by
        intro a ha
        have : a = 0 := by
          by_contra h
          exact ha (Ne.isUnit h)
        simp [this, Z] }
  have hρ : ∀ x, ρ x = cubicResidueChar ι P x := fun x => rfl
  -- a non-cube
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (𝓞 F ⧸ P)ˣ)
  have hog : orderOf g = Q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card,
      hcard]
  obtain ⟨i, hi⟩ := EX (g : 𝓞 F ⧸ P) g.ne_zero
  have hi3 : ¬ 3 ∣ i := by
    intro h
    have h1 : (g : 𝓞 F ⧸ P) ^ e = 1 := by rw [hi, hωb.pow_eq_one_iff_dvd]; exact h
    have h2 : g ^ e = 1 := Units.ext (by simpa using h1)
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hog] at this
    have hepos : 0 < e := by omega
    have := Nat.le_of_dvd hepos this
    omega
  have hρg : ρ g = ψ ^ i := KL _ g.ne_zero i hi
  have hρ1 : ρ ≠ 1 := by
    intro h
    have : ρ g = 1 := by rw [h]; exact MulChar.one_apply_coe g
    rw [hρg, hψ.pow_eq_one_iff_dvd] at this
    exact hi3 this
  have hρ2 : ρ * ρ ≠ 1 := by
    intro h
    have : (ρ * ρ) g = 1 := by rw [h]; exact MulChar.one_apply_coe g
    rw [MulChar.mul_apply, hρg, ← pow_add, hψ.pow_eq_one_iff_dvd] at this
    have : 3 ∣ 2 * i := by rwa [two_mul]
    exact hi3 ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this))
  have hch : ringChar ℂ ≠ ringChar (𝓞 F ⧸ P) := by
    simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite (𝓞 F ⧸ P)).symm
  have hJ := jacobiSum_mul_jacobiSum_inv hch hρ1 hρ1 hρ2
  rw [← MulChar.star_eq_inv] at hJ
  have hstar : jacobiSum (star ρ) (star ρ) = starRingEnd ℂ (jacobiSum ρ ρ) :=
    jacobiSum_ringHomComp ρ ρ (starRingEnd ℂ)
  rw [hstar, Complex.mul_conj', hcard] at hJ
  have hJn : ‖jacobiSum ρ ρ‖ ^ 2 = Q := by exact_mod_cast hJ
  have hcj : cubicJacobiSum ι P = jacobiSum ρ ρ := by
    rw [cubicJacobiSum, finsum_eq_sum_of_fintype]
    rfl
  rw [jacobiPhaseSix, hcj, norm_mul, norm_inv, norm_pow, norm_pow, Complex.norm_natCast,
    show ‖jacobiSum ρ ρ‖ ^ 6 = (‖jacobiSum ρ ρ‖ ^ 2) ^ 3 by ring, hJn]
  have : (0 : ℝ) < (Q : ℝ) ^ 3 := by have : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
                                     positivity
  rw [← hQdef]
  field_simp

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField Filter

end ArtinPrimitiveRoots

end

section
open ArtinPrimitiveRoots
open NumberField Filter
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), SmallPrimesDvd N₀ 𝔪 → ∀ χ : HeckeChar F 𝔪,
      DifferentiableOn ℂ (χ.principalCorrection ι) {s | 998 / 1000 < s.re} ∧
      (∀ s : ℂ, 998 / 1000 < s.re → χ.principalCorrection ι s ≠ 0) ∧
      ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖χ.principalCorrection ι s‖ ≤ B := by
  have hn3 : 3 ∣ n := (by norm_num : 3 ∣ 12).trans hn
  set d := Module.finrank ℤ (𝓞 F) with hd
  refine ⟨3 ^ (d + 4), fun 𝔪 hS χ => ?_⟩
  set K : Set ℂ := {s | 998 / 1000 < s.re} with hK
  have hKo : IsOpen K := isOpen_lt continuous_const Complex.continuous_re
  -- the index type and its properties
  let J := {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤}
  have hbig : ∀ P : J, 3 ^ (d + 4) < Ideal.absNorm P.1 := by
    intro P
    by_contra h
    have hle := hS P.1 P.2.1 P.2.2.1 (not_lt.mp h)
    have h2 := P.2.2.2
    rw [sup_eq_left.mpr hle] at h2
    exact P.2.1.ne_top h2
  have h30 : ∀ P : J, 30 ≤ Ideal.absNorm P.1 := by
    intro P
    have := hbig P
    have : 81 ≤ 3 ^ (d + 4) := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ (d + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hd3 : ∀ P : J, 3 ^ d < Ideal.absNorm P.1 := by
    intro P
    have := hbig P
    have : 3 ^ d ≤ 3 ^ (d + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have he : ∀ P : J, ‖χ.toFun P.1‖ ≤ 1 := fun P =>
    (T12C_norm_eq_one χ P.1 P.2.2.1 P.2.2.2).le
  have hθ : ∀ P : J,
      ‖starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6‖ ≤ 1 := by
    intro P
    rw [norm_mul, Complex.norm_conj, T12C_norm_jacobiPhaseSix n hn0 hn3 F ι P.1 P.2.1 P.2.2.1
      (hd3 P), norm_pow, T12C_norm_eq_one χ P.1 P.2.2.1 P.2.2.2]
    norm_num
  -- the factors
  set f : J → ℂ → ℂ := fun P s => principalLocalFactor (Ideal.absNorm P.1) (χ.toFun P.1)
    (starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6) s - 1 with hf
  set u : J → ℝ := fun P => 18 * ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-(1998 / 1000 : ℝ)) with hu
  have hfu : ∀ P : J, ∀ s ∈ K, ‖f P s‖ ≤ u P := fun P s hs =>
    (T12C_localFactor_sub_one _ (h30 P) _ _ s (he P) (hθ P) hs).1
  have hus : Summable u := by
    have h1 := T12C_summable_ideal F (α := 1998 / 1000) (by norm_num)
    exact (h1.comp_injective Subtype.coe_injective).mul_left 18
  have hfc : ∀ P : J, ContinuousOn (f P) K := fun P =>
    ((T12C_localFactor_differentiableOn _ (h30 P) _ _ (he P) (hθ P)).sub
      (differentiableOn_const 1)).continuousOn
  have hprod : ∀ s, χ.principalCorrection ι s = ∏' P : J, (1 + f P s) := by
    intro s
    simp only [HeckeChar.principalCorrection, hf, add_sub_cancel]
    rfl
  have hnf : ∀ s ∈ K, Summable fun P : J => ‖f P s‖ := fun s hs =>
    hus.of_nonneg_of_le (fun _ => norm_nonneg _) (fun P => hfu P s hs)
  have hne : ∀ s ∈ K, ∀ P : J, 1 + f P s ≠ 0 := by
    intro s hs P h
    have h1 : f P s = -1 := by linear_combination h
    have := (hfu P s hs).trans_lt (T12C_bound_lt_one _ (h30 P))
    rw [h1, norm_neg, norm_one] at this
    exact lt_irrefl _ this
  refine ⟨?_, ?_, ?_⟩
  · have H := Summable.hasProdLocallyUniformlyOn_one_add hKo hus
      (Eventually.of_forall fun P s hs => hfu P s hs) hfc
    rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at H
    have hD := H.differentiableOn (Eventually.of_forall fun t =>
      DifferentiableOn.fun_finsetProd fun P _ =>
        (differentiableOn_const 1).add ((T12C_localFactor_differentiableOn _ (h30 P) _ _ (he P)
          (hθ P)).sub (differentiableOn_const 1))) hKo
    exact hD.congr fun s _ => hprod s
  · intro s hs
    rw [hprod]
    exact tprod_one_add_ne_zero_of_summable (hne s hs) (hnf s hs)
  · refine ⟨Real.exp (∑' P, u P), fun s hs => ?_⟩
    rw [hprod, (multipliable_one_add_of_summable (hnf s hs)).norm_tprod,
      ← Real.rexp_tsum_eq_tprod (fun P => norm_pos_iff.mpr (hne s hs P))
        (hnf s hs).summable_log_norm_one_add]
    refine Real.exp_le_exp.mpr (Summable.tsum_le_tsum (fun P => ?_)
      (hnf s hs).summable_log_norm_one_add hus)
    have hpos := norm_pos_iff.mpr (hne s hs P)
    calc Real.log ‖1 + f P s‖ ≤ ‖1 + f P s‖ - 1 := Real.log_le_sub_one_of_pos hpos
      _ ≤ ‖f P s‖ := by
        have := norm_add_le (1 : ℂ) (f P s)
        rw [norm_one] at this
        linarith
      _ ≤ u P := hfu P s hs
end
