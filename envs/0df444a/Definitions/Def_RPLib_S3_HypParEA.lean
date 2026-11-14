-- Prove2me | Definitions.Def_RPLib_S3_HypParEA
-- name    : RPLib_S3_HypParEA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:51:22.340996+00:00
-- url     : https://prove2.me/theorems/0e59a9d4-46be-4f09-805a-802edd63aaef
-- title:
--   Integrals over the real line of rational functions with poles off the axis
-- statement:
--   For real $A \ne 0$ and $u_A(s) = s - Ai$: $\int_{\mathbb{R}} (u_A^{-1} - u_B^{-1})\, ds = \pi(\operatorname{sign} A - \operatorname{sign} B)\, i$, $\int_{\mathbb{R}} u_A^{-j}\, ds = 0$ for $j \ge 2$, and related partial-fraction integrals.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill 1979, Section 5.3

import Mathlib

/-!
# S3-HypParTerms, part EA: real-line integrals of rational functions with poles off the axis

For real `A` put `u A s = s - A i` (`s : ℝ`). Pure analysis (imports Mathlib only).

Main results:
* `integral_inv_sub_inv`: `∫ (u_A⁻¹ - u_B⁻¹) = π (sign A - sign B) i` for `A, B ≠ 0`;
* `integral_inv_pow`: `∫ (u_A ^ j)⁻¹ = 0` for `A ≠ 0`, `j ≥ 2`;
* `integral_rat`: for `A, B ≠ 0`, `A ≠ B`, `m ≥ 1`, `s ↦ (u_A ^ m u_B)⁻¹` is integrable and
  `∫ (u_A ^ m u_B)⁻¹ = ((B - A) i) ^ (-m) · π (sign B - sign A) i`.
-/

open Complex MeasureTheory Filter Topology
open scoped Real ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypEA

/-- `u A s = s - A i`. -/
def u (A s : ℝ) : ℂ := (s : ℂ) - (A : ℂ) * I

lemma normSq_u (A s : ℝ) : normSq (u A s) = s ^ 2 + A ^ 2 := by
  simp [u, normSq_apply]; ring

lemma sq_norm_u (A s : ℝ) : ‖u A s‖ ^ 2 = s ^ 2 + A ^ 2 := by
  rw [Complex.sq_norm, normSq_u]

lemma u_ne_zero {A : ℝ} (hA : A ≠ 0) (s : ℝ) : u A s ≠ 0 := by
  intro h
  have h1 := normSq_u A s
  rw [h, map_zero] at h1
  have : 0 < A ^ 2 := by positivity
  nlinarith [sq_nonneg s]

lemma abs_le_norm_u (A s : ℝ) : |A| ≤ ‖u A s‖ := by
  have := Complex.abs_im_le_norm (u A s)
  simpa [u] using this

lemma abs_s_le_norm_u (A s : ℝ) : |s| ≤ ‖u A s‖ := by
  have := Complex.abs_re_le_norm (u A s)
  simpa [u] using this

lemma inv_sq_le {A : ℝ} (hA : A ≠ 0) (s : ℝ) :
    (s ^ 2 + A ^ 2)⁻¹ ≤ (min 1 (A ^ 2))⁻¹ * (1 + s ^ 2)⁻¹ := by
  have hA2 : 0 < A ^ 2 := by positivity
  have hm : 0 < min 1 (A ^ 2) := lt_min one_pos hA2
  rw [← mul_inv]
  apply inv_anti₀ (mul_pos hm (by positivity))
  nlinarith [min_le_left 1 (A ^ 2), min_le_right 1 (A ^ 2), sq_nonneg s]

lemma norm_inv_u_sq_le {A : ℝ} (hA : A ≠ 0) (s : ℝ) :
    ‖(u A s)⁻¹‖ ^ 2 ≤ (min 1 (A ^ 2))⁻¹ * (1 + s ^ 2)⁻¹ := by
  rw [norm_inv, inv_pow, sq_norm_u]; exact inv_sq_le hA s

lemma continuous_u (A : ℝ) : Continuous (u A) := by
  unfold u; fun_prop

/-! ### The difference `u_A⁻¹ - u_B⁻¹` -/

lemma inv_sub_inv_u {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (s : ℝ) :
    (u A s)⁻¹ - (u B s)⁻¹ = ((A - B : ℝ) : ℂ) * I * ((u A s)⁻¹ * (u B s)⁻¹) := by
  rw [inv_sub_inv (u_ne_zero hA s) (u_ne_zero hB s), div_eq_mul_inv, mul_inv]
  congr 1
  unfold u; push_cast; ring

lemma integrable_inv_sub_inv {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) :
    Integrable (fun s : ℝ => (u A s)⁻¹ - (u B s)⁻¹) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul
      (|A - B| * ((min 1 (A ^ 2))⁻¹ + (min 1 (B ^ 2))⁻¹)))
    (((continuous_u A).inv₀ (u_ne_zero hA)).sub
      ((continuous_u B).inv₀ (u_ne_zero hB))).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [inv_sub_inv_u hA hB]
  simp only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h1 := norm_inv_u_sq_le hA s
  have h2 := norm_inv_u_sq_le hB s
  have h3 := two_mul_le_add_sq ‖(u A s)⁻¹‖ ‖(u B s)⁻¹‖
  have h4 : 0 ≤ ‖(u A s)⁻¹‖ * ‖(u B s)⁻¹‖ := by positivity
  have h6 : ‖(u A s)⁻¹‖ * ‖(u B s)⁻¹‖ ≤
      ((min 1 (A ^ 2))⁻¹ + (min 1 (B ^ 2))⁻¹) * (1 + s ^ 2)⁻¹ := by
    nlinarith [sq_nonneg ‖(u A s)⁻¹‖, sq_nonneg ‖(u B s)⁻¹‖]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h6 (abs_nonneg _)

lemma inv_u_eq (A s : ℝ) :
    (u A s)⁻¹ = ((s / (s ^ 2 + A ^ 2) : ℝ) : ℂ) + ((A / (s ^ 2 + A ^ 2) : ℝ) : ℂ) * I := by
  rw [Complex.inv_def, normSq_u]
  simp only [u, map_sub, conj_ofReal, map_mul, conj_I]
  push_cast
  ring

lemma hasDerivAt_re_part {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (Real.log (s ^ 2 + A ^ 2) - Real.log (s ^ 2 + B ^ 2)) / 2)
      (s / (s ^ 2 + A ^ 2) - s / (s ^ 2 + B ^ 2)) s := by
  have hA2 : 0 < s ^ 2 + A ^ 2 := by positivity
  have hB2 : 0 < s ^ 2 + B ^ 2 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + A ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (A ^ 2)
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2 + B ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (B ^ 2)
  refine (((h1.log hA2.ne').sub (h2.log hB2.ne')).div_const 2).congr_deriv ?_
  ring

lemma arctan_deriv_eq {C : ℝ} (hC : C ≠ 0) (s : ℝ) :
    1 / (1 + (s / C) ^ 2) * (1 / C) = C / (s ^ 2 + C ^ 2) := by
  have hD : 0 < s ^ 2 + C ^ 2 := by positivity
  have hC2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hC
  have e : (1 + (s / C) ^ 2) * C = (s ^ 2 + C ^ 2) / C := by
    rw [div_pow, eq_div_iff hC]
    field_simp
    ring
  rw [one_div_mul_one_div, e, one_div_div]

lemma hasDerivAt_im_part {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Real.arctan (s / A) - Real.arctan (s / B))
      (A / (s ^ 2 + A ^ 2) - B / (s ^ 2 + B ^ 2)) s := by
  have h1 := ((hasDerivAt_id' s).div_const A).arctan
  have h2 := ((hasDerivAt_id' s).div_const B).arctan
  refine (h1.sub h2).congr_deriv ?_
  rw [arctan_deriv_eq hA, arctan_deriv_eq hB]

/-- The antiderivative of `u_A⁻¹ - u_B⁻¹`. -/
def Fan (A B : ℝ) (s : ℝ) : ℂ :=
  (((Real.log (s ^ 2 + A ^ 2) - Real.log (s ^ 2 + B ^ 2)) / 2 : ℝ) : ℂ) +
    ((Real.arctan (s / A) - Real.arctan (s / B) : ℝ) : ℂ) * I

lemma hasDerivAt_Fan {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (s : ℝ) :
    HasDerivAt (Fan A B) ((u A s)⁻¹ - (u B s)⁻¹) s := by
  have h := ((hasDerivAt_re_part hA hB s).ofReal_comp).add
    (((hasDerivAt_im_part hA hB s).ofReal_comp).mul_const I)
  refine h.congr_deriv ?_
  rw [inv_u_eq, inv_u_eq]
  push_cast
  ring

lemma tendsto_sq_atTop' : Tendsto (fun s : ℝ => s ^ 2) atTop atTop :=
  tendsto_pow_atTop two_ne_zero

lemma tendsto_sq_atBot' : Tendsto (fun s : ℝ => s ^ 2) atBot atTop := by
  have := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_neg_atBot_atTop
  refine this.congr (fun s => ?_)
  simp only [Function.comp_apply]
  ring

lemma tendsto_log_part (A B : ℝ) {l : Filter ℝ} (hl : Tendsto (fun s : ℝ => s ^ 2) l atTop) :
    Tendsto (fun s : ℝ => (Real.log (s ^ 2 + A ^ 2) - Real.log (s ^ 2 + B ^ 2)) / 2) l (𝓝 0) := by
  have h := ((Real.tendsto_log_comp_add_sub_log (A ^ 2)).sub
    (Real.tendsto_log_comp_add_sub_log (B ^ 2))).div_const 2
  rw [show ((0 : ℝ) - 0) / 2 = 0 by norm_num] at h
  refine (h.comp hl).congr (fun s => ?_)
  simp only [Function.comp_apply]
  ring

lemma tendsto_arctan_div_atTop {A : ℝ} (hA : A ≠ 0) :
    Tendsto (fun s : ℝ => Real.arctan (s / A)) atTop (𝓝 (π / 2 * Real.sign A)) := by
  rcases hA.lt_or_gt with h | h
  · rw [Real.sign_of_neg h, mul_neg_one]
    exact (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const_of_neg h)
  · rw [Real.sign_of_pos h, mul_one]
    exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const h)

lemma tendsto_arctan_div_atBot {A : ℝ} (hA : A ≠ 0) :
    Tendsto (fun s : ℝ => Real.arctan (s / A)) atBot (𝓝 (-(π / 2) * Real.sign A)) := by
  rcases hA.lt_or_gt with h | h
  · rw [Real.sign_of_neg h, mul_neg_one, neg_neg]
    exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      ((tendsto_div_const_atTop_of_neg h).2 tendsto_id)
  · rw [Real.sign_of_pos h, mul_one]
    exact (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atBot_div_const h)

/-- `∫_ℝ (u_A⁻¹ - u_B⁻¹) = π (sign A - sign B) i`. -/
theorem integral_inv_sub_inv {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) :
    ∫ s : ℝ, ((u A s)⁻¹ - (u B s)⁻¹) = ((π * (Real.sign A - Real.sign B) : ℝ) : ℂ) * I := by
  have htop : Tendsto (Fan A B) atTop
      (𝓝 (((0 : ℝ) : ℂ) + ((π / 2 * Real.sign A - π / 2 * Real.sign B : ℝ) : ℂ) * I)) :=
    ((tendsto_log_part A B tendsto_sq_atTop').ofReal).add
      (((tendsto_arctan_div_atTop hA).sub (tendsto_arctan_div_atTop hB)).ofReal.mul_const I)
  have hbot : Tendsto (Fan A B) atBot
      (𝓝 (((0 : ℝ) : ℂ) + ((-(π / 2) * Real.sign A - -(π / 2) * Real.sign B : ℝ) : ℂ) * I)) :=
    ((tendsto_log_part A B tendsto_sq_atBot').ofReal).add
      (((tendsto_arctan_div_atBot hA).sub (tendsto_arctan_div_atBot hB)).ofReal.mul_const I)
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_Fan hA hB) (integrable_inv_sub_inv hA hB)
    hbot htop]
  push_cast
  ring

/-! ### Powers `u_A ^ j`, `j ≥ 2` -/

lemma tendsto_norm_u_atTop (A : ℝ) : Tendsto (fun s => ‖u A s‖) atTop atTop :=
  tendsto_atTop_mono (fun s => (le_abs_self s).trans (abs_s_le_norm_u A s)) tendsto_id

lemma tendsto_norm_u_atBot (A : ℝ) : Tendsto (fun s => ‖u A s‖) atBot atTop :=
  tendsto_atTop_mono (fun s => (neg_le_abs s).trans (abs_s_le_norm_u A s)) tendsto_neg_atBot_atTop

lemma tendsto_inv_pow_zero {l : Filter ℝ} {v : ℝ → ℂ} (hv : Tendsto (fun s => ‖v s‖) l atTop)
    {k : ℕ} (hk : k ≠ 0) : Tendsto (fun s => (v s ^ k)⁻¹) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv, norm_pow]
  exact tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop hk).comp hv)

lemma hasDerivAt_inv_pow_u {A : ℝ} (hA : A ≠ 0) (i : ℕ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ((u A s) ^ (i + 1))⁻¹ * (-((i : ℂ) + 1))⁻¹)
      (((u A s) ^ (i + 2))⁻¹) s := by
  have hne : ((s : ℂ) - (A : ℂ) * I) ≠ 0 := u_ne_zero hA s
  have h := (((((hasDerivAt_id' ((s : ℂ))).sub_const ((A : ℂ) * I)).pow (i + 1)).inv
    (pow_ne_zero _ hne)).mul_const (-((i : ℂ) + 1))⁻¹).comp_ofReal
  refine h.congr_deriv ?_
  have hi : ((i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  simp only [Pi.pow_apply]
  rw [show u A s = (s : ℂ) - (A : ℂ) * I from rfl, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

lemma integrable_inv_pow {A : ℝ} (hA : A ≠ 0) {j : ℕ} (hj : 2 ≤ j) :
    Integrable (fun s : ℝ => ((u A s) ^ j)⁻¹) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hj
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul ((|A| ^ i)⁻¹ * (min 1 (A ^ 2))⁻¹))
    (((continuous_u A).pow (i + 2)).inv₀
      (fun s => pow_ne_zero _ (u_ne_zero hA s))).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  have hAi : 0 < |A| ^ i := pow_pos (abs_pos.2 hA) i
  have h1 : |A| ^ i ≤ ‖u A s‖ ^ i := pow_le_pow_left₀ (abs_nonneg A) (abs_le_norm_u A s) i
  rw [norm_inv, norm_pow, pow_add, sq_norm_u, mul_inv]
  have h2 := inv_sq_le hA s
  have h3 : (‖u A s‖ ^ i)⁻¹ ≤ (|A| ^ i)⁻¹ := inv_anti₀ hAi h1
  have hm : 0 < min 1 (A ^ 2) := lt_min one_pos (by positivity)
  calc (‖u A s‖ ^ i)⁻¹ * (s ^ 2 + A ^ 2)⁻¹
      ≤ (|A| ^ i)⁻¹ * ((min 1 (A ^ 2))⁻¹ * (1 + s ^ 2)⁻¹) :=
        mul_le_mul h3 h2 (by positivity) (by positivity)
    _ = _ := by ring

/-- `∫_ℝ (u_A ^ j)⁻¹ = 0` for `j ≥ 2`. -/
theorem integral_inv_pow {A : ℝ} (hA : A ≠ 0) {j : ℕ} (hj : 2 ≤ j) :
    ∫ s : ℝ, ((u A s) ^ j)⁻¹ = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hj
  have hbot : Tendsto (fun s : ℝ => ((u A s) ^ (i + 1))⁻¹ * (-((i : ℂ) + 1))⁻¹) atBot (𝓝 0) := by
    have := (tendsto_inv_pow_zero (tendsto_norm_u_atBot A) (Nat.succ_ne_zero i)).mul_const
      (-((i : ℂ) + 1))⁻¹
    rwa [zero_mul] at this
  have htop : Tendsto (fun s : ℝ => ((u A s) ^ (i + 1))⁻¹ * (-((i : ℂ) + 1))⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_pow_zero (tendsto_norm_u_atTop A) (Nat.succ_ne_zero i)).mul_const
      (-((i : ℂ) + 1))⁻¹
    rwa [zero_mul] at this
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_inv_pow_u hA i) (integrable_inv_pow hA hj)
    hbot htop, sub_self]

/-! ### The rational function `(u_A ^ m u_B)⁻¹` -/

/-- For `A, B ≠ 0`, `A ≠ B`, `m ≥ 1`: `(u_A ^ m u_B)⁻¹` is integrable on `ℝ` and
`∫ (u_A ^ m u_B)⁻¹ = ((B - A) i) ^ (-m) π (sign B - sign A) i`. -/
theorem integral_rat {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B) {m : ℕ} (hm : 1 ≤ m) :
    Integrable (fun s : ℝ => ((u A s) ^ m * u B s)⁻¹) ∧
    ∫ s : ℝ, ((u A s) ^ m * u B s)⁻¹ =
      ((((B - A : ℝ) : ℂ) * I) ^ m)⁻¹ * (((π * (Real.sign B - Real.sign A) : ℝ) : ℂ) * I) := by
  set c : ℂ := ((B - A : ℝ) : ℂ) * I with hc
  have hc0 : c ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 (sub_ne_zero.2 hAB.symm)) I_ne_zero
  have hcu : ∀ s : ℝ, c = u A s - u B s := fun s => by rw [hc]; unfold u; push_cast; ring
  induction m, hm using Nat.le_induction with
  | base =>
    have hpt : ∀ s : ℝ, ((u A s) ^ 1 * u B s)⁻¹ = c⁻¹ * ((u B s)⁻¹ - (u A s)⁻¹) := by
      intro s
      have hA' := u_ne_zero hA s
      have hB' := u_ne_zero hB s
      have hd : u A s - u B s ≠ 0 := by rw [← hcu s]; exact hc0
      rw [hcu s]
      field_simp
    simp_rw [hpt]
    refine ⟨(integrable_inv_sub_inv hB hA).const_mul _, ?_⟩
    rw [integral_const_mul, integral_inv_sub_inv hB hA, pow_one]
  | succ n hn ih =>
    obtain ⟨hint, heq⟩ := ih
    have hint2 : Integrable (fun s : ℝ => ((u A s) ^ (n + 1))⁻¹) := integrable_inv_pow hA (by omega)
    have hpt : ∀ s : ℝ, ((u A s) ^ (n + 1) * u B s)⁻¹ =
        c⁻¹ * (((u A s) ^ n * u B s)⁻¹ - ((u A s) ^ (n + 1))⁻¹) := by
      intro s
      have hA' := u_ne_zero hA s
      have hB' := u_ne_zero hB s
      have hd : u A s - u B s ≠ 0 := by rw [← hcu s]; exact hc0
      rw [hcu s]
      field_simp
      ring
    simp_rw [hpt]
    refine ⟨(hint.sub hint2).const_mul _, ?_⟩
    rw [integral_const_mul, integral_sub hint hint2, heq, integral_inv_pow hA (by omega), sub_zero]
    ring

end RamanujanPetersson.HypEA


