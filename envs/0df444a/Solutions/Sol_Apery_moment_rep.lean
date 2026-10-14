-- Prove2me | solution 1 for Apery.moment_rep
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-11T23:22:29.875998+00:00
-- url     : https://prove2.me/submissions/db7242ec-b1fa-4633-87c4-a28af653a571

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# Proposition 2.2 (moment representation) — port of `Apery/Positivity.lean`

This file proves the platform theorem `Apery.moment_rep`:

  `IntegrableOn (integrand K P) (Set.Ioi 0) ∧
     aeval zeta5 (μX K P) = ∫ y in Set.Ioi 0, integrand K P y`

The development is a faithful port of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, modules
`Apery/Weight.lean`, `Apery/Moments.lean`, `Apery/PartialFractions.lean`
(with the elementary `D`-evaluation lemmas from `Apery/Degree.lean`),
`Apery/Hermite.lean`, `Apery/HermiteIntegrals.lean`, `Apery/HermiteIBP.lean`,
`Apery/HermiteFormula.lean`, and the moment-representation part of
`Apery/Positivity.lean`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_MomentWeight

set_option autoImplicit false

section Port0
/-!
# The weight `w` of (2.10) — port of `Apery/Weight.lean`

`w(y) = (2π)⁴ y⁵ / 12 · ∑_{ℓ ≥ 1} ℓ⁴ e^{-2πℓy}`; its positivity, the bound
`w(y) ≤ (32 y + 11) e^{-π y}`, and a.e.-measurability on `(0, ∞)`.
The definitions `wS`, `w` themselves are platform definitions
(`Definitions.Def_Zeta5_MomentWeight`); this module ports only the lemmas.

Source: mo271/Zeta5 @ 7fe7367, `Apery/Weight.lean`.
-/

open MeasureTheory Set Filter Topology

namespace Apery

lemma summable_w_term {y : ℝ} (hy : 0 < y) :
    Summable fun ℓ : ℕ => ((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y)) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul 4 (r := 2 * Real.pi * y) (by positivity)
  have h2 := (summable_nat_add_iff 1).mpr h
  refine h2.congr fun ℓ => ?_
  push_cast
  ring_nf

lemma wS_pos {y : ℝ} (hy : 0 < y) : 0 < wS y :=
  (summable_w_term hy).tsum_pos (fun ℓ => by positivity) 0 (by positivity)

lemma w_pos {y : ℝ} (hy : 0 < y) : 0 < w y := by
  unfold w; have := wS_pos hy; positivity

/-- `1 / (1 - e^{-x}) ≤ 1 + 1 / x` for `x > 0`. -/
lemma one_div_one_sub_exp_neg_le {x : ℝ} (hx : 0 < x) :
    1 / (1 - Real.exp (-x)) ≤ 1 + 1 / x := by
  have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h2 : Real.exp (-x) = 1 / Real.exp x := by rw [Real.exp_neg, one_div]
  have h3 : 0 < Real.exp x := Real.exp_pos x
  have h4 : Real.exp (-x) < 1 := by rw [h2, div_lt_one h3]; linarith
  rw [div_le_iff₀ (by linarith), h2]
  have hid : (1 + 1 / x) * (1 - 1 / Real.exp x) =
      1 + (Real.exp x - x - 1) / (x * Real.exp x) := by
    field_simp
    ring
  rw [hid]
  have : 0 ≤ (Real.exp x - x - 1) / (x * Real.exp x) := div_nonneg (by linarith) (by positivity)
  linarith

/-- The bound `wS y ≤ 24 (1 + 1/(πy)) e^{-πy} / (πy)⁴`. -/
lemma wS_le {y : ℝ} (hy : 0 < y) :
    wS y ≤ 24 / (Real.pi * y) ^ 4 * (1 + 1 / (Real.pi * y)) * Real.exp (-(Real.pi * y)) := by
  have hpy : 0 < Real.pi * y := by positivity
  set q : ℝ := Real.exp (-(Real.pi * y)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  -- termwise bound
  have hterm : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y)) ≤
      24 / (Real.pi * y) ^ 4 * (q * q ^ ℓ) := by
    intro ℓ
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) + 1 := by positivity
    have hpow := Real.pow_div_factorial_le_exp (x := Real.pi * y * ((ℓ : ℝ) + 1)) (by positivity) 4
    have hexp : Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y)) =
        Real.exp (-(Real.pi * y * ((ℓ : ℝ) + 1))) * (q * q ^ ℓ) := by
      rw [hq, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [hexp]
    have hE : Real.exp (-(Real.pi * y * ((ℓ : ℝ) + 1))) = 1 / Real.exp (Real.pi * y * ((ℓ : ℝ) + 1)) := by
      rw [Real.exp_neg, one_div]
    rw [hE]
    have hEpos : 0 < Real.exp (Real.pi * y * ((ℓ : ℝ) + 1)) := Real.exp_pos _
    have hqq : 0 ≤ q * q ^ ℓ := by positivity
    have key : ((ℓ : ℝ) + 1) ^ 4 * (1 / Real.exp (Real.pi * y * ((ℓ : ℝ) + 1))) ≤
        24 / (Real.pi * y) ^ 4 := by
      rw [mul_one_div, div_le_div_iff₀ hEpos (by positivity)]
      have : (Real.pi * y * ((ℓ : ℝ) + 1)) ^ 4 / (4 : ℕ).factorial =
          (Real.pi * y) ^ 4 * ((ℓ : ℝ) + 1) ^ 4 / 24 := by
        rw [Nat.factorial]; norm_num; ring
      rw [this] at hpow
      nlinarith [pow_pos hpy 4]
    calc ((ℓ : ℝ) + 1) ^ 4 * (1 / Real.exp (Real.pi * y * ((ℓ : ℝ) + 1)) * (q * q ^ ℓ))
        = (((ℓ : ℝ) + 1) ^ 4 * (1 / Real.exp (Real.pi * y * ((ℓ : ℝ) + 1)))) * (q * q ^ ℓ) := by
          ring
      _ ≤ 24 / (Real.pi * y) ^ 4 * (q * q ^ ℓ) := mul_le_mul_of_nonneg_right key hqq
  have hgeom : Summable fun ℓ : ℕ => 24 / (Real.pi * y) ^ 4 * (q * q ^ ℓ) :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left q).mul_left _
  calc wS y ≤ ∑' ℓ : ℕ, 24 / (Real.pi * y) ^ 4 * (q * q ^ ℓ) :=
        (summable_w_term hy).tsum_le_tsum hterm hgeom
    _ = 24 / (Real.pi * y) ^ 4 * (q * (1 / (1 - q))) := by
        rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, one_div]
    _ ≤ 24 / (Real.pi * y) ^ 4 * (1 + 1 / (Real.pi * y)) * q := by
        have h := one_div_one_sub_exp_neg_le hpy
        rw [← hq] at h
        have h24 : 0 ≤ 24 / (Real.pi * y) ^ 4 := by positivity
        calc 24 / (Real.pi * y) ^ 4 * (q * (1 / (1 - q)))
            ≤ 24 / (Real.pi * y) ^ 4 * (q * (1 + 1 / (Real.pi * y))) := by gcongr
          _ = 24 / (Real.pi * y) ^ 4 * (1 + 1 / (Real.pi * y)) * q := by ring

/-- The bound `w(y) ≤ (32 y + 11) e^{-πy}` for `y > 0`. -/
lemma w_le {y : ℝ} (hy : 0 < y) : w y ≤ (32 * y + 11) * Real.exp (-(Real.pi * y)) := by
  unfold w
  have h := wS_le hy
  have hpi := Real.pi_gt_three
  have hpy : 0 < Real.pi * y := by positivity
  have hc : 0 ≤ (2 * Real.pi) ^ 4 * y ^ 5 / 12 := by positivity
  calc (2 * Real.pi) ^ 4 * y ^ 5 / 12 * wS y
      ≤ (2 * Real.pi) ^ 4 * y ^ 5 / 12 *
          (24 / (Real.pi * y) ^ 4 * (1 + 1 / (Real.pi * y)) * Real.exp (-(Real.pi * y))) :=
        mul_le_mul_of_nonneg_left h hc
    _ = (32 * y + 32 / Real.pi) * Real.exp (-(Real.pi * y)) := by
        field_simp
        ring
    _ ≤ (32 * y + 11) * Real.exp (-(Real.pi * y)) := by
        have : 32 / Real.pi ≤ 11 := by
          rw [div_le_iff₀ (by positivity)]; linarith
        have he : 0 ≤ Real.exp (-(Real.pi * y)) := (Real.exp_pos _).le
        nlinarith

/-- `wS` is a.e.-measurable on `(0, ∞)`, as the pointwise limit of continuous partial sums. -/
lemma aemeasurable_wS : AEMeasurable wS (volume.restrict (Ioi 0)) := by
  refine aemeasurable_of_tendsto_metrizable_ae' (f := fun n y =>
    ∑ ℓ ∈ Finset.range n, ((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y))) ?_ ?_
  · intro n
    refine (Continuous.measurable ?_).aemeasurable
    exact continuous_finsetSum _ fun ℓ _ => continuous_const.mul (Real.continuous_exp.comp (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    exact (summable_w_term hy).hasSum.tendsto_sum_nat

lemma aemeasurable_w : AEMeasurable w (volume.restrict (Ioi 0)) := by
  unfold w
  exact (aemeasurable_const.mul (measurable_id.pow_const 5).aemeasurable |>.div_const 12).mul
    aemeasurable_wS

end Apery
end Port0

section Port1
/-!
# The polynomial moments of the weight `w` — port of `Apery/Moments.lean`

`∫₀^∞ y^{2e} w(y) dy = μ(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5) / 24`.

Source: mo271/Zeta5 @ 7fe7367, `Apery/Moments.lean`.
-/

open MeasureTheory Set Filter Topology Finset

namespace Apery

/-- `∫₀^∞ y^m e^{-ry} dy = m! / r^(m+1)`. -/
lemma integral_pow_mul_exp_neg_mul (m : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ y in Ioi 0, y ^ m * Real.exp (-(r * y)) = (m.factorial : ℝ) / r ^ (m + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (m : ℝ) + 1) (by positivity) hr
  rw [Real.Gamma_nat_eq_factorial, add_sub_cancel_right] at h
  have hL : ∫ y in Ioi 0, y ^ m * Real.exp (-(r * y)) =
      ∫ t in Ioi 0, t ^ (m : ℝ) * Real.exp (-(r * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [Real.rpow_natCast]
  rw [hL, h]
  have : (1 / r) ^ ((m : ℝ) + 1) = (1 / r) ^ (m + 1) := by
    rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [this, one_div_pow, div_mul_eq_mul_div, one_mul]

lemma integrableOn_pow_mul_exp_neg_mul (m : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => y ^ m * Real.exp (-(r * y))) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (m : ℝ) + 1) (by positivity)
  rw [add_sub_cancel_right] at h
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-(r * x)) * (r * x) ^ (m : ℝ)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x) * x ^ (m : ℝ)) 0 hr).mpr
      (by simpa using h)
    simpa using this
  have h3 : IntegrableOn (fun x : ℝ => (1 / r ^ m) * (Real.exp (-(r * x)) * (r * x) ^ (m : ℝ)))
      (Ioi 0) := h2.const_mul _
  refine h3.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx : 0 < x := hx
  simp only
  rw [Real.rpow_natCast, mul_pow]
  field_simp

/-- The summand `y^{2e} · (2π)⁴ y⁵ / 12 · (ℓ+1)⁴ e^{-2π(ℓ+1)y}`. -/
noncomputable def momTerm (e ℓ : ℕ) (y : ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 / 12 * ((ℓ : ℝ) + 1) ^ 4 *
    (y ^ (2 * e + 5) * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y)))

lemma momTerm_eq (e ℓ : ℕ) (y : ℝ) : momTerm e ℓ y =
    y ^ (2 * e) * ((2 * Real.pi) ^ 4 * y ^ 5 / 12) *
      (((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y))) := by
  unfold momTerm; ring

lemma integrableOn_momTerm (e ℓ : ℕ) : IntegrableOn (momTerm e ℓ) (Ioi 0) := by
  unfold momTerm
  exact (integrableOn_pow_mul_exp_neg_mul (2 * e + 5) (r := 2 * Real.pi * ((ℓ : ℝ) + 1))
    (by positivity)).const_mul _

lemma integral_momTerm (e ℓ : ℕ) :
    ∫ y in Ioi 0, momTerm e ℓ y =
      (2 * Real.pi) ^ 4 / 12 * ((2 * e + 5).factorial : ℝ) / (2 * Real.pi) ^ (2 * e + 6) *
        (1 / ((ℓ : ℝ) + 1) ^ (2 * e + 2)) := by
  unfold momTerm
  rw [integral_const_mul, integral_pow_mul_exp_neg_mul _ (by positivity)]
  have hl : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [mul_pow (2 * Real.pi) ((ℓ : ℝ) + 1)]
  have hsplit : ((ℓ : ℝ) + 1) ^ (2 * e + 5 + 1) =
      ((ℓ : ℝ) + 1) ^ 4 * ((ℓ : ℝ) + 1) ^ (2 * e + 2) := by ring
  rw [hsplit]
  field_simp

lemma momTerm_nonneg (e ℓ : ℕ) {y : ℝ} (hy : 0 < y) : 0 ≤ momTerm e ℓ y := by
  unfold momTerm; positivity

/-- **The polynomial moments**: `∫₀^∞ y^{2e} w(y) dy = μ(t^e)`, with integrability. -/
theorem mono_moment (e : ℕ) :
    IntegrableOn (fun y => y ^ (2 * e) * w y) (Ioi 0) ∧
      ∫ y in Ioi 0, y ^ (2 * e) * w y = ((μmono e : ℚ) : ℝ) := by
  have hpt : ∀ y, y ^ (2 * e) * w y = ∑' ℓ, momTerm e ℓ y := by
    intro y
    simp_rw [momTerm_eq]
    rw [tsum_mul_left]
    unfold w wS; ring
  have hnorm : ∀ ℓ, ∫ y in Ioi 0, ‖momTerm e ℓ y‖ = ∫ y in Ioi 0, momTerm e ℓ y := by
    intro ℓ
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    exact Real.norm_of_nonneg (momTerm_nonneg e ℓ hy)
  have hsum : Summable fun ℓ => ∫ y in Ioi 0, ‖momTerm e ℓ y‖ := by
    simp_rw [hnorm, integral_momTerm]
    refine Summable.mul_left _ ?_
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2 * e + 2))
    refine this.congr fun ℓ => ?_
    push_cast; ring
  have hint := integral_tsum_of_summable_integral_norm (fun ℓ => integrableOn_momTerm e ℓ) hsum
  constructor
  · -- integrability by domination
    have hg : IntegrableOn (fun y : ℝ => 32 * (y ^ (2 * e + 1) * Real.exp (-(Real.pi * y))) +
        11 * (y ^ (2 * e) * Real.exp (-(Real.pi * y)))) (Ioi 0) :=
      ((integrableOn_pow_mul_exp_neg_mul (2 * e + 1) Real.pi_pos).const_mul 32).add
        ((integrableOn_pow_mul_exp_neg_mul (2 * e) Real.pi_pos).const_mul 11)
    refine hg.mono' ((measurable_id.pow_const _).aemeasurable.mul aemeasurable_w).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    have hy : 0 < y := hy
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (w_pos hy).le)]
    have := mul_le_mul_of_nonneg_left (w_le hy) (by positivity : (0 : ℝ) ≤ y ^ (2 * e))
    calc y ^ (2 * e) * w y ≤ y ^ (2 * e) * ((32 * y + 11) * Real.exp (-(Real.pi * y))) := this
      _ = _ := by ring
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => hpt y), ← hint]
    simp_rw [integral_momTerm]
    rw [tsum_mul_left]
    -- Euler's formula
    have hz := hasSum_zeta_nat (k := e + 1) (by omega)
    have hz1 := (hasSum_nat_add_iff' 1).mpr hz
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq,
      Nat.mul_eq_zero, OfNat.ofNat_ne_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, or_self,
      not_false_eq_true, zero_pow, div_zero, sub_zero] at hz1
    have hS : ∑' ℓ : ℕ, 1 / ((ℓ : ℝ) + 1) ^ (2 * e + 2) =
        (-1 : ℝ) ^ (e + 1 + 1) * (2 : ℝ) ^ (2 * (e + 1) - 1) * Real.pi ^ (2 * (e + 1)) *
          (bernoulli (2 * (e + 1)) : ℝ) / (2 * (e + 1)).factorial := by
      rw [← hz1.tsum_eq]
      refine tsum_congr fun ℓ => ?_
      push_cast
      ring_nf
    rw [hS]
    have hfac : ((2 * e + 5).factorial : ℝ) =
        ((2 * e + 5) * (2 * e + 4) * (2 * e + 3) : ℕ) * ((2 * e + 2).factorial : ℝ) := by
      rw [show 2 * e + 5 = (2 * e + 4) + 1 from rfl, Nat.factorial_succ,
        show 2 * e + 4 = (2 * e + 3) + 1 from rfl, Nat.factorial_succ,
        show 2 * e + 3 = (2 * e + 2) + 1 from rfl, Nat.factorial_succ]
      push_cast; ring
    rw [show 2 * (e + 1) = 2 * e + 2 by ring, show 2 * e + 2 - 1 = 2 * e + 1 by omega, hfac]
    unfold μmono
    push_cast
    have hfac2 : (0 : ℝ) < ((2 * e + 2).factorial : ℝ) := by positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    field_simp
    ring

end Apery
end Port1

section Port2
/-!
# Partial fractions for `P / D_K` — port of `Apery/PartialFractions.lean`

For a polynomial `P` and `t ≥ 0`, `P(t) / D_K(t) = (P /ₘ D_K)(t) + ∑_j res_j / (t + j²)`
with `res_j = P(-j²) / D_K'(-j²)`, the residues used in the definition of `μ_X`.
This module also ports the elementary `D`-evaluation lemmas from `Apery/Degree.lean`
that the partial-fraction identity uses.

Source: mo271/Zeta5 @ 7fe7367, `Apery/PartialFractions.lean`, `Apery/Degree.lean`.
-/

open Polynomial Finset

namespace Apery

lemma D_monic (K : ℕ) : (D K).Monic := by
  unfold D; exact monic_prod_of_monic _ _ fun j _ => monic_X_add_C _

lemma natDegree_D (K : ℕ) : (D K).natDegree = K := by
  unfold D; rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
  omega

/-- The residues `res_j = P(-j²) / D_K'(-j²)`. -/
noncomputable def res (K : ℕ) (P : ℚ[X]) (j : ℕ) : ℚ :=
  P.eval (-(j : ℚ) ^ 2) / (derivative (D K)).eval (-(j : ℚ) ^ 2)

lemma eval_D (m : ℕ) (x : ℚ) : (D m).eval x = ∏ j ∈ Icc 1 m, (x + (j : ℚ) ^ 2) := by
  simp [D, eval_prod]

lemma eval_D_eq_zero {m j : ℕ} (hj : j ∈ Icc 1 m) : (D m).eval (-(j : ℚ) ^ 2) = 0 := by
  rw [eval_D]
  exact Finset.prod_eq_zero hj (by ring)

lemma eval_derivative_D {K j : ℕ} (hj : j ∈ Icc 1 K) :
    (derivative (D K)).eval (-(j : ℚ) ^ 2) = ∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) := by
  rw [D, derivative_prod_finset, eval_finsetSum, Finset.sum_eq_single j]
  · simp only [derivative_add, derivative_X, derivative_C, add_zero, eval_mul, eval_one, mul_one,
      eval_prod, eval_add, eval_X, eval_C]
    exact Finset.prod_congr rfl fun i _ => by ring
  · intro b _ hb
    rw [eval_mul, eval_prod]
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hb.symm, hj⟩) (by simp)) _
  · intro h; exact absurd hj h

lemma eval_derivative_D_ne_zero {K j : ℕ} (hj : j ∈ Icc 1 K) :
    (derivative (D K)).eval (-(j : ℚ) ^ 2) ≠ 0 := by
  rw [eval_derivative_D hj]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  have hij : i ≠ j := (Finset.mem_erase.mp hi).1
  have : (i : ℚ) ≠ j := by exact_mod_cast hij
  have h0i : (0 : ℚ) ≤ i := by positivity
  have h0j : (0 : ℚ) ≤ j := by positivity
  intro h
  have hfac : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact this (by linarith)
  · have hj1 : (1 : ℚ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    linarith

/-- The polynomial identity behind the partial fractions: the remainder `P %ₘ D_K` equals
`∑_j res_j ∏_{i ≠ j} (X + i²)`. -/
lemma modByMonic_eq_sum_res (K : ℕ) (P : ℚ[X]) :
    P %ₘ D K = ∑ j ∈ Icc 1 K, C (res K P j) * ∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2)) := by
  have hnodes : Set.InjOn (fun j : ℕ => -(j : ℚ) ^ 2) (Icc 1 K : Set ℕ) := by
    intro a _ b _ hab
    have h1 : (a : ℚ) ^ 2 = (b : ℚ) ^ 2 := by simpa using hab
    have h2 : a ^ 2 = b ^ 2 := by exact_mod_cast h1
    exact Nat.pow_left_injective two_ne_zero h2
  set s : Finset ℚ := (Icc 1 K).image (fun j : ℕ => -(j : ℚ) ^ 2) with hs
  have hcard : s.card = K := by
    rw [hs, Finset.card_image_of_injOn hnodes]; simp
  -- degree of each summand
  have hterm : ∀ j ∈ Icc 1 K,
      (C (res K P j) * ∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).degree < K := by
    intro j hj
    have hK : 1 ≤ K := (Finset.mem_Icc.mp hj).2.trans' (Finset.mem_Icc.mp hj).1
    have hprod : (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).natDegree = K - 1 := by
      rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C _]
      simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem hj, Nat.card_Icc]
      omega
    calc (C (res K P j) * ∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).degree
        ≤ (C (res K P j)).degree + (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).degree :=
          degree_mul_le _ _
      _ ≤ 0 + ((K - 1 : ℕ) : WithBot ℕ) := by
          gcongr
          · exact degree_C_le
          · rw [← hprod]; exact degree_le_natDegree
      _ < K := by
          rw [zero_add]; exact_mod_cast (by omega : K - 1 < K)
  refine eq_of_degree_sub_lt_of_eval_finset_eq s ?_ ?_
  · rw [hcard]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · rcases eq_or_ne (P %ₘ D K) 0 with h | h
      · rw [h, degree_zero]; exact WithBot.bot_lt_coe _
      · have := degree_modByMonic_lt P (D_monic K)
        rwa [degree_eq_natDegree (D_monic K).ne_zero, natDegree_D] at this
    · refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      exact (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr hterm
  · intro x hx
    rw [hs, Finset.mem_image] at hx
    obtain ⟨j₀, hj₀, rfl⟩ := hx
    -- LHS: `(P %ₘ D_K)(-j₀²) = P(-j₀²)`
    have hL : (P %ₘ D K).eval (-(j₀ : ℚ) ^ 2) = P.eval (-(j₀ : ℚ) ^ 2) := by
      conv_rhs => rw [← modByMonic_add_div P (D K)]
      rw [eval_add, eval_mul, eval_D_eq_zero hj₀, zero_mul, add_zero]
    rw [hL, eval_finsetSum, Finset.sum_eq_single j₀]
    · rw [eval_mul, eval_C, eval_prod, res, eval_derivative_D hj₀]
      have hne := eval_derivative_D_ne_zero hj₀
      rw [eval_derivative_D hj₀] at hne
      have : ∏ i ∈ (Icc 1 K).erase j₀, eval (-(j₀ : ℚ) ^ 2) (X + C ((i : ℚ) ^ 2)) =
          ∏ i ∈ (Icc 1 K).erase j₀, ((i : ℚ) ^ 2 - (j₀ : ℚ) ^ 2) :=
        Finset.prod_congr rfl fun i _ => by simp; ring
      rw [this, div_mul_cancel₀ _ hne]
    · intro j hj hjne
      rw [eval_mul, eval_prod]
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := j₀) ?_ ?_)
      · exact Finset.mem_erase.mpr ⟨fun h => hjne h.symm, hj₀⟩
      · simp
    · intro h; exact absurd hj₀ h

lemma aeval_D_pos (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 < aeval t (D m) := by
  simp only [D, map_prod, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
  refine Finset.prod_pos fun j hj => ?_
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  positivity

/-- **Partial fractions** as real functions, for `t ≥ 0`. -/
theorem partial_fractions (K : ℕ) (P : ℚ[X]) {t : ℝ} (ht : 0 ≤ t) :
    aeval t P / aeval t (D K) =
      aeval t (P /ₘ D K) + ∑ j ∈ Icc 1 K, (res K P j : ℝ) / (t + (j : ℝ) ^ 2) := by
  have hD : 0 < aeval t (D K) := aeval_D_pos K ht
  have hsplit : aeval t P = aeval t (P %ₘ D K) + aeval t (D K) * aeval t (P /ₘ D K) := by
    conv_lhs => rw [← modByMonic_add_div P (D K)]
    rw [map_add, map_mul]
  rw [hsplit, add_div, mul_div_cancel_left₀ _ hD.ne', add_comm]
  congr 1
  rw [modByMonic_eq_sum_res, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_mul, aeval_C, map_prod]
  simp only [map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
  have hj2 : 0 < t + (j : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    positivity
  have hDt : aeval t (D K) = (t + (j : ℝ) ^ 2) * ∏ i ∈ (Icc 1 K).erase j, (t + (i : ℝ) ^ 2) := by
    simp only [D, map_prod, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
    rw [← Finset.mul_prod_erase _ _ hj]
  rw [hDt]
  have hprod : 0 < ∏ i ∈ (Icc 1 K).erase j, (t + (i : ℝ) ^ 2) :=
    Finset.prod_pos fun i hi => by
      have : (1 : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
      positivity
  field_simp

end Apery
end Port2

section Port3
/-!
# Towards Hermite's formula at `s = 5`: the calculus ingredients — port of `Apery/Hermite.lean`

* the closed form `∑_{ℓ ≥ 1} ℓ⁴ x^ℓ = x (1 + 11x + 11x² + x³) / (1 - x)⁵` for `0 ≤ x < 1`;
* `F(y) = 1 / (e^{2πy} - 1)` and its derivatives `F₁, …, F₄`, with `w(y) = y⁵ F₄(y) / 12`;
* `g(y) = y⁵ / (12 (y² + a²))` and its derivatives;
* the Mittag-Leffler expansion of `F`.

Source: mo271/Zeta5 @ 7fe7367, `Apery/Hermite.lean`.
-/

open Filter Topology Finset

namespace Apery

/-! ### The series `∑ ℓ⁴ x^ℓ` -/

/-- The telescoping polynomial: `(1 - x)⁵ ∑_{ℓ < N} (ℓ+1)⁴ x^{ℓ+1} = x(1+11x+11x²+x³) - x^{N+1} P(N, x)`. -/
noncomputable def Ptel (N x : ℝ) : ℝ :=
  N ^ 4 * x ^ 4 - 4 * N ^ 4 * x ^ 3 + 6 * N ^ 4 * x ^ 2 - 4 * N ^ 4 * x + N ^ 4 - 4 * N ^ 3 * x ^ 3 +
    12 * N ^ 3 * x ^ 2 - 12 * N ^ 3 * x + 4 * N ^ 3 + 6 * N ^ 2 * x ^ 3 - 6 * N ^ 2 * x ^ 2 -
    6 * N ^ 2 * x + 6 * N ^ 2 - 4 * N * x ^ 3 - 12 * N * x ^ 2 + 12 * N * x + 4 * N + x ^ 3 +
    11 * x ^ 2 + 11 * x + 1

lemma telescope (x : ℝ) (N : ℕ) :
    (1 - x) ^ 5 * ∑ ℓ ∈ range N, ((ℓ : ℝ) + 1) ^ 4 * x ^ (ℓ + 1) =
      x * (1 + 11 * x + 11 * x ^ 2 + x ^ 3) - x ^ (N + 1) * Ptel N x := by
  induction N with
  | zero => simp [Ptel]; ring
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    unfold Ptel
    ring

lemma tendsto_pow_mul_Ptel {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun N : ℕ => x ^ (N + 1) * Ptel N x) atTop (𝓝 0) := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h : ∀ k : ℕ, Tendsto (fun N : ℕ => (N : ℝ) ^ k * x ^ N) atTop (𝓝 0) :=
    fun k => tendsto_pow_const_mul_const_pow_of_abs_lt_one k habs
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  have : (fun N : ℕ => x ^ (N + 1) * Ptel N x) = fun N : ℕ =>
      ((N : ℝ) ^ 4 * x ^ N) * (x ^ 5 - 4 * x ^ 4 + 6 * x ^ 3 - 4 * x ^ 2 + x) +
      ((N : ℝ) ^ 3 * x ^ N) * (-4 * x ^ 4 + 12 * x ^ 3 - 12 * x ^ 2 + 4 * x) +
      ((N : ℝ) ^ 2 * x ^ N) * (6 * x ^ 4 - 6 * x ^ 3 - 6 * x ^ 2 + 6 * x) +
      ((N : ℝ) ^ 1 * x ^ N) * (-4 * x ^ 4 - 12 * x ^ 3 + 12 * x ^ 2 + 4 * x) +
      ((N : ℝ) ^ 0 * x ^ N) * (x ^ 4 + 11 * x ^ 3 + 11 * x ^ 2 + x) := by
    funext N; unfold Ptel; ring
  rw [this]
  simpa using ((((h4.mul_const _).add (h3.mul_const _)).add (h2.mul_const _)).add
    (h1.mul_const _)).add (h0.mul_const _)

/-- `∑_{ℓ ≥ 1} ℓ⁴ x^ℓ = x (1 + 11x + 11x² + x³) / (1 - x)⁵`. -/
lemma hasSum_pow_four_mul_geometric {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun ℓ : ℕ => ((ℓ : ℝ) + 1) ^ 4 * x ^ (ℓ + 1))
      (x * (1 + 11 * x + 11 * x ^ 2 + x ^ 3) / (1 - x) ^ 5) := by
  have h1x : (0 : ℝ) < (1 - x) ^ 5 := pow_pos (by linarith) 5
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun ℓ => by positivity) _).mpr ?_
  have hS : ∀ N : ℕ, ∑ ℓ ∈ range N, ((ℓ : ℝ) + 1) ^ 4 * x ^ (ℓ + 1) =
      (x * (1 + 11 * x + 11 * x ^ 2 + x ^ 3) - x ^ (N + 1) * Ptel N x) / (1 - x) ^ 5 := by
    intro N; rw [← telescope, mul_div_cancel_left₀ _ h1x.ne']
  simp_rw [hS]
  have := ((tendsto_const_nhds (x := x * (1 + 11 * x + 11 * x ^ 2 + x ^ 3))).sub
    (tendsto_pow_mul_Ptel hx0 hx1)).div_const ((1 - x) ^ 5)
  rw [sub_zero] at this
  exact this

/-! ### `F(y) = 1 / (e^{2πy} - 1)` and its derivatives -/

/-- `q(y) = e^{2πy}`. -/
noncomputable def qe (y : ℝ) : ℝ := Real.exp (2 * Real.pi * y)

lemma qe_pos (y : ℝ) : 0 < qe y := Real.exp_pos _
lemma qe_gt_one {y : ℝ} (hy : 0 < y) : 1 < qe y := by
  unfold qe; rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by positivity)
lemma hasDerivAt_qe (y : ℝ) : HasDerivAt qe (2 * Real.pi * qe y) y := by
  have h := ((hasDerivAt_id (𝕜 := ℝ) y).const_mul (2 * Real.pi)).exp
  simp only [id, mul_one] at h
  unfold qe
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq h
    (Filter.Eventually.of_forall fun _ => rfl)) ?_
  ring

/-- `F(y) = 1 / (e^{2πy} - 1)` and its first four derivatives. -/
noncomputable def F0 (y : ℝ) : ℝ := 1 / (qe y - 1)
noncomputable def F1 (y : ℝ) : ℝ := -(2 * Real.pi) * qe y / (qe y - 1) ^ 2
noncomputable def F2 (y : ℝ) : ℝ := (2 * Real.pi) ^ 2 * qe y * (qe y + 1) / (qe y - 1) ^ 3
noncomputable def F3 (y : ℝ) : ℝ :=
  -(2 * Real.pi) ^ 3 * qe y * (qe y ^ 2 + 4 * qe y + 1) / (qe y - 1) ^ 4
noncomputable def F4 (y : ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 * qe y * (qe y ^ 3 + 11 * qe y ^ 2 + 11 * qe y + 1) / (qe y - 1) ^ 5

lemma hasDerivAt_F0 {y : ℝ} (hy : 0 < y) : HasDerivAt F0 (F1 y) y := by
  have hq : qe y - 1 ≠ 0 := by have := qe_gt_one hy; linarith
  have := ((hasDerivAt_qe y).sub_const 1).inv hq
  unfold F0 F1
  simp only [one_div]
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq this
    (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
  field_simp

lemma hasDerivAt_F1 {y : ℝ} (hy : 0 < y) : HasDerivAt F1 (F2 y) y := by
  have hq : qe y - 1 ≠ 0 := by have := qe_gt_one hy; linarith
  have hd := ((hasDerivAt_qe y).const_mul (-(2 * Real.pi))).div
    (((hasDerivAt_qe y).sub_const 1).pow 2) (pow_ne_zero 2 hq)
  unfold F1 F2
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq hd
    (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
  field_simp
  ring

lemma hasDerivAt_F2 {y : ℝ} (hy : 0 < y) : HasDerivAt F2 (F3 y) y := by
  have hq : qe y - 1 ≠ 0 := by have := qe_gt_one hy; linarith
  have hd := (((hasDerivAt_qe y).const_mul ((2 * Real.pi) ^ 2)).mul
    ((hasDerivAt_qe y).add_const 1)).div (((hasDerivAt_qe y).sub_const 1).pow 3) (pow_ne_zero 3 hq)
  unfold F2 F3
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq hd
    (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
  field_simp
  ring

lemma hasDerivAt_F3 {y : ℝ} (hy : 0 < y) : HasDerivAt F3 (F4 y) y := by
  have hq : qe y - 1 ≠ 0 := by have := qe_gt_one hy; linarith
  have hd := (((hasDerivAt_qe y).const_mul (-(2 * Real.pi) ^ 3)).mul
    ((((hasDerivAt_qe y).pow 2).add ((hasDerivAt_qe y).const_mul 4)).add_const 1)).div
    (((hasDerivAt_qe y).sub_const 1).pow 4) (pow_ne_zero 4 hq)
  unfold F3 F4
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq hd
    (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
  field_simp
  ring

/-- The series `wS` in closed form: `wS(y) = q (q³ + 11q² + 11q + 1) / (q - 1)⁵`. -/
lemma wS_eq {y : ℝ} (hy : 0 < y) :
    wS y = qe y * (qe y ^ 3 + 11 * qe y ^ 2 + 11 * qe y + 1) / (qe y - 1) ^ 5 := by
  set x : ℝ := Real.exp (-(2 * Real.pi * y)) with hx
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := by rw [hx, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  have hterm : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y)) =
      ((ℓ : ℝ) + 1) ^ 4 * x ^ (ℓ + 1) := by
    intro ℓ
    rw [hx, ← Real.exp_nat_mul]
    congr 2
    push_cast; ring
  unfold wS
  simp_rw [hterm]
  rw [(hasSum_pow_four_mul_geometric hx0 hx1).tsum_eq]
  have hq : qe y = 1 / x := by
    rw [hx, qe, one_div, ← Real.exp_neg, neg_neg]
  rw [hq]
  have hxne : x ≠ 0 := (Real.exp_pos _).ne'
  have h1x : 1 - x ≠ 0 := by linarith
  field_simp
  try ring

/-- `w(y) = y⁵ F₄(y) / 12` for `y > 0`. -/
lemma w_eq_F4 {y : ℝ} (hy : 0 < y) : w y = y ^ 5 * F4 y / 12 := by
  unfold w F4
  rw [wS_eq hy]
  ring

/-! ### `g(y) = y⁵ / (12 (y² + a²))` and its derivatives -/

noncomputable def g0 (a y : ℝ) : ℝ := y ^ 5 / (12 * (y ^ 2 + a ^ 2))
noncomputable def g1 (a y : ℝ) : ℝ := y ^ 4 * (5 * a ^ 2 + 3 * y ^ 2) / (12 * (y ^ 2 + a ^ 2) ^ 2)
noncomputable def g2 (a y : ℝ) : ℝ :=
  y ^ 3 * (10 * a ^ 4 + 9 * a ^ 2 * y ^ 2 + 3 * y ^ 4) / (6 * (y ^ 2 + a ^ 2) ^ 3)
noncomputable def g3 (a y : ℝ) : ℝ :=
  y ^ 2 * (10 * a ^ 6 + 5 * a ^ 4 * y ^ 2 + 4 * a ^ 2 * y ^ 4 + y ^ 6) / (2 * (y ^ 2 + a ^ 2) ^ 4)
noncomputable def g4 (a y : ℝ) : ℝ :=
  2 * a ^ 4 * y * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4) / (y ^ 2 + a ^ 2) ^ 5

lemma hasDerivAt_g0 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (g0 a) (g1 a y) y := by
  have hne : 12 * (y ^ 2 + a ^ 2) ≠ 0 := by positivity
  have hd := (hasDerivAt_pow 5 y).div (((hasDerivAt_pow 2 y).add_const (a ^ 2)).const_mul 12) hne
  unfold g0 g1
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq hd
    (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
  field_simp
  ring

lemma hasDerivAt_g1 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (g1 a) (g2 a y) y := by
  have hne : 12 * (y ^ 2 + a ^ 2) ^ 2 ≠ 0 := by positivity
  have hd := ((hasDerivAt_pow 4 y).mul (((hasDerivAt_pow 2 y).const_mul 3).const_add (5 * a ^ 2))).div
    ((((hasDerivAt_pow 2 y).add_const (a ^ 2)).pow 2).const_mul 12) hne
  unfold g1 g2
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq hd
    (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
  field_simp
  ring

lemma hasDerivAt_g2 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (g2 a) (g3 a y) y := by
  have hne : 6 * (y ^ 2 + a ^ 2) ^ 3 ≠ 0 := by positivity
  have hd := ((hasDerivAt_pow 3 y).mul
      ((((hasDerivAt_pow 2 y).const_mul (9 * a ^ 2)).const_add (10 * a ^ 4)).add
        ((hasDerivAt_pow 4 y).const_mul 3))).div
    ((((hasDerivAt_pow 2 y).add_const (a ^ 2)).pow 3).const_mul 6) hne
  unfold g2 g3
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq hd
    (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
  field_simp
  ring

lemma hasDerivAt_g3 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (g3 a) (g4 a y) y := by
  have hne : 2 * (y ^ 2 + a ^ 2) ^ 4 ≠ 0 := by positivity
  have hd := ((hasDerivAt_pow 2 y).mul
      (((((hasDerivAt_pow 2 y).const_mul (5 * a ^ 4)).const_add (10 * a ^ 6)).add
        ((hasDerivAt_pow 4 y).const_mul (4 * a ^ 2))).add (hasDerivAt_pow 6 y))).div
    ((((hasDerivAt_pow 2 y).add_const (a ^ 2)).pow 4).const_mul 2) hne
  unfold g3 g4
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq hd
    (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
  field_simp
  ring

end Apery

namespace Apery

open MeasureTheory Set

/-! ### Bounds, integrability and the first integral `∫₀^∞ g₄ = 1/2` -/

lemma abs_g4_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 ≤ y) :
    |g4 a y| ≤ 10 * a ^ 3 / (y ^ 2 + a ^ 2) ^ 2 := by
  unfold g4
  have hden : 0 < y ^ 2 + a ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (y ^ 2 + a ^ 2) ^ 5),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |2 * a ^ 4 * y * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)| ≤
      2 * a ^ 4 * y * (10 * (y ^ 2 + a ^ 2) ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a ^ 4 * y)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a ^ 2 - y ^ 2), sq_nonneg y, sq_nonneg a,
      mul_nonneg (sq_nonneg a) (sq_nonneg y)]
  have h2 : y ≤ (y ^ 2 + a ^ 2) / (2 * a) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (y - a)]
  calc |2 * a ^ 4 * y * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)| * (y ^ 2 + a ^ 2) ^ 2
      ≤ 2 * a ^ 4 * y * (10 * (y ^ 2 + a ^ 2) ^ 2) * (y ^ 2 + a ^ 2) ^ 2 := by gcongr
    _ ≤ 2 * a ^ 4 * ((y ^ 2 + a ^ 2) / (2 * a)) * (10 * (y ^ 2 + a ^ 2) ^ 2) *
          (y ^ 2 + a ^ 2) ^ 2 := by gcongr
    _ = 10 * a ^ 3 * (y ^ 2 + a ^ 2) ^ 5 := by
          field_simp

lemma inv_sq_add_le {a : ℝ} (ha : 0 < a) (y : ℝ) :
    1 / (y ^ 2 + a ^ 2) ≤ (1 + 1 / a ^ 2) * (1 / (1 + y ^ 2)) := by
  rw [div_le_iff₀ (by positivity)]
  have : (1 + 1 / a ^ 2) * (1 / (1 + y ^ 2)) * (y ^ 2 + a ^ 2) =
      (y ^ 2 + a ^ 2 + y ^ 2 / a ^ 2 + 1) / (1 + y ^ 2) := by field_simp; ring
  rw [this, le_div_iff₀ (by positivity)]
  have : 0 ≤ y ^ 2 / a ^ 2 := by positivity
  nlinarith

/-- `g₄ · h` is integrable on `(0, ∞)` whenever `h` is measurable and bounded by `1/(y²+a²)`
-type control: we only need the three cases below. -/
lemma integrableOn_g4 {a : ℝ} (ha : 0 < a) : IntegrableOn (g4 a) (Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ => (10 * a ^ 3 / a ^ 2 * (1 + 1 / a ^ 2)) * (1 + y ^ 2)⁻¹)
      (Ioi 0) := (integrable_inv_one_add_sq.const_mul _).integrableOn
  have hcont : Continuous (g4 a) := by
    unfold g4
    exact (by fun_prop : Continuous fun y : ℝ => 2 * a ^ 4 * y * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)).div
      (by fun_prop) (fun y => by positivity)
  refine hg.mono' hcont.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hy : 0 < y := hy
  rw [Real.norm_eq_abs]
  calc |g4 a y| ≤ 10 * a ^ 3 / (y ^ 2 + a ^ 2) ^ 2 := abs_g4_le ha hy.le
    _ ≤ 10 * a ^ 3 / (a ^ 2 * (y ^ 2 + a ^ 2)) := by
        gcongr
        nlinarith [sq_nonneg y]
    _ = 10 * a ^ 3 / a ^ 2 * (1 / (y ^ 2 + a ^ 2)) := by field_simp
    _ ≤ 10 * a ^ 3 / a ^ 2 * ((1 + 1 / a ^ 2) * (1 / (1 + y ^ 2))) := by
        gcongr; exact inv_sq_add_le ha y
    _ = _ := by ring

lemma tendsto_g3_atTop {a : ℝ} (ha : 0 < a) : Tendsto (g3 a) atTop (𝓝 (1 / 2)) := by
  have hφ : Tendsto (fun u : ℝ => (10 * a ^ 6 * u ^ 6 + 5 * a ^ 4 * u ^ 4 + 4 * a ^ 2 * u ^ 2 + 1) /
      (2 * (1 + a ^ 2 * u ^ 2) ^ 4)) (𝓝 0) (𝓝 (1 / 2)) := by
    have : ContinuousAt (fun u : ℝ => (10 * a ^ 6 * u ^ 6 + 5 * a ^ 4 * u ^ 4 + 4 * a ^ 2 * u ^ 2 + 1) /
        (2 * (1 + a ^ 2 * u ^ 2) ^ 4)) 0 := by
      refine ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    have h0 := this.tendsto
    simpa using h0
  have := hφ.comp tendsto_inv_atTop_zero
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  simp only [Function.comp, g3]
  field_simp

/-- `∫₀^∞ g₄(y) dy = 1/2`. -/
lemma integral_g4 {a : ℝ} (ha : 0 < a) : ∫ y in Ioi 0, g4 a y = 1 / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (f := g3 a) (f' := g4 a)
    (fun y _ => hasDerivAt_g3 ha y) (integrableOn_g4 ha) (tendsto_g3_atTop ha)
  rw [h]; simp [g3]

end Apery

namespace Apery

open Complex in
/-- The Mittag-Leffler expansion of `F(y) = 1/(e^{2πy} - 1)`:
`F(y) = -1/2 + 1/(2πy) + (1/π) ∑_{n ≥ 1} y/(y² + n²)`, from Mathlib's `cot_series_rep`. -/
lemma F0_series {y : ℝ} (hy : 0 < y) :
    F0 y = -1 / 2 + 1 / (2 * Real.pi * y) +
      (1 / Real.pi) * ∑' n : ℕ, y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) := by
  have hx : (I * (y : ℂ)) ∈ integerComplement := by
    rw [integerComplement_eq]
    rintro ⟨n, hn⟩
    have h := congrArg Complex.im hn
    simp at h
    linarith
  have h := cot_series_rep hx
  -- the left-hand side
  have hs : Real.sinh (Real.pi * y) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have hL : (Real.pi : ℂ) * cot (Real.pi * (I * y)) =
      -I * ((Real.pi * (Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y)) : ℝ) : ℂ) := by
    rw [cot_eq_cos_div_sin, show (Real.pi : ℂ) * (I * y) = ((Real.pi * y : ℝ) : ℂ) * I by
      push_cast; ring, cos_mul_I, sin_mul_I, ← ofReal_cosh, ← ofReal_sinh]
    have hs' : (Real.sinh (Real.pi * y) : ℂ) ≠ 0 := by exact_mod_cast hs
    push_cast
    field_simp
    ring_nf
    simp [I_sq]
  -- the right-hand side
  have hR : (1 / (I * (y : ℂ)) + ∑' n : ℕ+, (1 / (I * y - n) + 1 / (I * y + n))) =
      -I * ((1 / y + ∑' n : ℕ, 2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    have hterm : ∀ n : ℕ+, (1 / (I * (y : ℂ) - n) + 1 / (I * y + n)) =
        -I * ((2 * y / (y ^ 2 + ((n : ℕ) : ℝ) ^ 2) : ℝ) : ℂ) := by
      intro n
      have h1 : I * (y : ℂ) - n ≠ 0 := by
        intro h; have := congrArg Complex.im h; simp at this; linarith
      have h2 : I * (y : ℂ) + n ≠ 0 := by
        intro h; have := congrArg Complex.im h; simp at this; linarith
      have h3 : ((y : ℂ) ^ 2 + ((n : ℕ) : ℂ) ^ 2) ≠ 0 := by
        have : (0 : ℝ) < y ^ 2 + ((n : ℕ) : ℝ) ^ 2 := by positivity
        exact_mod_cast this.ne'
      push_cast
      rw [div_add_div _ _ h1 h2, div_eq_iff (mul_ne_zero h1 h2)]
      have hIy : (I * (y : ℂ) - n) * (I * y + n) = -((y : ℂ) ^ 2 + ((n : ℕ) : ℂ) ^ 2) := by
        ring_nf; rw [I_sq]; ring
      rw [hIy]
      field_simp
      ring
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_pnat_eq_tsum_succ (f := fun m : ℕ => ((2 * y / (y ^ 2 + (m : ℝ) ^ 2) : ℝ) : ℂ))]
    push_cast
    rw [one_div, mul_inv, Complex.inv_I]
    ring
  rw [hL, hR] at h
  have hI : (-I : ℂ) ≠ 0 := by simp
  have h' := mul_left_cancel₀ hI h
  have hreal : Real.pi * (Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y)) =
      1 / y + ∑' n : ℕ, 2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) := by exact_mod_cast h'
  -- `cosh/sinh = 1 + 2 F₀`
  have hcoth : Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y) = 1 + 2 * F0 y := by
    rw [Real.cosh_eq, Real.sinh_eq, F0, qe]
    have hq : Real.exp (2 * Real.pi * y) = Real.exp (Real.pi * y) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hq1 : Real.exp (2 * Real.pi * y) - 1 ≠ 0 := by
      have := qe_gt_one hy; unfold qe at this; linarith
    have he : Real.exp (-(Real.pi * y)) = 1 / Real.exp (Real.pi * y) := by
      rw [Real.exp_neg, one_div]
    rw [he]
    have hpos : Real.exp (Real.pi * y) ≠ 0 := (Real.exp_pos _).ne'
    rw [hq] at hq1 ⊢
    field_simp
    ring
  rw [hcoth] at hreal
  have hsum : ∑' n : ℕ, 2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) =
      2 * ∑' n : ℕ, y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) := by
    rw [← tsum_mul_left]; congr 1; funext n; ring
  rw [hsum] at hreal
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  set S := ∑' n : ℕ, y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) with hS
  have h2 : F0 y = (1 / y + 2 * S) / (2 * Real.pi) - 1 / 2 := by
    field_simp at hreal ⊢
    linear_combination hreal
  rw [h2]
  field_simp
  ring

end Apery
end Port3

section Port4
/-!
# The rational integrals in Hermite's formula — port of `Apery/HermiteIntegrals.lean`

* `∫₀^∞ g₄(y)/y dy = π/a`;
* `∫₀^∞ g₄(y) y/(y² + n²) dy = π a⁴/(a + n)⁵` for `n > 0`.
The antiderivatives (a rational function plus arctan terms) are verified by differentiation.

Source: mo271/Zeta5 @ 7fe7367, `Apery/HermiteIntegrals.lean`.
-/

open Filter Topology Set MeasureTheory

namespace Apery

/-- `g₄(y) / y` as a rational function (continuous at `0`). -/
noncomputable def h4 (a y : ℝ) : ℝ := 2 * a ^ 4 * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4) / (y ^ 2 + a ^ 2) ^ 5

lemma g4_div_eq_h4 (a : ℝ) {y : ℝ} (hy : y ≠ 0) : g4 a y / y = h4 a y := by
  unfold g4 h4; field_simp

lemma abs_h4_le {a : ℝ} (ha : 0 < a) (y : ℝ) : |h4 a y| ≤ 20 / (y ^ 2 + a ^ 2) := by
  unfold h4
  have hden : 0 < y ^ 2 + a ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (y ^ 2 + a ^ 2) ^ 5),
    div_le_div_iff₀ (by positivity) hden]
  have h1 : |2 * a ^ 4 * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)| ≤ 2 * a ^ 4 * (10 * (y ^ 2 + a ^ 2) ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a ^ 4)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a ^ 2 - y ^ 2), sq_nonneg y, sq_nonneg a,
      mul_nonneg (sq_nonneg a) (sq_nonneg y)]
  have h2 : a ^ 4 ≤ (y ^ 2 + a ^ 2) ^ 2 := by nlinarith [sq_nonneg y, sq_nonneg a, mul_nonneg (sq_nonneg y) (sq_nonneg a)]
  calc |2 * a ^ 4 * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)| * (y ^ 2 + a ^ 2)
      ≤ 2 * a ^ 4 * (10 * (y ^ 2 + a ^ 2) ^ 2) * (y ^ 2 + a ^ 2) := by gcongr
    _ ≤ 2 * (y ^ 2 + a ^ 2) ^ 2 * (10 * (y ^ 2 + a ^ 2) ^ 2) * (y ^ 2 + a ^ 2) := by gcongr
    _ = 20 * (y ^ 2 + a ^ 2) ^ 5 := by ring

lemma integrableOn_of_le_inv_sq {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    {C : ℝ} (hC : ∀ y, 0 < y → |f y| ≤ C / (y ^ 2 + a ^ 2)) : IntegrableOn f (Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ => (C * (1 + 1 / a ^ 2)) * (1 + y ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul _).integrableOn
  refine hg.mono' hf ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hy : 0 < y := hy
  rw [Real.norm_eq_abs]
  have hC0 : 0 ≤ C := by
    by_contra hneg
    push Not at hneg
    have h1 := hC y hy
    have h2 : C / (y ^ 2 + a ^ 2) < 0 := div_neg_of_neg_of_pos hneg (by positivity)
    linarith [abs_nonneg (f y)]
  calc |f y| ≤ C / (y ^ 2 + a ^ 2) := hC y hy
    _ = C * (1 / (y ^ 2 + a ^ 2)) := by ring
    _ ≤ C * ((1 + 1 / a ^ 2) * (1 / (1 + y ^ 2))) := by gcongr; exact inv_sq_add_le ha y
    _ = _ := by ring

/-- The limit `arctan (y / c) → π/2` as `y → ∞`, for `c > 0`. -/
lemma tendsto_arctan_div_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => Real.arctan (y / c)) atTop (𝓝 (Real.pi / 2)) :=
  (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp (tendsto_id.atTop_div_const hc)

/-! ### `∫₀^∞ g₄(y)/y dy = π / a` -/

/-- Antiderivative of `h₄`. -/
noncomputable def A1 (a y : ℝ) : ℝ :=
  2 / a * Real.arctan (y / a) +
    2 * y * (12 * a ^ 6 + 14 * a ^ 4 * y ^ 2 + 11 * a ^ 2 * y ^ 4 + 3 * y ^ 6) / (3 * (a ^ 2 + y ^ 2) ^ 4)

lemma hasDerivAt_A1 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (A1 a) (h4 a y) y := by
  have h1 := ((hasDerivAt_id y).div_const a).arctan.const_mul (2 / a)
  have hne : 3 * (a ^ 2 + y ^ 2) ^ 4 ≠ 0 := by positivity
  have hnum := ((hasDerivAt_id y).const_mul 2).mul
    (((((hasDerivAt_pow 2 y).const_mul (14 * a ^ 4)).const_add (12 * a ^ 6)).add
      ((hasDerivAt_pow 4 y).const_mul (11 * a ^ 2))).add ((hasDerivAt_pow 6 y).const_mul 3))
  have h2 := hnum.div ((((hasDerivAt_pow 2 y).const_add (a ^ 2)).pow 4).const_mul 3) hne
  have h := h1.add h2
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp only [A1, id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
  · simp only [h4, id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    field_simp
    ring

lemma tendsto_A1_atTop {a : ℝ} (ha : 0 < a) : Tendsto (A1 a) atTop (𝓝 (Real.pi / a)) := by
  have h1 : Tendsto (fun y : ℝ => 2 / a * Real.arctan (y / a)) atTop (𝓝 (2 / a * (Real.pi / 2))) :=
    (tendsto_arctan_div_atTop ha).const_mul _
  have hφ : Tendsto (fun u : ℝ => 2 * u * (12 * a ^ 6 * u ^ 6 + 14 * a ^ 4 * u ^ 4 + 11 * a ^ 2 * u ^ 2 + 3) /
      (3 * (a ^ 2 * u ^ 2 + 1) ^ 4)) (𝓝 0) (𝓝 0) := by
    have : ContinuousAt (fun u : ℝ => 2 * u * (12 * a ^ 6 * u ^ 6 + 14 * a ^ 4 * u ^ 4 + 11 * a ^ 2 * u ^ 2 + 3) /
        (3 * (a ^ 2 * u ^ 2 + 1) ^ 4)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    simpa using this.tendsto
  have h2 : Tendsto (fun y : ℝ => 2 * y * (12 * a ^ 6 + 14 * a ^ 4 * y ^ 2 + 11 * a ^ 2 * y ^ 4 + 3 * y ^ 6) /
      (3 * (a ^ 2 + y ^ 2) ^ 4)) atTop (𝓝 0) := by
    refine (hφ.comp tendsto_inv_atTop_zero).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [Function.comp]
    field_simp
  have := h1.add h2
  unfold A1
  convert this using 2
  field_simp
  ring

lemma continuous_g4 (a : ℝ) (ha : 0 < a) : Continuous (g4 a) := by
  unfold g4
  exact (by fun_prop : Continuous fun y : ℝ => 2 * a ^ 4 * y * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)).div
    (by fun_prop) (fun y => by positivity)

lemma integrableOn_h4 {a : ℝ} (ha : 0 < a) : IntegrableOn (h4 a) (Ioi 0) := by
  have hcont : Continuous (h4 a) := by
    unfold h4
    exact (by fun_prop : Continuous fun y : ℝ => 2 * a ^ 4 * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)).div
      (by fun_prop) (fun y => by positivity)
  exact integrableOn_of_le_inv_sq ha hcont.aestronglyMeasurable (fun y _ => abs_h4_le ha y)

/-- `∫₀^∞ g₄(y)/y dy = π/a`. -/
lemma integral_h4 {a : ℝ} (ha : 0 < a) : ∫ y in Ioi 0, h4 a y = Real.pi / a := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (f := A1 a) (f' := h4 a)
    (fun y _ => hasDerivAt_A1 ha y) (integrableOn_h4 ha) (tendsto_A1_atTop ha)
  rw [h]; simp [A1]


/-! ### `∫₀^∞ g₄(y) y/(y² + n²) dy = π a⁴/(a + n)⁵` -/

/-- The integrand `g₄(y) · y/(y² + n²)`. -/
noncomputable def k4 (a n y : ℝ) : ℝ := g4 a y * (y / (y ^ 2 + n ^ 2))

lemma abs_k4_le {a n : ℝ} (ha : 0 < a) (hn : 0 < n) {y : ℝ} (hy : 0 < y) :
    |k4 a n y| ≤ 5 * a / n / (y ^ 2 + a ^ 2) := by
  unfold k4
  have h1 := abs_g4_le ha hy.le
  have h2 : y / (y ^ 2 + n ^ 2) ≤ 1 / (2 * n) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_nonneg (y - n)]
  have h3 : 0 ≤ y / (y ^ 2 + n ^ 2) := by positivity
  rw [abs_mul, abs_of_nonneg h3]
  calc |g4 a y| * (y / (y ^ 2 + n ^ 2)) ≤ 10 * a ^ 3 / (y ^ 2 + a ^ 2) ^ 2 * (1 / (2 * n)) := by gcongr
    _ ≤ 10 * a ^ 3 / (a ^ 2 * (y ^ 2 + a ^ 2)) * (1 / (2 * n)) := by
        gcongr; nlinarith [sq_nonneg y]
    _ = 5 * a / n / (y ^ 2 + a ^ 2) := by field_simp; ring

lemma integrableOn_k4 {a n : ℝ} (ha : 0 < a) (hn : 0 < n) : IntegrableOn (k4 a n) (Ioi 0) := by
  have hcont : Continuous (k4 a n) := by
    unfold k4
    exact (continuous_g4 a ha).mul ((by fun_prop : Continuous fun y : ℝ => y).div (by fun_prop)
      (fun y => by positivity))
  exact integrableOn_of_le_inv_sq ha hcont.aestronglyMeasurable (fun y hy => abs_k4_le ha hn hy)

/-- Antiderivative of `k4 a n` for `n ≠ a`; `D = a² - n²`. -/
noncomputable def A2 (a n y : ℝ) : ℝ :=
  (2 * a ^ 9 + 20 * a ^ 7 * n ^ 2 + 10 * a ^ 5 * n ^ 4) / (a ^ 2 - n ^ 2) ^ 5 * Real.arctan (y / a) -
    (10 * a ^ 8 * n + 20 * a ^ 6 * n ^ 3 + 2 * a ^ 4 * n ^ 5) / (a ^ 2 - n ^ 2) ^ 5 * Real.arctan (y / n) +
    (y ^ 7 * (3 * (2 * a ^ 8 + 12 * a ^ 6 * n ^ 2 + 2 * a ^ 4 * n ^ 4)) +
      y ^ 5 * (22 * a ^ 10 + 122 * a ^ 8 * n ^ 2 + 2 * a ^ 6 * n ^ 4 - 2 * a ^ 4 * n ^ 6) +
      y ^ 3 * (28 * a ^ 12 + 146 * a ^ 10 * n ^ 2 - 40 * a ^ 8 * n ^ 4 + 10 * a ^ 6 * n ^ 6) +
      y * (3 * (8 * a ^ 14 + 8 * a ^ 12 * n ^ 2))) / (3 * (a ^ 2 - n ^ 2) ^ 4 * (a ^ 2 + y ^ 2) ^ 4)

lemma hasDerivAt_A2 {a n : ℝ} (ha : 0 < a) (hn : 0 < n) (hne : n ≠ a) (y : ℝ) :
    HasDerivAt (A2 a n) (k4 a n y) y := by
  have hD : a ^ 2 - n ^ 2 ≠ 0 := by
    intro h
    have : (a - n) * (a + n) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hne (by linarith)
    · linarith
  have h1 := ((hasDerivAt_id y).div_const a).arctan.const_mul
    ((2 * a ^ 9 + 20 * a ^ 7 * n ^ 2 + 10 * a ^ 5 * n ^ 4) / (a ^ 2 - n ^ 2) ^ 5)
  have h2 := ((hasDerivAt_id y).div_const n).arctan.const_mul
    ((10 * a ^ 8 * n + 20 * a ^ 6 * n ^ 3 + 2 * a ^ 4 * n ^ 5) / (a ^ 2 - n ^ 2) ^ 5)
  have hne3 : 3 * (a ^ 2 - n ^ 2) ^ 4 * (a ^ 2 + y ^ 2) ^ 4 ≠ 0 := by positivity
  have hnum := ((((hasDerivAt_pow 7 y).mul_const (3 * (2 * a ^ 8 + 12 * a ^ 6 * n ^ 2 + 2 * a ^ 4 * n ^ 4))).add
      ((hasDerivAt_pow 5 y).mul_const (22 * a ^ 10 + 122 * a ^ 8 * n ^ 2 + 2 * a ^ 6 * n ^ 4 - 2 * a ^ 4 * n ^ 6))).add
      ((hasDerivAt_pow 3 y).mul_const (28 * a ^ 12 + 146 * a ^ 10 * n ^ 2 - 40 * a ^ 8 * n ^ 4 + 10 * a ^ 6 * n ^ 6))).add
      ((hasDerivAt_id y).mul_const (3 * (8 * a ^ 14 + 8 * a ^ 12 * n ^ 2)))
  have h3 := hnum.div ((((hasDerivAt_pow 2 y).const_add (a ^ 2)).pow 4).const_mul
    (3 * (a ^ 2 - n ^ 2) ^ 4)) hne3
  have h := (h1.sub h2).add h3
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp only [A2, id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
  · simp only [k4, g4, id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    have hyn : y ^ 2 + n ^ 2 ≠ 0 := by positivity
    have hya : a ^ 2 + y ^ 2 ≠ 0 := by positivity
    field_simp
    ring

lemma tendsto_A2_atTop {a n : ℝ} (ha : 0 < a) (hn : 0 < n) (hne : n ≠ a) :
    Tendsto (A2 a n) atTop (𝓝 (Real.pi * a ^ 4 / (a + n) ^ 5)) := by
  have hD : a ^ 2 - n ^ 2 ≠ 0 := by
    intro h
    have : (a - n) * (a + n) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hne (by linarith)
    · linarith
  have h1 := (tendsto_arctan_div_atTop ha).const_mul
    ((2 * a ^ 9 + 20 * a ^ 7 * n ^ 2 + 10 * a ^ 5 * n ^ 4) / (a ^ 2 - n ^ 2) ^ 5)
  have h2 := (tendsto_arctan_div_atTop hn).const_mul
    ((10 * a ^ 8 * n + 20 * a ^ 6 * n ^ 3 + 2 * a ^ 4 * n ^ 5) / (a ^ 2 - n ^ 2) ^ 5)
  have hφ : Tendsto (fun u : ℝ => u * (3 * (2 * a ^ 8 + 12 * a ^ 6 * n ^ 2 + 2 * a ^ 4 * n ^ 4) +
      u ^ 2 * (22 * a ^ 10 + 122 * a ^ 8 * n ^ 2 + 2 * a ^ 6 * n ^ 4 - 2 * a ^ 4 * n ^ 6) +
      u ^ 4 * (28 * a ^ 12 + 146 * a ^ 10 * n ^ 2 - 40 * a ^ 8 * n ^ 4 + 10 * a ^ 6 * n ^ 6) +
      u ^ 6 * (3 * (8 * a ^ 14 + 8 * a ^ 12 * n ^ 2))) / (3 * (a ^ 2 - n ^ 2) ^ 4 * (a ^ 2 * u ^ 2 + 1) ^ 4))
      (𝓝 0) (𝓝 0) := by
    have : ContinuousAt (fun u : ℝ => u * (3 * (2 * a ^ 8 + 12 * a ^ 6 * n ^ 2 + 2 * a ^ 4 * n ^ 4) +
        u ^ 2 * (22 * a ^ 10 + 122 * a ^ 8 * n ^ 2 + 2 * a ^ 6 * n ^ 4 - 2 * a ^ 4 * n ^ 6) +
        u ^ 4 * (28 * a ^ 12 + 146 * a ^ 10 * n ^ 2 - 40 * a ^ 8 * n ^ 4 + 10 * a ^ 6 * n ^ 6) +
        u ^ 6 * (3 * (8 * a ^ 14 + 8 * a ^ 12 * n ^ 2))) / (3 * (a ^ 2 - n ^ 2) ^ 4 * (a ^ 2 * u ^ 2 + 1) ^ 4)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by simp; positivity)
    simpa using this.tendsto
  have h3 : Tendsto (fun y : ℝ => (y ^ 7 * (3 * (2 * a ^ 8 + 12 * a ^ 6 * n ^ 2 + 2 * a ^ 4 * n ^ 4)) +
      y ^ 5 * (22 * a ^ 10 + 122 * a ^ 8 * n ^ 2 + 2 * a ^ 6 * n ^ 4 - 2 * a ^ 4 * n ^ 6) +
      y ^ 3 * (28 * a ^ 12 + 146 * a ^ 10 * n ^ 2 - 40 * a ^ 8 * n ^ 4 + 10 * a ^ 6 * n ^ 6) +
      y * (3 * (8 * a ^ 14 + 8 * a ^ 12 * n ^ 2))) / (3 * (a ^ 2 - n ^ 2) ^ 4 * (a ^ 2 + y ^ 2) ^ 4))
      atTop (𝓝 0) := by
    refine (hφ.comp tendsto_inv_atTop_zero).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [Function.comp]
    field_simp
  have := (h1.sub h2).add h3
  unfold A2
  convert this using 2
  have hsum : a + n ≠ 0 := by positivity
  have hdiff : a - n ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hDf : a ^ 2 - n ^ 2 = (a - n) * (a + n) := by ring
  rw [hDf]
  field_simp
  ring

/-- `∫₀^∞ g₄(y) y/(y² + n²) dy = π a⁴/(a + n)⁵` for `n ≠ a`. -/
lemma integral_k4_ne {a n : ℝ} (ha : 0 < a) (hn : 0 < n) (hne : n ≠ a) :
    ∫ y in Ioi 0, k4 a n y = Real.pi * a ^ 4 / (a + n) ^ 5 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (f := A2 a n) (f' := k4 a n)
    (fun y _ => hasDerivAt_A2 ha hn hne y) (integrableOn_k4 ha hn) (tendsto_A2_atTop ha hn hne)
  rw [h]; simp [A2]

/-- Antiderivative of `k4 a a`. -/
noncomputable def A2e (a y : ℝ) : ℝ :=
  Real.arctan (y / a) / (16 * a) +
    y * (-15 * a ^ 8 + 730 * a ^ 6 * y ^ 2 + 32 * a ^ 4 * y ^ 4 + 70 * a ^ 2 * y ^ 6 + 15 * y ^ 8) /
      (240 * (a ^ 2 + y ^ 2) ^ 5)

lemma hasDerivAt_A2e {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (A2e a) (k4 a a y) y := by
  have h1 := ((hasDerivAt_id y).div_const a).arctan.div_const (16 * a)
  have hne : 240 * (a ^ 2 + y ^ 2) ^ 5 ≠ 0 := by positivity
  have hnum := (hasDerivAt_id y).mul
    (((((((hasDerivAt_pow 2 y).const_mul (730 * a ^ 6)).const_add (-15 * a ^ 8)).add
      ((hasDerivAt_pow 4 y).const_mul (32 * a ^ 4))).add ((hasDerivAt_pow 6 y).const_mul (70 * a ^ 2))).add
      ((hasDerivAt_pow 8 y).const_mul 15)))
  have h2 := hnum.div ((((hasDerivAt_pow 2 y).const_add (a ^ 2)).pow 5).const_mul 240) hne
  have h := h1.add h2
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp only [A2e, id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
  · simp only [k4, g4, id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    have hya : a ^ 2 + y ^ 2 ≠ 0 := by positivity
    have hya' : y ^ 2 + a ^ 2 ≠ 0 := by positivity
    field_simp
    ring

lemma tendsto_A2e_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (A2e a) atTop (𝓝 (Real.pi * a ^ 4 / (a + a) ^ 5)) := by
  have h1 := (tendsto_arctan_div_atTop ha).div_const (16 * a)
  have hφ : Tendsto (fun u : ℝ => u * (-15 * a ^ 8 * u ^ 8 + 730 * a ^ 6 * u ^ 6 + 32 * a ^ 4 * u ^ 4 +
      70 * a ^ 2 * u ^ 2 + 15) / (240 * (a ^ 2 * u ^ 2 + 1) ^ 5)) (𝓝 0) (𝓝 0) := by
    have : ContinuousAt (fun u : ℝ => u * (-15 * a ^ 8 * u ^ 8 + 730 * a ^ 6 * u ^ 6 + 32 * a ^ 4 * u ^ 4 +
        70 * a ^ 2 * u ^ 2 + 15) / (240 * (a ^ 2 * u ^ 2 + 1) ^ 5)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    simpa using this.tendsto
  have h2 : Tendsto (fun y : ℝ => y * (-15 * a ^ 8 + 730 * a ^ 6 * y ^ 2 + 32 * a ^ 4 * y ^ 4 +
      70 * a ^ 2 * y ^ 6 + 15 * y ^ 8) / (240 * (a ^ 2 + y ^ 2) ^ 5)) atTop (𝓝 0) := by
    refine (hφ.comp tendsto_inv_atTop_zero).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [Function.comp]
    field_simp
  have := h1.add h2
  unfold A2e
  convert this using 2
  field_simp
  ring

/-- `∫₀^∞ g₄(y) y/(y² + a²) dy = π a⁴/(2a)⁵`. -/
lemma integral_k4_eq {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi 0, k4 a a y = Real.pi * a ^ 4 / (a + a) ^ 5 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (f := A2e a) (f' := k4 a a)
    (fun y _ => hasDerivAt_A2e ha y) (integrableOn_k4 ha ha) (tendsto_A2e_atTop ha)
  rw [h]; simp [A2e]

/-- `∫₀^∞ g₄(y) y/(y² + n²) dy = π a⁴/(a + n)⁵` for all `n > 0`. -/
lemma integral_k4 {a n : ℝ} (ha : 0 < a) (hn : 0 < n) :
    ∫ y in Ioi 0, k4 a n y = Real.pi * a ^ 4 / (a + n) ^ 5 := by
  rcases eq_or_ne n a with rfl | hne
  · exact integral_k4_eq ha
  · exact integral_k4_ne ha hn hne

end Apery
end Port4

section Port5
/-!
# Four integrations by parts: `∫₀^∞ g F₄ = ∫₀^∞ g₄ F₀` — port of `Apery/HermiteIBP.lean`

Uniform bounds `|F_m(y)| ≤ c_m (1+2πy)^{m+1} / (2π y^{m+1} e^{2πy})` and `|g_j(y)| ≤ c_j y^{5-j}/a²`
give integrability of the products and vanishing boundary terms at `0⁺` and `∞`.

Source: mo271/Zeta5 @ 7fe7367, `Apery/HermiteIBP.lean`.
-/

open Filter Topology Set MeasureTheory

namespace Apery

/-! ### Bounds for `F_m` -/

lemma qe_sub_one_ge {y : ℝ} : 2 * Real.pi * y ≤ qe y - 1 := by
  unfold qe; linarith [Real.add_one_le_exp (2 * Real.pi * y)]

lemma one_div_qe_sub_one_le {y : ℝ} (hy : 0 < y) :
    1 / (qe y - 1) ≤ (1 + 2 * Real.pi * y) / (2 * Real.pi * y * qe y) := by
  have hq := qe_gt_one hy
  have h := qe_sub_one_ge (y := y)
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith [qe_pos y]

/-- Generic estimate `N / (q-1)^(m+1) ≤ c (1+2πy)^(m+1) / (2π y^(m+1) q)` when
`N ≤ (2π)^m c q^m`. -/
lemma F_bound_aux {y : ℝ} (hy : 0 < y) (m : ℕ) {N c : ℝ} (hN : 0 ≤ N)
    (hNc : N ≤ (2 * Real.pi) ^ m * c * qe y ^ m) :
    N / (qe y - 1) ^ (m + 1) ≤ c * (1 + 2 * Real.pi * y) ^ (m + 1) / (2 * Real.pi * y ^ (m + 1) * qe y) := by
  have hq := qe_gt_one hy
  have hq0 := qe_pos y
  have h1 : 1 / (qe y - 1) ^ (m + 1) ≤ ((1 + 2 * Real.pi * y) / (2 * Real.pi * y * qe y)) ^ (m + 1) := by
    rw [one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ (by positivity) (one_div_qe_sub_one_le hy) _
  calc N / (qe y - 1) ^ (m + 1) = N * (1 / (qe y - 1) ^ (m + 1)) := by ring
    _ ≤ ((2 * Real.pi) ^ m * c * qe y ^ m) * ((1 + 2 * Real.pi * y) / (2 * Real.pi * y * qe y)) ^ (m + 1) :=
        mul_le_mul hNc h1 (by positivity) (by
          have : 0 ≤ N := hN
          exact le_trans this hNc)
    _ = c * (1 + 2 * Real.pi * y) ^ (m + 1) / (2 * Real.pi * y ^ (m + 1) * qe y) := by
        have h2pi : (2 * Real.pi) ≠ 0 := by positivity
        have hqne : qe y ≠ 0 := hq0.ne'
        rw [div_pow, mul_pow (2 * Real.pi * y) (qe y), mul_pow (2 * Real.pi) y, pow_succ (2 * Real.pi),
          pow_succ (qe y), pow_succ y]
        field_simp
        try ring

lemma abs_F0_le {y : ℝ} (hy : 0 < y) :
    |F0 y| ≤ 1 * (1 + 2 * Real.pi * y) ^ (0 + 1) / (2 * Real.pi * y ^ (0 + 1) * qe y) := by
  have hq := qe_gt_one hy
  rw [F0, abs_of_pos (by positivity)]
  have := F_bound_aux hy 0 (N := 1) (c := 1) (by norm_num) (by simp)
  simpa using this

lemma abs_F1_le {y : ℝ} (hy : 0 < y) :
    |F1 y| ≤ 1 * (1 + 2 * Real.pi * y) ^ (1 + 1) / (2 * Real.pi * y ^ (1 + 1) * qe y) := by
  have hq := qe_gt_one hy
  have hq0 := qe_pos y
  have : F1 y = -((2 * Real.pi) * qe y / (qe y - 1) ^ 2) := by unfold F1; ring
  rw [this, abs_neg, abs_of_pos (by positivity)]
  exact F_bound_aux hy 1 (by positivity) (by ring_nf; rfl)

lemma abs_F2_le {y : ℝ} (hy : 0 < y) :
    |F2 y| ≤ 2 * (1 + 2 * Real.pi * y) ^ (2 + 1) / (2 * Real.pi * y ^ (2 + 1) * qe y) := by
  have hq := qe_gt_one hy
  have hq0 := qe_pos y
  rw [F2, abs_of_pos (by positivity)]
  refine F_bound_aux hy 2 (by positivity) ?_
  have h1 : qe y + 1 ≤ 2 * qe y := by linarith
  calc (2 * Real.pi) ^ 2 * qe y * (qe y + 1) ≤ (2 * Real.pi) ^ 2 * qe y * (2 * qe y) := by gcongr
    _ = (2 * Real.pi) ^ 2 * 2 * qe y ^ 2 := by ring

lemma abs_F3_le {y : ℝ} (hy : 0 < y) :
    |F3 y| ≤ 6 * (1 + 2 * Real.pi * y) ^ (3 + 1) / (2 * Real.pi * y ^ (3 + 1) * qe y) := by
  have hq := qe_gt_one hy
  have hq0 := qe_pos y
  have : F3 y = -((2 * Real.pi) ^ 3 * qe y * (qe y ^ 2 + 4 * qe y + 1) / (qe y - 1) ^ 4) := by
    unfold F3; ring
  rw [this, abs_neg, abs_of_pos (by positivity)]
  refine F_bound_aux hy 3 (by positivity) ?_
  have h1 : qe y ^ 2 + 4 * qe y + 1 ≤ 6 * qe y ^ 2 := by nlinarith
  calc (2 * Real.pi) ^ 3 * qe y * (qe y ^ 2 + 4 * qe y + 1)
      ≤ (2 * Real.pi) ^ 3 * qe y * (6 * qe y ^ 2) := by gcongr
    _ = (2 * Real.pi) ^ 3 * 6 * qe y ^ 3 := by ring

lemma abs_F4_le {y : ℝ} (hy : 0 < y) :
    |F4 y| ≤ 24 * (1 + 2 * Real.pi * y) ^ (4 + 1) / (2 * Real.pi * y ^ (4 + 1) * qe y) := by
  have hq := qe_gt_one hy
  have hq0 := qe_pos y
  rw [F4, abs_of_pos (by positivity)]
  refine F_bound_aux hy 4 (by positivity) ?_
  have h1 : qe y ^ 3 + 11 * qe y ^ 2 + 11 * qe y + 1 ≤ 24 * qe y ^ 3 := by
    nlinarith [sq_nonneg (qe y), mul_pos hq0 hq0]
  calc (2 * Real.pi) ^ 4 * qe y * (qe y ^ 3 + 11 * qe y ^ 2 + 11 * qe y + 1)
      ≤ (2 * Real.pi) ^ 4 * qe y * (24 * qe y ^ 3) := by gcongr
    _ = (2 * Real.pi) ^ 4 * 24 * qe y ^ 4 := by ring

/-! ### Bounds for `g_j` -/

lemma abs_g0_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 ≤ y) : |g0 a y| ≤ 1 / 12 * y ^ 5 / a ^ 2 := by
  unfold g0
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_nonneg hy 5, sq_nonneg y, mul_nonneg (pow_nonneg hy 5) (sq_nonneg y)]

lemma abs_g1_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 ≤ y) : |g1 a y| ≤ 5 / 12 * y ^ 4 / a ^ 2 := by
  unfold g1
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : 0 ≤ y ^ 4 := by positivity
  nlinarith [mul_nonneg h4 (sq_nonneg y), mul_nonneg (mul_nonneg h4 (sq_nonneg y)) (sq_nonneg y),
    mul_nonneg (mul_nonneg h4 (sq_nonneg y)) (sq_nonneg a), mul_nonneg h4 (sq_nonneg a),
    mul_nonneg (mul_nonneg h4 (sq_nonneg a)) (sq_nonneg a)]

lemma abs_g2_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 ≤ y) : |g2 a y| ≤ 10 / 6 * y ^ 3 / a ^ 2 := by
  unfold g2
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : 0 ≤ y ^ 3 := by positivity
  have hs : 0 ≤ (y ^ 2 + a ^ 2) := by positivity
  have key : 10 * a ^ 4 + 9 * a ^ 2 * y ^ 2 + 3 * y ^ 4 ≤ 10 * (y ^ 2 + a ^ 2) ^ 2 := by
    nlinarith [sq_nonneg y, sq_nonneg a, mul_nonneg (sq_nonneg y) (sq_nonneg a)]
  calc y ^ 3 * (10 * a ^ 4 + 9 * a ^ 2 * y ^ 2 + 3 * y ^ 4) * a ^ 2
      ≤ y ^ 3 * (10 * (y ^ 2 + a ^ 2) ^ 2) * a ^ 2 := by gcongr
    _ ≤ y ^ 3 * (10 * (y ^ 2 + a ^ 2) ^ 2) * (y ^ 2 + a ^ 2) := by gcongr; nlinarith [sq_nonneg y]
    _ = 10 / 6 * y ^ 3 * (6 * (y ^ 2 + a ^ 2) ^ 3) := by ring

lemma abs_g3_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 ≤ y) : |g3 a y| ≤ 5 * y ^ 2 / a ^ 2 := by
  unfold g3
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have hs : 0 ≤ (y ^ 2 + a ^ 2) := by positivity
  have key : 10 * a ^ 6 + 5 * a ^ 4 * y ^ 2 + 4 * a ^ 2 * y ^ 4 + y ^ 6 ≤ 10 * (y ^ 2 + a ^ 2) ^ 3 := by
    nlinarith [sq_nonneg y, sq_nonneg a, mul_nonneg (sq_nonneg y) (sq_nonneg a),
      mul_nonneg (mul_nonneg (sq_nonneg y) (sq_nonneg a)) (sq_nonneg y),
      mul_nonneg (mul_nonneg (sq_nonneg y) (sq_nonneg a)) (sq_nonneg a),
      pow_nonneg (sq_nonneg y) 3, pow_nonneg (sq_nonneg a) 3]
  calc y ^ 2 * (10 * a ^ 6 + 5 * a ^ 4 * y ^ 2 + 4 * a ^ 2 * y ^ 4 + y ^ 6) * a ^ 2
      ≤ y ^ 2 * (10 * (y ^ 2 + a ^ 2) ^ 3) * a ^ 2 := by gcongr
    _ ≤ y ^ 2 * (10 * (y ^ 2 + a ^ 2) ^ 3) * (y ^ 2 + a ^ 2) := by gcongr; nlinarith [sq_nonneg y]
    _ = 5 * y ^ 2 * (2 * (y ^ 2 + a ^ 2) ^ 4) := by ring

lemma g4_eq_mul_h4 (a y : ℝ) : g4 a y = y * h4 a y := by
  unfold g4 h4; ring

lemma abs_g4_le' {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 ≤ y) : |g4 a y| ≤ 20 * y / a ^ 2 := by
  rw [g4_eq_mul_h4, abs_mul, abs_of_nonneg hy]
  have h := abs_h4_le ha y
  have h2 : 20 / (y ^ 2 + a ^ 2) ≤ 20 / a ^ 2 := by
    gcongr; nlinarith [sq_nonneg y]
  calc y * |h4 a y| ≤ y * (20 / a ^ 2) := by gcongr; exact h.trans h2
    _ = 20 * y / a ^ 2 := by ring

/-! ### Product bounds -/

/-- `|G F| ≤ 4 y^e (1+2πy)^5 / (a² q)` from `|G| ≤ c y^(m+1+e)/a²`, `|F| ≤ d (1+2πy)^(m+1)/(2π y^(m+1) q)`,
`c d ≤ 8π`, `m + 1 ≤ 5`. -/
lemma prod_bound_aux {a y : ℝ} (ha : 0 < a) (hy : 0 < y) {G Fv c d : ℝ} {m e : ℕ}
    (hG : |G| ≤ c * y ^ (m + 1 + e) / a ^ 2)
    (hF : |Fv| ≤ d * (1 + 2 * Real.pi * y) ^ (m + 1) / (2 * Real.pi * y ^ (m + 1) * qe y))
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c * d ≤ 8 * Real.pi) (hm : m + 1 ≤ 5) :
    |G * Fv| ≤ 4 * y ^ e * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) := by
  have hq := qe_pos y
  have hpi := Real.pi_pos
  have hb : 1 ≤ 1 + 2 * Real.pi * y := by nlinarith
  have hpow : (1 + 2 * Real.pi * y) ^ (m + 1) ≤ (1 + 2 * Real.pi * y) ^ 5 :=
    pow_le_pow_right₀ hb hm
  rw [abs_mul]
  calc |G| * |Fv| ≤ (c * y ^ (m + 1 + e) / a ^ 2) *
        (d * (1 + 2 * Real.pi * y) ^ (m + 1) / (2 * Real.pi * y ^ (m + 1) * qe y)) :=
        mul_le_mul hG hF (abs_nonneg _) (by positivity)
    _ = (c * d / (2 * Real.pi)) * (y ^ e * (1 + 2 * Real.pi * y) ^ (m + 1) / (a ^ 2 * qe y)) := by
        rw [pow_add, pow_add]
        field_simp
        try ring
    _ ≤ (8 * Real.pi / (2 * Real.pi)) * (y ^ e * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y)) := by
        gcongr
    _ = 4 * y ^ e * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) := by
        field_simp
        try ring

lemma abs_g0F4_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g0 a y * F4 y| ≤ 4 * y ^ 0 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 4) (e := 0) (abs_g0_le ha hy.le) (abs_F4_le hy) (by norm_num) (by norm_num)
    (by nlinarith [Real.pi_gt_three]) (by norm_num)
lemma abs_g1F3_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g1 a y * F3 y| ≤ 4 * y ^ 0 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 3) (e := 0) (abs_g1_le ha hy.le) (abs_F3_le hy) (by norm_num) (by norm_num)
    (by nlinarith [Real.pi_gt_three]) (by norm_num)
lemma abs_g2F2_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g2 a y * F2 y| ≤ 4 * y ^ 0 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 2) (e := 0) (abs_g2_le ha hy.le) (abs_F2_le hy) (by norm_num) (by norm_num)
    (by nlinarith [Real.pi_gt_three]) (by norm_num)
lemma abs_g3F1_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g3 a y * F1 y| ≤ 4 * y ^ 0 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 1) (e := 0) (abs_g3_le ha hy.le) (abs_F1_le hy) (by norm_num) (by norm_num)
    (by nlinarith [Real.pi_gt_three]) (by norm_num)
lemma abs_g4F0_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g4 a y * F0 y| ≤ 4 * y ^ 0 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 0) (e := 0) (by simpa using abs_g4_le' ha hy.le) (abs_F0_le hy) (by norm_num)
    (by norm_num) (by nlinarith [Real.pi_gt_three]) (by norm_num)
lemma abs_g0F3_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g0 a y * F3 y| ≤ 4 * y ^ 1 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 3) (e := 1) (abs_g0_le ha hy.le) (abs_F3_le hy) (by norm_num) (by norm_num)
    (by nlinarith [Real.pi_gt_three]) (by norm_num)
lemma abs_g1F2_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g1 a y * F2 y| ≤ 4 * y ^ 1 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 2) (e := 1) (abs_g1_le ha hy.le) (abs_F2_le hy) (by norm_num) (by norm_num)
    (by nlinarith [Real.pi_gt_three]) (by norm_num)
lemma abs_g2F1_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g2 a y * F1 y| ≤ 4 * y ^ 1 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 1) (e := 1) (abs_g2_le ha hy.le) (abs_F1_le hy) (by norm_num) (by norm_num)
    (by nlinarith [Real.pi_gt_three]) (by norm_num)
lemma abs_g3F0_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g3 a y * F0 y| ≤ 4 * y ^ 1 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 0) (e := 1) (abs_g3_le ha hy.le) (abs_F0_le hy) (by norm_num) (by norm_num)
    (by nlinarith [Real.pi_gt_three]) (by norm_num)

/-! ### `(1 + x)^5 e^{-x} ≤ C e^{-x/2}` -/

lemma poly_exp_bound {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ 5 * Real.exp (-x) ≤ 122912 * Real.exp (-(x / 2)) := by
  have h1 : (1 + x) ^ 5 ≤ 32 * (1 + x ^ 5) := by
    rcases le_or_gt x 1 with h | h
    · have : (1 + x) ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
      have : 0 ≤ x ^ 5 := by positivity
      nlinarith
    · have : (1 + x) ^ 5 ≤ (2 * x) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
      have : 0 ≤ x ^ 5 := by positivity
      nlinarith
  have h2 := Real.pow_div_factorial_le_exp (x := x / 2) (by positivity) 5
  have h3 : x ^ 5 ≤ 3840 * Real.exp (x / 2) := by
    rw [Nat.factorial] at h2; norm_num at h2
    have : (x / 2) ^ 5 = x ^ 5 / 32 := by ring
    rw [this] at h2
    linarith
  have h4 : (1 : ℝ) ≤ Real.exp (x / 2) := Real.one_le_exp (by positivity)
  have h5 : (1 + x) ^ 5 ≤ 122912 * Real.exp (x / 2) := by nlinarith
  have he : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have he2 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by rw [← Real.exp_add]; simp
  calc (1 + x) ^ 5 * Real.exp (-x) ≤ 122912 * Real.exp (x / 2) * Real.exp (-x) := by
        gcongr
    _ = 122912 * Real.exp (-(x / 2)) * (Real.exp (x / 2) * Real.exp (-(x / 2))) := by rw [he]; ring
    _ = 122912 * Real.exp (-(x / 2)) := by rw [he2, mul_one]

lemma bound_exp {a y : ℝ} (ha : 0 < a) (hy : 0 < y) (e : ℕ) :
    4 * y ^ e * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) ≤
      4 * 122912 / a ^ 2 * (y ^ e * Real.exp (-(Real.pi * y))) := by
  have h := poly_exp_bound (x := 2 * Real.pi * y) (by positivity)
  have hq : qe y = Real.exp (2 * Real.pi * y) := rfl
  have hinv : 1 / qe y = Real.exp (-(2 * Real.pi * y)) := by rw [hq, Real.exp_neg, one_div]
  have hx2 : -(2 * Real.pi * y / 2) = -(Real.pi * y) := by ring
  rw [hx2] at h
  calc 4 * y ^ e * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y)
      = 4 / a ^ 2 * y ^ e * ((1 + 2 * Real.pi * y) ^ 5 * (1 / qe y)) := by field_simp
    _ = 4 / a ^ 2 * y ^ e * ((1 + 2 * Real.pi * y) ^ 5 * Real.exp (-(2 * Real.pi * y))) := by rw [hinv]
    _ ≤ 4 / a ^ 2 * y ^ e * (122912 * Real.exp (-(Real.pi * y))) := by gcongr
    _ = _ := by ring

/-! ### Continuity, integrability, limits -/

@[fun_prop] lemma continuous_qe : Continuous qe := by unfold qe; fun_prop

lemma qe_sub_one_ne {y : ℝ} (hy : y ∈ Ioi (0 : ℝ)) : qe y - 1 ≠ 0 := by
  have := qe_gt_one (show (0 : ℝ) < y from hy); linarith

lemma continuousOn_F0 : ContinuousOn F0 (Ioi 0) := by
  unfold F0; exact ContinuousOn.div continuousOn_const (by fun_prop) fun y hy => qe_sub_one_ne hy
lemma continuousOn_F1 : ContinuousOn F1 (Ioi 0) := by
  unfold F1; exact ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => pow_ne_zero _ (qe_sub_one_ne hy)
lemma continuousOn_F2 : ContinuousOn F2 (Ioi 0) := by
  unfold F2; exact ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => pow_ne_zero _ (qe_sub_one_ne hy)
lemma continuousOn_F3 : ContinuousOn F3 (Ioi 0) := by
  unfold F3; exact ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => pow_ne_zero _ (qe_sub_one_ne hy)
lemma continuousOn_F4 : ContinuousOn F4 (Ioi 0) := by
  unfold F4; exact ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => pow_ne_zero _ (qe_sub_one_ne hy)

lemma continuous_g0 {a : ℝ} (ha : 0 < a) : Continuous (g0 a) := by
  unfold g0; exact (by fun_prop : Continuous fun y : ℝ => y ^ 5).div (by fun_prop) (fun y => by positivity)
lemma continuous_g1 {a : ℝ} (ha : 0 < a) : Continuous (g1 a) := by
  unfold g1; exact (by fun_prop : Continuous fun y : ℝ => y ^ 4 * (5 * a ^ 2 + 3 * y ^ 2)).div (by fun_prop) (fun y => by positivity)
lemma continuous_g2 {a : ℝ} (ha : 0 < a) : Continuous (g2 a) := by
  unfold g2; exact (by fun_prop : Continuous fun y : ℝ => y ^ 3 * (10 * a ^ 4 + 9 * a ^ 2 * y ^ 2 + 3 * y ^ 4)).div (by fun_prop) (fun y => by positivity)
lemma continuous_g3 {a : ℝ} (ha : 0 < a) : Continuous (g3 a) := by
  unfold g3; exact (by fun_prop : Continuous fun y : ℝ => y ^ 2 * (10 * a ^ 6 + 5 * a ^ 4 * y ^ 2 + 4 * a ^ 2 * y ^ 4 + y ^ 6)).div (by fun_prop) (fun y => by positivity)

/-- Integrability on `(0, ∞)` of a product bounded by `4 y^0 (1+2πy)^5/(a² q)`. -/
lemma integrableOn_of_prod_bound {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    (hb : ∀ y, 0 < y → |f y| ≤ 4 * y ^ 0 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y)) :
    IntegrableOn f (Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ => 4 * 122912 / a ^ 2 * (y ^ 0 * Real.exp (-(Real.pi * y)))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_mul 0 Real.pi_pos).const_mul _
  refine hg.mono' (hf.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hy : 0 < y := hy
  rw [Real.norm_eq_abs]
  exact (hb y hy).trans (bound_exp ha hy 0)

/-- Vanishing at `0⁺` and `∞` of a product bounded by `4 y (1+2πy)^5/(a² q)`. -/
lemma tendsto_of_prod_bound {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hb : ∀ y, 0 < y → |f y| ≤ 4 * y ^ 1 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y)) :
    Tendsto f (𝓝[>] 0) (𝓝 0) ∧ Tendsto f atTop (𝓝 0) := by
  have hb' : ∀ y, 0 < y → |f y| ≤ 4 * 122912 / a ^ 2 * (y ^ 1 * Real.exp (-(Real.pi * y))) :=
    fun y hy => (hb y hy).trans (bound_exp ha hy 1)
  constructor
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun y => abs_nonneg _)
      (eventually_nhdsWithin_of_forall fun y hy => hb' y hy) ?_
    have hc : Continuous fun y : ℝ => 4 * 122912 / a ^ 2 * (y ^ 1 * Real.exp (-(Real.pi * y))) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    convert this using 2
    simp
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun y => abs_nonneg _)
      ((eventually_gt_atTop 0).mono fun y hy => hb' y hy) ?_
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.const_mul_atTop Real.pi_pos)
    have h2 : Tendsto (fun y : ℝ => y ^ 1 * Real.exp (-(Real.pi * y))) atTop (𝓝 0) := by
      have := h1.const_mul (1 / Real.pi)
      rw [mul_zero] at this
      refine this.congr' (Filter.Eventually.of_forall fun y => ?_)
      simp only [Function.comp, id, pow_one]
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      field_simp
    simpa using h2.const_mul (4 * 122912 / a ^ 2)

/-! ### The integrations by parts -/

lemma ibp_step {u u' v v' : ℝ → ℝ} (hu : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt u (u' y) y)
    (hv : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt v (v' y) y)
    (h1 : IntegrableOn (fun y => u y * v' y) (Ioi 0)) (h2 : IntegrableOn (fun y => u' y * v y) (Ioi 0))
    (h0 : Tendsto (fun y => u y * v y) (𝓝[>] 0) (𝓝 0)) (hinf : Tendsto (fun y => u y * v y) atTop (𝓝 0)) :
    ∫ y in Ioi 0, u y * v' y = -∫ y in Ioi 0, u' y * v y := by
  have := integral_Ioi_mul_deriv_eq_deriv_mul hu hv h1 h2 h0 hinf
  rw [this]; ring

/-- **Four integrations by parts**: `∫₀^∞ g F₄ = ∫₀^∞ g₄ F₀`. -/
theorem integral_g0F4_eq {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi 0, g0 a y * F4 y = ∫ y in Ioi 0, g4 a y * F0 y := by
  have hg0 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (g0 a) (g1 a y) y := fun y _ => hasDerivAt_g0 ha y
  have hg1 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (g1 a) (g2 a y) y := fun y _ => hasDerivAt_g1 ha y
  have hg2 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (g2 a) (g3 a y) y := fun y _ => hasDerivAt_g2 ha y
  have hg3 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (g3 a) (g4 a y) y := fun y _ => hasDerivAt_g3 ha y
  have hF0 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt F0 (F1 y) y := fun y hy => hasDerivAt_F0 hy
  have hF1 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt F1 (F2 y) y := fun y hy => hasDerivAt_F1 hy
  have hF2 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt F2 (F3 y) y := fun y hy => hasDerivAt_F2 hy
  have hF3 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt F3 (F4 y) y := fun y hy => hasDerivAt_F3 hy
  have i04 := integrableOn_of_prod_bound ha ((continuous_g0 ha).continuousOn.mul continuousOn_F4)
    (fun y hy => abs_g0F4_le ha hy)
  have i13 := integrableOn_of_prod_bound ha ((continuous_g1 ha).continuousOn.mul continuousOn_F3)
    (fun y hy => abs_g1F3_le ha hy)
  have i22 := integrableOn_of_prod_bound ha ((continuous_g2 ha).continuousOn.mul continuousOn_F2)
    (fun y hy => abs_g2F2_le ha hy)
  have i31 := integrableOn_of_prod_bound ha ((continuous_g3 ha).continuousOn.mul continuousOn_F1)
    (fun y hy => abs_g3F1_le ha hy)
  have i40 := integrableOn_of_prod_bound ha ((continuous_g4 a ha).continuousOn.mul continuousOn_F0)
    (fun y hy => abs_g4F0_le ha hy)
  obtain ⟨z03, t03⟩ := tendsto_of_prod_bound ha (f := fun y => g0 a y * F3 y) (fun y hy => abs_g0F3_le ha hy)
  obtain ⟨z12, t12⟩ := tendsto_of_prod_bound ha (f := fun y => g1 a y * F2 y) (fun y hy => abs_g1F2_le ha hy)
  obtain ⟨z21, t21⟩ := tendsto_of_prod_bound ha (f := fun y => g2 a y * F1 y) (fun y hy => abs_g2F1_le ha hy)
  obtain ⟨z30, t30⟩ := tendsto_of_prod_bound ha (f := fun y => g3 a y * F0 y) (fun y hy => abs_g3F0_le ha hy)
  have s0 := ibp_step hg0 hF3 i04 i13 z03 t03
  have s1 := ibp_step hg1 hF2 i13 i22 z12 t12
  have s2 := ibp_step hg2 hF1 i22 i31 z21 t21
  have s3 := ibp_step hg3 hF0 i31 i40 z30 t30
  rw [s0, s1, s2, s3]; ring

end Apery
end Port5

section Port6
/-!
# Hermite's formula at `s = 5` for integer arguments — port of `Apery/HermiteFormula.lean`

`∫₀^∞ w(y) / (y² + j²) dy = j⁴ (ζ(5) - H_j^{(5)}) - 1/4 + 1/(2j)` for `j ≥ 1`,
i.e. the pole moments (2.3) of the paper (Proposition 2.2).

Source: mo271/Zeta5 @ 7fe7367, `Apery/HermiteFormula.lean`.
-/

open Filter Topology Set MeasureTheory Finset

namespace Apery

/-- `∫₀^∞ y/(y² + a²)² dy = 1/(2a²)`. -/
lemma integral_y_div_sq_sq {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi 0, y / (y ^ 2 + a ^ 2) ^ 2 = 1 / (2 * a ^ 2) := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => -1 / (2 * (y ^ 2 + a ^ 2))) (y / (y ^ 2 + a ^ 2) ^ 2) y := by
    intro y
    have hne : 2 * (y ^ 2 + a ^ 2) ≠ 0 := by positivity
    have := (hasDerivAt_const y (-1 : ℝ)).div (((hasDerivAt_pow 2 y).add_const (a ^ 2)).const_mul 2) hne
    refine this.congr_deriv ?_
    field_simp
    ring
  have hint : IntegrableOn (fun y : ℝ => y / (y ^ 2 + a ^ 2) ^ 2) (Ioi 0) := by
    refine integrableOn_of_le_inv_sq ha (C := 1 / (2 * a)) ((by fun_prop : Continuous fun y : ℝ => y).div
      (by fun_prop) (fun y => by positivity)).aestronglyMeasurable (fun y hy => ?_)
    rw [abs_of_nonneg (by positivity)]
    have h2 : y / (y ^ 2 + a ^ 2) ≤ 1 / (2 * a) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_nonneg (y - a)]
    calc y / (y ^ 2 + a ^ 2) ^ 2 = (y / (y ^ 2 + a ^ 2)) * (1 / (y ^ 2 + a ^ 2)) := by
          field_simp
      _ ≤ (1 / (2 * a)) * (1 / (y ^ 2 + a ^ 2)) := by gcongr
      _ = 1 / (2 * a) / (y ^ 2 + a ^ 2) := by ring
  have hlim : Tendsto (fun y : ℝ => -1 / (2 * (y ^ 2 + a ^ 2))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact ((tendsto_pow_atTop two_ne_zero).atTop_add tendsto_const_nhds).const_mul_atTop two_pos
  have := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun y _ => hd y) hint hlim
  rw [this]
  field_simp
  ring

/-- `∫₀^∞ |k4 a n| ≤ 5a / n²`. -/
lemma integral_abs_k4_le {a n : ℝ} (ha : 0 < a) (hn : 0 < n) :
    ∫ y in Ioi 0, |k4 a n y| ≤ 5 * a / n ^ 2 := by
  have hint1 : IntegrableOn (fun y => |k4 a n y|) (Ioi 0) := (integrableOn_k4 ha hn).abs
  have hbase : IntegrableOn (fun y : ℝ => y / (y ^ 2 + a ^ 2) ^ 2) (Ioi 0) := by
    refine integrableOn_of_le_inv_sq ha (C := 1 / (2 * a)) ((by fun_prop : Continuous fun y : ℝ => y).div
      (by fun_prop) (fun y => by positivity)).aestronglyMeasurable (fun y hy => ?_)
    rw [abs_of_nonneg (by positivity)]
    have h2 : y / (y ^ 2 + a ^ 2) ≤ 1 / (2 * a) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_nonneg (y - a)]
    calc y / (y ^ 2 + a ^ 2) ^ 2 = (y / (y ^ 2 + a ^ 2)) * (1 / (y ^ 2 + a ^ 2)) := by
          field_simp
      _ ≤ (1 / (2 * a)) * (1 / (y ^ 2 + a ^ 2)) := by gcongr
      _ = 1 / (2 * a) / (y ^ 2 + a ^ 2) := by ring
  have hint2 : IntegrableOn (fun y : ℝ => 10 * a ^ 3 / n ^ 2 * (y / (y ^ 2 + a ^ 2) ^ 2)) (Ioi 0) :=
    hbase.const_mul _
  calc ∫ y in Ioi 0, |k4 a n y| ≤ ∫ y in Ioi 0, 10 * a ^ 3 / n ^ 2 * (y / (y ^ 2 + a ^ 2) ^ 2) := by
        refine setIntegral_mono_on hint1 hint2 measurableSet_Ioi fun y hy => ?_
        have hy : 0 < y := hy
        unfold k4
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ y / (y ^ 2 + n ^ 2))]
        have h1 := abs_g4_le ha hy.le
        have h2 : y / (y ^ 2 + n ^ 2) ≤ y / n ^ 2 := by
          gcongr; nlinarith [sq_nonneg y]
        calc |g4 a y| * (y / (y ^ 2 + n ^ 2)) ≤ 10 * a ^ 3 / (y ^ 2 + a ^ 2) ^ 2 * (y / n ^ 2) := by gcongr
          _ = 10 * a ^ 3 / n ^ 2 * (y / (y ^ 2 + a ^ 2) ^ 2) := by ring
    _ = 10 * a ^ 3 / n ^ 2 * (1 / (2 * a ^ 2)) := by rw [integral_const_mul, integral_y_div_sq_sq ha]
    _ = 5 * a / n ^ 2 := by field_simp; ring

/-- `∑_{n ≥ 0} 1/(n + j + 1)⁵ = ζ(5) - H_j^{(5)}`. -/
lemma tsum_tail_eq (j : ℕ) :
    ∑' n : ℕ, 1 / ((j : ℝ) + ((n : ℝ) + 1)) ^ 5 = zeta5 - (H5 j : ℝ) := by
  have hz : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 5) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h := hz.sum_add_tsum_nat_add (j + 1)
  have hH : ∑ i ∈ range (j + 1), 1 / ((i : ℝ)) ^ 5 = (H5 j : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, add_zero]
    unfold H5
    push_cast
    have e1 : Finset.Icc 1 j = Finset.Ico 1 (j + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e1, Finset.sum_Ico_eq_sum_range, show j + 1 - 1 = j by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  have htail : ∑' n : ℕ, 1 / ((j : ℝ) + ((n : ℝ) + 1)) ^ 5 = ∑' n : ℕ, 1 / ((n + (j + 1) : ℕ) : ℝ) ^ 5 := by
    refine tsum_congr fun n => ?_
    push_cast; ring_nf
  rw [htail, ← hH]
  unfold zeta5
  linarith

/-- **Hermite's formula at `s = 5`** (the pole moments (2.3) of the paper). -/
theorem hermite_pole (j : ℕ) (hj : 1 ≤ j) :
    ∫ y in Ioi 0, w y / (y ^ 2 + (j : ℝ) ^ 2) =
      (j : ℝ) ^ 4 * (zeta5 - (H5 j : ℝ)) - 1 / 4 + 1 / (2 * (j : ℝ)) := by
  set a : ℝ := (j : ℝ) with ha_def
  have ha : 0 < a := by rw [ha_def]; exact_mod_cast hj
  -- Step 1: `w / (y² + a²) = g₀ · F₄`
  have h1 : ∫ y in Ioi 0, w y / (y ^ 2 + a ^ 2) = ∫ y in Ioi 0, g0 a y * F4 y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy : 0 < y := hy
    have hne : y ^ 2 + a ^ 2 ≠ 0 := by positivity
    rw [w_eq_F4 hy]; unfold g0; field_simp; try ring
  -- Step 2: integrate by parts four times
  rw [h1, integral_g0F4_eq ha]
  -- Step 3: the pointwise decomposition of `g₄ F₀`
  have hdec : ∀ y, 0 < y → g4 a y * F0 y =
      -(1 / 2) * g4 a y + 1 / (2 * Real.pi) * h4 a y + 1 / Real.pi * ∑' n : ℕ, k4 a ((n : ℝ) + 1) y := by
    intro y hy
    rw [F0_series hy, ← g4_div_eq_h4 a hy.ne']
    simp only [k4]
    rw [tsum_mul_left]
    have hy' : y ≠ 0 := hy.ne'
    field_simp
    try ring
  -- Step 4: integrability of the pieces
  have hA : IntegrableOn (fun y => -(1 / 2) * g4 a y) (Ioi 0) := (integrableOn_g4 ha).const_mul _
  have hB : IntegrableOn (fun y => 1 / (2 * Real.pi) * h4 a y) (Ioi 0) := (integrableOn_h4 ha).const_mul _
  have hprod : IntegrableOn (fun y => g4 a y * F0 y) (Ioi 0) :=
    integrableOn_of_prod_bound ha ((continuous_g4 a ha).continuousOn.mul continuousOn_F0)
      (fun y hy => abs_g4F0_le ha hy)
  have hC : IntegrableOn (fun y => 1 / Real.pi * ∑' n : ℕ, k4 a ((n : ℝ) + 1) y) (Ioi 0) := by
    have := (hprod.sub hA).sub hB
    refine this.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy : 0 < y := hy
    simp only [Pi.sub_apply]
    rw [hdec y hy]; ring
  -- Step 5: the series of integrals
  have hnorm : Summable fun n : ℕ => ∫ y in Ioi 0, ‖k4 a ((n : ℝ) + 1) y‖ := by
    have hs : Summable fun n : ℕ => 5 * a / ((n : ℝ) + 1) ^ 2 := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
      refine (this.mul_left (5 * a)).congr fun n => ?_
      push_cast; ring
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) (fun n => ?_) hs
    simp only [Real.norm_eq_abs]
    exact integral_abs_k4_le ha (by positivity)
  have hsum : ∫ y in Ioi 0, ∑' n : ℕ, k4 a ((n : ℝ) + 1) y =
      ∑' n : ℕ, ∫ y in Ioi 0, k4 a ((n : ℝ) + 1) y :=
    (integral_tsum_of_summable_integral_norm (fun n => integrableOn_k4 ha (by positivity)) hnorm).symm
  have hval : ∀ n : ℕ, ∫ y in Ioi 0, k4 a ((n : ℝ) + 1) y = Real.pi * a ^ 4 / (a + ((n : ℝ) + 1)) ^ 5 :=
    fun n => integral_k4 ha (by positivity)
  -- Step 6: assemble
  have hAB : IntegrableOn (fun y => -(1 / 2) * g4 a y + 1 / (2 * Real.pi) * h4 a y) (Ioi 0) := hA.add hB
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => hdec y hy), integral_add hAB hC,
    integral_add hA hB, integral_const_mul, integral_const_mul, integral_const_mul, integral_g4 ha,
    integral_h4 ha, hsum, tsum_congr hval]
  have htail : ∑' n : ℕ, Real.pi * a ^ 4 / (a + ((n : ℝ) + 1)) ^ 5 =
      Real.pi * a ^ 4 * (zeta5 - (H5 j : ℝ)) := by
    rw [← tsum_tail_eq j, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [ha_def]; ring
  rw [htail]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

end Apery
end Port6

section Port7
/-!
# Proposition 2.2 — port of `Apery/Positivity.lean`

* `integrableOn_pole`: integrability of `w(y)/(y²+j²)`;
* `integrand_eq_sum`: the pointwise decomposition of the integrand;
* `aeval_μX`: the value of `μ_{ζ(5)}` in terms of quotient coefficients and residues;
* `moment_rep`: `μ_{ζ(5)}(P / D_K) = ∫₀^∞ (P / D_K)(y²) w(y) dy` with integrability;
* `Δ_pos`: `Δ_K(ζ(5)) > 0`, since `G_K(ζ(5))` is the Gram matrix of a positive weight.

Source: mo271/Zeta5 @ 7fe7367, `Apery/Positivity.lean`.
-/

open Polynomial MeasureTheory Set Finset
open scoped Matrix

namespace Apery

lemma integrableOn_pole (j : ℕ) (hj : 1 ≤ j) :
    IntegrableOn (fun y => w y / (y ^ 2 + (j : ℝ) ^ 2)) (Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ => 32 * (y ^ 1 * Real.exp (-(Real.pi * y))) +
      11 * (y ^ 0 * Real.exp (-(Real.pi * y)))) (Ioi 0) :=
    ((integrableOn_pow_mul_exp_neg_mul 1 Real.pi_pos).const_mul 32).add
      ((integrableOn_pow_mul_exp_neg_mul 0 Real.pi_pos).const_mul 11)
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  refine hg.mono' (aemeasurable_w.div (by fun_prop : Measurable fun y : ℝ => y ^ 2 + (j : ℝ) ^ 2).aemeasurable).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hy : 0 < y := hy
  have hw := w_pos hy
  have hden : (1 : ℝ) ≤ y ^ 2 + (j : ℝ) ^ 2 := by nlinarith
  rw [Real.norm_of_nonneg (div_nonneg hw.le (by positivity))]
  calc w y / (y ^ 2 + (j : ℝ) ^ 2) ≤ w y := div_le_self hw.le hden
    _ ≤ (32 * y + 11) * Real.exp (-(Real.pi * y)) := w_le hy
    _ = _ := by ring

/-- The pointwise decomposition of the integrand, for `y > 0`. -/
lemma integrand_eq_sum (K : ℕ) (P : ℚ[X]) {y : ℝ} (hy : 0 < y) :
    integrand K P y =
      (∑ e ∈ range ((P /ₘ D K).natDegree + 1),
          ((P /ₘ D K).coeff e : ℝ) * (y ^ (2 * e) * w y)) +
        ∑ j ∈ Icc 1 K, (res K P j : ℝ) * (w y / (y ^ 2 + (j : ℝ) ^ 2)) := by
  unfold integrand
  rw [partial_fractions K P (t := y ^ 2) (by positivity), aeval_eq_sum_range, add_mul,
    Finset.sum_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    try simp only [Rat.smul_def, eq_ratCast, ← pow_mul]
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The value `μ_{ζ(5)}(P / D_K)` in terms of the coefficients of the quotient and residues. -/
lemma aeval_μX (K : ℕ) (P : ℚ[X]) :
    aeval zeta5 (μX K P) =
      (∑ e ∈ range ((P /ₘ D K).natDegree + 1), ((P /ₘ D K).coeff e : ℝ) * (μmono e : ℝ)) +
        ∑ j ∈ Icc 1 K, (res K P j : ℝ) *
          ((j : ℝ) ^ 4 * (zeta5 - (H5 j : ℝ)) - 1 / 4 + 1 / (2 * (j : ℝ))) := by
  simp only [μX, map_add, aeval_C, map_sum, map_mul, poleValue, map_sub, aeval_X, eq_ratCast]
  congr 1
  · unfold μpoly
    rw [Polynomial.sum_over_range' _ (fun n => by simp) _ (Nat.lt_succ_self _)]
    push_cast
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [res]
    push_cast
    ring

/-- **Proposition 2.2** (the moment representation): for every polynomial `P`, the function
`(P / D_K)(y²) w(y)` is integrable on `(0, ∞)` and its integral is `μ_{ζ(5)}(P / D_K)`. -/
theorem moment_rep_port (K : ℕ) (P : ℚ[X]) :
    IntegrableOn (integrand K P) (Ioi 0) ∧
      aeval zeta5 (μX K P) = ∫ y in Ioi 0, integrand K P y := by
  set Q := P /ₘ D K with hQ
  have hint1 : ∀ e ∈ range (Q.natDegree + 1),
      IntegrableOn (fun y => (Q.coeff e : ℝ) * (y ^ (2 * e) * w y)) (Ioi 0) :=
    fun e _ => (mono_moment e).1.const_mul _
  have hint2 : ∀ j ∈ Finset.Icc 1 K,
      IntegrableOn (fun y => (res K P j : ℝ) * (w y / (y ^ 2 + (j : ℝ) ^ 2))) (Ioi 0) :=
    fun j hj => (integrableOn_pole j (Finset.mem_Icc.mp hj).1).const_mul _
  have hsumint : IntegrableOn (fun y =>
      (∑ e ∈ range (Q.natDegree + 1), (Q.coeff e : ℝ) * (y ^ (2 * e) * w y)) +
        ∑ j ∈ Icc 1 K, (res K P j : ℝ) * (w y / (y ^ 2 + (j : ℝ) ^ 2))) (Ioi 0) :=
    (integrable_finsetSum _ hint1).add (integrable_finsetSum _ hint2)
  have hEq : EqOn (fun y =>
      (∑ e ∈ range (Q.natDegree + 1), (Q.coeff e : ℝ) * (y ^ (2 * e) * w y)) +
        ∑ j ∈ Icc 1 K, (res K P j : ℝ) * (w y / (y ^ 2 + (j : ℝ) ^ 2))) (integrand K P) (Ioi 0) :=
    fun y hy => (integrand_eq_sum K P hy).symm
  refine ⟨hsumint.congr_fun hEq measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hEq, integral_add (integrable_finsetSum _ hint1)
    (integrable_finsetSum _ hint2), integral_finsetSum _ hint1, integral_finsetSum _ hint2,
    aeval_μX]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [integral_const_mul, (mono_moment e).2]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_const_mul, hermite_pole j (Finset.mem_Icc.mp hj).1]

/-- The positive weight `ν(y) = D_N(y²)^6 / D_K(y²) · w(y)`. -/
noncomputable def ν (n : ℕ) (y : ℝ) : ℝ :=
  aeval (y ^ 2) (D (3 * n)) ^ 6 / aeval (y ^ 2) (D (40 * n)) * w y

lemma ν_pos (n : ℕ) {y : ℝ} (hy : 0 < y) : 0 < ν n y := by
  unfold ν
  have h1 := aeval_D_pos (3 * n) (t := y ^ 2) (by positivity)
  have h2 := aeval_D_pos (40 * n) (t := y ^ 2) (by positivity)
  have h3 := w_pos hy
  positivity

lemma integrand_eq (n : ℕ) (i j : ℕ) (y : ℝ) :
    integrand (40 * n) (D (3 * n) ^ 6 * X ^ (i + j)) y =
      (y ^ 2) ^ i * (y ^ 2) ^ j * ν n y := by
  simp only [integrand, ν, map_mul, map_pow, aeval_X]
  rw [pow_add]; ring

/-- **Positivity**: `Δ_K(ζ(5)) > 0`, from the moment representation. -/
theorem delta_pos_port (n : ℕ) (_hn : 0 < n) : 0 < aeval zeta5 (Δ n) := by
  have hdet : aeval zeta5 (Δ n) = ((G n).map (aeval zeta5)).det := by
    have := RingHom.map_det (aeval zeta5 : ℚ[X] →ₐ[ℚ] ℝ).toRingHom (G n)
    simpa [Δ, RingHom.mapMatrix_apply] using this
  rw [hdet]
  set M : Matrix (Fin (37 * n)) (Fin (37 * n)) ℝ := (G n).map (aeval zeta5) with hM
  have hentry : ∀ i j : Fin (37 * n), M i j =
      ∫ y in Ioi 0, integrand (40 * n) (D (3 * n) ^ 6 * X ^ ((i : ℕ) + (j : ℕ))) y :=
    fun i j => (moment_rep_port _ _).2
  have hint : ∀ i j : Fin (37 * n),
      IntegrableOn (integrand (40 * n) (D (3 * n) ^ 6 * X ^ ((i : ℕ) + (j : ℕ)))) (Ioi 0) :=
    fun i j => (moment_rep_port _ _).1
  apply Matrix.PosDef.det_pos
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [star_trivial, hM, Matrix.map_apply, G]
    rw [Nat.add_comm (j : ℕ) i]
  · intro x hx
    set f : Fin (37 * n) → Fin (37 * n) → ℝ → ℝ := fun i j y =>
      x i * x j * integrand (40 * n) (D (3 * n) ^ 6 * X ^ ((i : ℕ) + (j : ℕ))) y with hf
    have hfint : ∀ i j, IntegrableOn (f i j) (Ioi 0) := fun i j => (hint i j).const_mul _
    have hpt : ∀ y, ∑ i, ∑ j, f i j y = (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y := by
      intro y
      simp only [hf, integrand_eq]
      rw [sq (∑ i, x i * (y ^ 2) ^ (i : ℕ)), Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hq : star x ⬝ᵥ (M *ᵥ x) = ∫ y in Ioi 0, (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y := by
      have h1 : star x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, ∫ y in Set.Ioi 0, f i j y := by
        simp only [dotProduct, Matrix.mulVec, star_trivial, hentry, hf, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]; ring
      rw [h1]
      have h2 : ∀ i, ∑ j, ∫ y in Set.Ioi 0, f i j y = ∫ y in Set.Ioi 0, ∑ j, f i j y :=
        fun i => (integral_finsetSum _ (fun j _ => hfint i j)).symm
      simp_rw [h2]
      rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hfint i j))]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => hpt y)
    rw [hq]
    have hsq : IntegrableOn (fun y => (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y) (Ioi 0) := by
      have : (fun y => (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y) = fun y => ∑ i, ∑ j, f i j y :=
        funext fun y => (hpt y).symm
      rw [this]
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hfint i j
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
        fun y => (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y := by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
      exact mul_nonneg (sq_nonneg _) (ν_pos n hy).le
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hsq]
    set q : ℝ[X] := ∑ i : Fin (37 * n), C (x i) * X ^ (i : ℕ) with hqdef
    have hqeval : ∀ y : ℝ, q.eval (y ^ 2) = ∑ i, x i * (y ^ 2) ^ (i : ℕ) := by
      intro y; simp [hqdef, eval_finsetSum]
    have hq0 : q ≠ 0 := by
      intro h0
      apply hx
      funext i
      have hc : q.coeff (i : ℕ) = x i := by
        simp only [hqdef, finsetSum_coeff, coeff_C_mul_X_pow]
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb; rw [if_neg]; exact fun h => hb (Fin.ext h.symm)
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [← hc, h0, coeff_zero]; rfl
    have hroots : Set.Finite {t : ℝ | IsRoot q t} := Polynomial.finite_setOfPred_isRoot hq0
    have hB : Set.Finite {y : ℝ | IsRoot q (y ^ 2)} := by
      refine (hroots.image Real.sqrt |>.union (hroots.image fun t => -Real.sqrt t)).subset ?_
      intro y hy
      simp only [Set.mem_ofPred_eq] at hy
      rcases le_or_gt 0 y with h | h
      · exact Or.inl ⟨y ^ 2, hy, Real.sqrt_sq h⟩
      · exact Or.inr ⟨y ^ 2, hy, by
          show -Real.sqrt (y ^ 2) = y
          rw [Real.sqrt_sq_eq_abs, abs_of_neg h, neg_neg]⟩
    have hsub : Set.Ioi 0 \ {y : ℝ | IsRoot q (y ^ 2)} ⊆
        Function.support (fun y => (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y) ∩ Set.Ioi 0 := by
      intro y hy
      obtain ⟨hy0, hyB⟩ := hy
      refine ⟨?_, hy0⟩
      simp only [Function.mem_support]
      have hqy : q.eval (y ^ 2) ≠ 0 := fun h => hyB h
      rw [hqeval] at hqy
      exact mul_ne_zero (pow_ne_zero _ hqy) (ν_pos n hy0).ne'
    calc (0 : ENNReal) < ⊤ := ENNReal.zero_lt_top
      _ = volume (Set.Ioi (0 : ℝ) \ {y : ℝ | IsRoot q (y ^ 2)}) := by
        rw [measure_sdiff_null (hB.measure_zero volume), Real.volume_Ioi]
      _ ≤ _ := measure_mono hsub

end Apery
end Port7


open MeasureTheory Polynomial in
/-- The platform target `Apery.moment_rep`, restated at top level as `solution`. -/
theorem solution (K : ℕ) (P : ℚ[X]) :
    IntegrableOn (Apery.integrand K P) (Set.Ioi 0) ∧
      aeval Apery.zeta5 (Apery.μX K P) = ∫ y in Set.Ioi 0, Apery.integrand K P y :=
  Apery.moment_rep_port K P
