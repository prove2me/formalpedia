-- Prove2me | solution 1 for ActualXiBranchesPublished.concrete_G_positive_from_product
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T09:17:09.740381+00:00
-- url     : https://prove2.me/submissions/a1c750b4-6a56-4db2-a8c0-0ee4acd63679

import Mathlib
universe u
variable {ι : Type u} [Countable ι]

open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
namespace CountingTail

theorem weight_integrable (t A : ℝ) (ht : 0 < t) (hA : 0 ≤ A) :
    IntegrableOn (fun y : ℝ => t*y*Real.exp (-(t*y))) (Ioi A) := by
  have hi : IntegrableOn (fun y : ℝ => y*Real.exp (-(t*y))) (Ioi 0) := by
    by_contra h
    have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := t) (by norm_num) ht
    norm_num at hg
    rw [integral_undef h] at hg
    have hp : 0 < (t^2)⁻¹ := by positivity
    linarith
  have hj : IntegrableOn (fun y : ℝ => t*(y*Real.exp (-(t*y)))) (Ioi 0) := hi.const_mul t
  simpa only [mul_assoc] using hj.mono_set (Ioi_subset_Ioi hA)

theorem integral_weight (t A : ℝ) (ht : 0 < t) (hA : 0 ≤ A) :
    (∫ y : ℝ in Ioi A, t*y*Real.exp (-(t*y))) =
      (A+t⁻¹)*Real.exp (-(t*A)) := by
  have hd (y : ℝ) : HasDerivAt (fun y : ℝ => -(y+t⁻¹)*Real.exp (-(t*y)))
      (t*y*Real.exp (-(t*y))) y := by
    have he := (Real.hasDerivAt_exp (-t*y)).comp y ((hasDerivAt_id y).const_mul (-t))
    have hh := (((hasDerivAt_id y).add_const t⁻¹).neg).mul he
    convert! hh using 1
    · funext x
      simp only [Pi.mul_apply, Pi.neg_apply, Function.comp_apply, id_eq, neg_mul]
    · dsimp
      field_simp
      <;> ring
  have h0 : Tendsto (fun y : ℝ => Real.exp (-(t*y))) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) t ht
  have h1 : Tendsto (fun y : ℝ => y*Real.exp (-(t*y))) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) t ht
  have hz : Tendsto (fun y : ℝ => -(y+t⁻¹)*Real.exp (-(t*y))) atTop (𝓝 0) := by
    convert (h1.add (h0.const_mul t⁻¹)).neg using 1 <;> simp <;> ring
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto' (fun y _ => hd y)
    (weight_integrable t A ht hA) hz
  rw [hh]
  ring

theorem indicator_integrable (t A a : ℝ) (ht : 0 < t) :
    IntegrableOn ((Ioi a).indicator (fun y : ℝ => t*Real.exp (-(t*y)))) (Ioi A) := by
  apply Integrable.indicator _ measurableSet_Ioi
  simpa only [neg_mul] using (integrableOn_exp_mul_Ioi (neg_neg_of_pos ht) A).const_mul t

theorem indicator_integral (t A a : ℝ) (ht : 0 < t) (hAa : A ≤ a) :
    (∫ y : ℝ in Ioi A, (Ioi a).indicator (fun y : ℝ => t*Real.exp (-(t*y))) y) =
      Real.exp (-(t*a)) := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hAa), integral_const_mul]
  have he := integral_exp_mul_Ioi (neg_neg_of_pos ht) a
  simp only [neg_mul] at he
  rw [he]
  field_simp

theorem finite_tail_bound (a : ι → ℝ) (F : Finset ι) (t A : ℝ)
    (ht : 0 < t) (hA : 0 ≤ A) (hF : ∀ j ∈ F, A < a j)
    (hcount : ∀ y ≥ A, ((F.filter (fun j => a j < y)).card : ℝ) ≤ y) :
    (∑ j ∈ F, Real.exp (-(t*a j))) ≤ (A+t⁻¹)*Real.exp (-(t*A)) := by
  classical
  have hi := fun j (_ : j ∈ F) => indicator_integrable t A (a j) ht
  calc
    _ = ∑ j ∈ F, ∫ y : ℝ in Ioi A,
        (Ioi (a j)).indicator (fun y : ℝ => t*Real.exp (-(t*y))) y := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (indicator_integral t A (a j) ht (hF j hj).le).symm
    _ = ∫ y : ℝ in Ioi A, ∑ j ∈ F,
        (Ioi (a j)).indicator (fun y : ℝ => t*Real.exp (-(t*y))) y :=
      (integral_finsetSum F hi).symm
    _ ≤ ∫ y : ℝ in Ioi A, t*y*Real.exp (-(t*y)) := by
      apply integral_mono_ae (integrable_finset_sum F hi) (weight_integrable t A ht hA)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have he : (∑ j ∈ F, (Ioi (a j)).indicator
          (fun y : ℝ => t*Real.exp (-(t*y))) y) =
          ((F.filter (fun j => a j < y)).card : ℝ) * (t*Real.exp (-(t*y))) := by
        simp only [Set.indicator, mem_Ioi]
        rw [← Finset.sum_filter]
        simp
      rw [he]
      have hh := mul_le_mul_of_nonneg_right (hcount y (mem_Ioi.mp hy).le)
        (mul_nonneg ht.le (Real.exp_pos (-(t*y))).le)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
    _ = _ := integral_weight t A ht hA

theorem tail_summable_and_bound (a : ι → ℝ) (t A : ℝ)
    (ht : 0 < t) (hA : 0 ≤ A)
    (hcount : ∀ y ≥ A, ∀ F : Finset ι,
      (∀ j ∈ F, a j ≤ y) → (F.card : ℝ) ≤ y) :
    Summable (fun j => if A < a j then Real.exp (-(t*a j)) else 0) ∧
    (∑' j, if A < a j then Real.exp (-(t*a j)) else 0) ≤
      (A+t⁻¹)*Real.exp (-(t*A)) := by
  classical
  have hb (F : Finset ι) :
      (∑ j ∈ F, if A < a j then Real.exp (-(t*a j)) else 0) ≤
        (A+t⁻¹)*Real.exp (-(t*A)) := by
    rw [← Finset.sum_filter]
    apply finite_tail_bound a _ t A ht hA
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro y hy
      apply hcount y hy
      intro j hj
      exact ((Finset.mem_filter.mp hj).2).le
  have hs := summable_of_sum_le (fun j => by split_ifs <;> positivity) hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

theorem full_summable (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (t A : ℝ)
    (ht : 0 < t) (hA : 0 ≤ A)
    (hcount : ∀ y ≥ A, ∀ F : Finset ι,
      (∀ j ∈ F, a j ≤ y) → (F.card : ℝ) ≤ y) :
    Summable (fun j => Real.exp (-(t*a j))) := by
  classical
  apply summable_of_sum_le (fun j => (Real.exp_pos _).le)
    (c := A+(A+t⁻¹)*Real.exp (-(t*A)))
  intro F
  rw [← Finset.sum_filter_add_sum_filter_not F (fun j => A < a j)]
  have htail : (∑ j ∈ F.filter (fun j => A < a j), Real.exp (-(t*a j))) ≤
      (A+t⁻¹)*Real.exp (-(t*A)) := by
    apply finite_tail_bound a _ t A ht hA
    · intro j hj; exact (Finset.mem_filter.mp hj).2
    · intro y hy
      apply hcount y hy
      intro j hj; exact ((Finset.mem_filter.mp hj).2).le
  have hhead : (∑ j ∈ F.filter (fun j => ¬ A < a j), Real.exp (-(t*a j))) ≤ A := by
    calc
      _ ≤ ∑ j ∈ F.filter (fun j => ¬ A < a j), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Real.exp_le_one_iff.mpr
        exact neg_nonpos.mpr (mul_nonneg ht.le (ha j))
      _ = ((F.filter (fun j => ¬ A < a j)).card : ℝ) := by simp
      _ ≤ A := hcount A le_rfl _ (fun j hj => le_of_not_gt (Finset.mem_filter.mp hj).2)
  linarith

theorem gaussian_from_counting (gamma : ι → ℝ) (hg : ∀ j, 0 ≤ gamma j)
    (hcount : ∀ T ≥ (10 : ℝ), ∀ F : Finset ι,
      (∀ j ∈ F, gamma j ≤ T) → (F.card : ℝ) ≤ T^2) :
    (∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t))) ∧
    (∀ t > 0, ∀ L ≥ (10 : ℝ),
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
        (L^2+t⁻¹)*Real.exp (-L^2*t)) := by
  have hc (L : ℝ) (hL : 10 ≤ L) :
      ∀ y ≥ L^2, ∀ F : Finset ι,
      (∀ j ∈ F, (gamma j)^2 ≤ y) → (F.card : ℝ) ≤ y := by
    intro y hy F hF
    have hy0 : 0 ≤ y := le_trans (sq_nonneg L) hy
    have hs : (Real.sqrt y)^2 = y := Real.sq_sqrt hy0
    have hs0 := Real.sqrt_nonneg y
    have hs10 : 10 ≤ Real.sqrt y := by nlinarith
    have hh := hcount (Real.sqrt y) hs10 F (by
      intro j hj
      have hjj := hF j hj
      nlinarith [hg j])
    simpa only [hs] using hh
  constructor
  · intro t ht
    have hh := full_summable (fun j => (gamma j)^2) (fun j => sq_nonneg _) t 100
      ht (by norm_num) (by simpa only [show (10:ℝ)^2=100 by norm_num] using hc 10 le_rfl)
    simpa only [neg_mul, mul_comm t] using hh
  · intro t ht L hL
    have hh := (tail_summable_and_bound (fun j => (gamma j)^2) t (L^2)
      ht (sq_nonneg L) (hc L hL)).2
    have he (j : ι) : L^2 < (gamma j)^2 ↔ L < gamma j := by
      constructor <;> intro h <;> nlinarith [hg j]
    simpa only [he, neg_mul, mul_comm t] using hh

end CountingTail


open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
namespace ReciprocalCounting

theorem indicator_integrable (a : ℝ) :
    IntegrableOn ((Ioi a).indicator (fun y : ℝ => y^(-2 : ℝ))) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)).indicator measurableSet_Ioi

theorem indicator_integral (a : ℝ) (ha : 1 ≤ a) :
    (∫ y : ℝ in Ioi 1, (Ioi a).indicator (fun y : ℝ => y^(-2 : ℝ)) y) = a⁻¹ := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi ha)]
  have hh := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (show 0 < a by linarith)
  simpa only [show (-2 : ℝ)+1 = -1 by norm_num, Real.rpow_neg_one,
    div_neg, div_one, neg_neg] using hh

theorem summable_inverse_from_sublinear_count (a : ι → ℝ) (ha : ∀ j, 1 ≤ a j)
    (C r : ℝ) (hr : r < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ j ∈ F, a j ≤ y) → (F.card : ℝ) ≤ C*y^r) :
    Summable (fun j => (a j)⁻¹) ∧ (∑' j, (a j)⁻¹) ≤ C/(1-r) := by
  classical
  have hi : IntegrableOn (fun y : ℝ => C*y^(r-2)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : r-2 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul C
  have hb (F : Finset ι) : (∑ j ∈ F, (a j)⁻¹) ≤ C/(1-r) := by
    calc
      _ = ∑ j ∈ F, ∫ y : ℝ in Ioi 1,
          (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (indicator_integral (a j) (ha j)).symm
      _ = ∫ y : ℝ in Ioi 1, ∑ j ∈ F,
          (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y :=
        (integral_finsetSum F (fun j _ => indicator_integrable (a j))).symm
      _ ≤ ∫ y : ℝ in Ioi 1, C*y^(r-2) := by
        apply integral_mono_ae (integrable_finset_sum F (fun j _ => indicator_integrable (a j))) hi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        have hy1 : 1 ≤ y := (mem_Ioi.mp hy).le
        have hy0 : 0 ≤ y := by linarith
        have he : (∑ j ∈ F, (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y) =
            ((F.filter (fun j => a j < y)).card : ℝ)*y^(-2 : ℝ) := by
          simp only [Set.indicator, mem_Ioi]
          rw [← Finset.sum_filter]
          simp
        rw [he]
        have hc := hcount y hy1 (F.filter (fun j => a j < y))
          (fun j hj => (Finset.mem_filter.mp hj).2.le)
        calc
          _ ≤ (C*y^r)*y^(-2 : ℝ) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hy0 _)
          _ = C*y^(r-2) := by rw [mul_assoc, ← Real.rpow_add (show 0 < y by linarith)]; congr 2 <;> ring
      _ = C/(1-r) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : r-2 < -1) (by norm_num)]
        rw [show r-2+1 = -(1-r) by ring]
        simp only [Real.one_rpow, div_neg, neg_neg, one_div]
        ring
  have hs := summable_of_sum_le (fun j => inv_nonneg.mpr (by linarith [ha j])) hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

end ReciprocalCounting



open scoped BigOperators
open Set Filter Topology
noncomputable section
namespace HadamardSeries

def domain : Set ℂ := {z | -(1/2 : ℝ) < z.re}

theorem domain_open : IsOpen domain :=
  isOpen_lt continuous_const Complex.continuous_re

theorem domain_convex : Convex ℝ domain := by
  intro x hx y hy a b ha hb hab
  change -(1/2 : ℝ) < (a • x + b • y).re
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  change -(1/2 : ℝ) < x.re at hx
  change -(1/2 : ℝ) < y.re at hy
  by_cases h : a = 0
  · subst a
    have hbb : b = 1 := by linarith
    simpa [hbb] using hy
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
    nlinarith [mul_pos hap (show 0 < x.re+1/2 by linarith),
      mul_nonneg hb (show 0 ≤ y.re+1/2 by linarith)]

theorem zero_mem : (0 : ℂ) ∈ domain := by norm_num [domain]

theorem realpart_pos (B z : ℂ) (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    0 < (z+B).re := by
  change -(1/2 : ℝ) < z.re at hz
  simp only [Complex.add_re]
  linarith

theorem denominator_nonzero (B z : ℂ) (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    z+B ≠ 0 := by
  have hp := realpart_pos B z hB hz
  intro h
  simp [h] at hp

theorem inverse_bound (B z : ℂ) (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    ‖(z+B)⁻¹‖ ≤ 2 * B.re⁻¹ := by
  have hb : 0 < B.re := by linarith
  have hd : B.re/2 ≤ ‖z+B‖ := by
    have hr := Complex.re_le_norm (z+B)
    change -(1/2 : ℝ) < z.re at hz
    simp only [Complex.add_re] at hr
    linarith
  rw [norm_inv]
  calc
    ‖z+B‖⁻¹ ≤ (B.re/2)⁻¹ :=
      (inv_le_inv₀ (lt_of_lt_of_le (by positivity : 0 < B.re/2) hd) (by positivity)).2 hd
    _ = 2 * B.re⁻¹ := by field_simp

theorem inverse_power_bound (B z : ℂ) (r : ℕ)
    (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    ‖((z+B)⁻¹)^(r+1)‖ ≤ 2^(r+1) * B.re⁻¹ := by
  have hb : 0 ≤ B.re⁻¹ := inv_nonneg.mpr (by linarith)
  have hle : B.re⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).2 hB
  have hp : (B.re⁻¹)^r ≤ 1 := pow_le_one₀ hb hle
  rw [norm_pow]
  calc
    ‖(z+B)⁻¹‖^(r+1) ≤ (2*B.re⁻¹)^(r+1) :=
      pow_le_pow_left₀ (norm_nonneg _) (inverse_bound B z hB hz) _
    _ = 2^(r+1) * ((B.re⁻¹)^r * B.re⁻¹) := by rw [mul_pow, pow_succ (B.re⁻¹)]
    _ ≤ 2^(r+1) * B.re⁻¹ := mul_le_mul_of_nonneg_left
      (by simpa using mul_le_mul_of_nonneg_right hp hb) (by positivity)

theorem pole_power_summable (B : ι → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    Summable (fun i => ((z+B i)⁻¹)^(r+1)) := by
  exact (hs.mul_left (2^(r+1))).of_norm_bounded
    (fun i => inverse_power_bound (B i) z r (hB i) hz)

theorem log_atom_derivative (B z : ℂ) (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    HasDerivAt (fun w => Complex.log (w+B) - Complex.log B) ((z+B)⁻¹) z := by
  have hd := (Complex.hasDerivAt_log (by
    exact Or.inl (realpart_pos B z hB hz))).comp z ((hasDerivAt_id z).add_const B)
  simpa using hd.sub_const (Complex.log B)

theorem log_series_derivative (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    HasDerivAt (fun w => ∑' i, (Complex.log (w+B i) - Complex.log (B i)))
      (∑' i, (z+B i)⁻¹) z := by
  apply hasDerivAt_tsum_of_isPreconnected (hs.mul_left 2)
    domain_open domain_convex.isPreconnected
    (fun i w hw => log_atom_derivative (B i) w (hB i) hw)
    (fun i w hw => inverse_bound (B i) w (hB i) hw) zero_mem
  · simp
  · exact hz

theorem log_series_summable (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    Summable (fun i => Complex.log (z+B i) - Complex.log (B i)) := by
  apply summable_of_summable_hasDerivAt_of_isPreconnected (hs.mul_left 2)
    domain_open domain_convex.isPreconnected
    (fun i w hw => log_atom_derivative (B i) w (hB i) hw)
    (fun i w hw => inverse_bound (B i) w (hB i) hw) zero_mem
  · simp
  · exact hz

theorem canonical_product_hasProd (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    HasProd (fun i => 1+z/B i)
      (Complex.exp (∑' i, (Complex.log (z+B i) - Complex.log (B i)))) := by
  have hsum := (log_series_summable B hB hs z hz).hasSum
  have ht := (Complex.continuous_exp.tendsto _).comp hsum
  have hterm : ∀ i, Complex.exp (Complex.log (z+B i) - Complex.log (B i)) = 1+z/B i := by
    intro i
    have hb : B i ≠ 0 := by
      have := hB i
      intro he
      norm_num [he] at this
    rw [Complex.exp_sub, Complex.exp_log (denominator_nonzero _ _ (hB i) hz),
      Complex.exp_log hb]
    field_simp
    ring
  simpa only [HasProd, Function.comp_def, Complex.exp_sum, hterm] using ht

theorem canonical_product_eq_exp (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    (∏' i, (1+z/B i)) =
      Complex.exp (∑' i, (Complex.log (z+B i) - Complex.log (B i))) :=
  (canonical_product_hasProd B hB hs z hz).tprod_eq

theorem canonical_product_derivative (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    HasDerivAt (fun w => ∏' i, (1+w/B i))
      ((∏' i, (1+z/B i)) * ∑' i, (z+B i)⁻¹) z := by
  have hd := (Complex.hasDerivAt_exp _).comp z (log_series_derivative B hB hs z hz)
  rw [← canonical_product_eq_exp B hB hs z hz] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [domain_open.mem_nhds hz] with w hw
  exact canonical_product_eq_exp B hB hs w hw

theorem pole_atom_derivative (B z : ℂ) (r : ℕ)
    (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    HasDerivAt (fun w => ((w+B)⁻¹)^(r+1))
      (-((r+1 : ℕ) : ℂ) * ((z+B)⁻¹)^(r+2)) z := by
  have hd := (((hasDerivAt_id z).add_const B).inv
    (denominator_nonzero B z hB hz)).pow (r+1)
  convert! hd using 1 <;>
    simp [Nat.add_sub_cancel, one_div, div_eq_mul_inv, inv_pow, pow_succ] <;> ring

theorem pole_series_derivative (B : ι → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    HasDerivAt (fun w => ∑' i, ((w+B i)⁻¹)^(r+1))
      (-((r+1 : ℕ) : ℂ) * ∑' i, ((z+B i)⁻¹)^(r+2)) z := by
  have hbound : ∀ i w, w ∈ domain →
      ‖-((r+1 : ℕ) : ℂ) * ((w+B i)⁻¹)^(r+2)‖ ≤
        ((r+1 : ℕ) : ℝ) * 2^(r+2) * (B i).re⁻¹ := by
    intro i w hw
    rw [norm_mul, norm_neg, Complex.norm_natCast]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (inverse_power_bound (B i) w (r+1) (hB i) hw) (Nat.cast_nonneg _)
  have hd := hasDerivAt_tsum_of_isPreconnected
    (hs.mul_left (((r+1 : ℕ) : ℝ)*2^(r+2))) domain_open domain_convex.isPreconnected
    (fun i w hw => pole_atom_derivative (B i) w r (hB i) hw) hbound
    zero_mem (pole_power_summable B r hB hs 0 zero_mem) hz
  simpa only [tsum_mul_left] using hd

theorem log_series_iteratedDeriv (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (r : ℕ) (z : ℂ) (hz : z ∈ domain) :
    iteratedDeriv (r+1) (fun w => ∑' i,
      (Complex.log (w+B i) - Complex.log (B i))) z =
      (-1 : ℂ)^r * (r.factorial : ℂ) * ∑' i, ((z+B i)⁻¹)^(r+1) := by
  induction r generalizing z with
  | zero =>
    simpa using (log_series_derivative B hB hs z hz).deriv
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (r+1) (fun w => ∑' i,
        (Complex.log (w+B i) - Complex.log (B i))) =ᶠ[𝓝 z]
        (fun w => (-1 : ℂ)^r * (r.factorial : ℂ) * ∑' i, ((w+B i)⁻¹)^(r+1)) := by
      filter_upwards [domain_open.mem_nhds hz] with w hw
      exact ih w hw
    rw [he.deriv_eq]
    rw [((pole_series_derivative B r hB hs z hz).const_mul
      ((-1 : ℂ)^r * (r.factorial : ℂ))).deriv]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

end HadamardSeries


open MeasureTheory Set Filter Topology
noncomputable section
namespace LaplaceBridge

theorem real_gamma_nat (r : ℕ) (a : ℝ) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, t^r * Real.exp (-(a*t))) =
      (r.factorial : ℝ) * (a⁻¹)^(r+1) := by
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((r+1 : ℕ) : ℝ)) (r := a) (by positivity) ha
  rw [show ((r+1 : ℕ) : ℝ)-1 = (r : ℝ) by push_cast; ring] at hg
  simp only [Real.rpow_natCast] at hg
  rw [show Real.Gamma ((r+1 : ℕ) : ℝ) = (r.factorial : ℝ) by
      simpa using Real.Gamma_nat_eq_factorial r] at hg
  simpa only [one_div, mul_comm] using hg

theorem real_weight_integrable (r : ℕ) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t^r * Real.exp (-(a*t))) (Ioi 0) := by
  by_contra h
  have hv := real_gamma_nat r a ha
  rw [integral_undef h] at hv
  have hp : 0 < (r.factorial : ℝ) * (a⁻¹)^(r+1) := by positivity
  linarith

theorem complex_weight_integrable (r : ℕ) (a : ℂ) (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^r * Complex.exp (-(a*t))) (Ioi 0) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  apply (real_weight_integrable r a.re ha).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp [Complex.norm_exp, Complex.mul_re, abs_of_pos (mem_Ioi.mp ht)]

theorem integral_complex_weight_norm (r : ℕ) (a : ℂ) (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, ‖(t : ℂ)^r * Complex.exp (-(a*t))‖) =
      (r.factorial : ℝ) * (a.re⁻¹)^(r+1) := by
  rw [← real_gamma_nat r a.re ha]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp [Complex.norm_exp, Complex.mul_re, abs_of_pos (mem_Ioi.mp ht)]

theorem complex_weight_tendsto_zero (r : ℕ) (a : ℂ) (ha : 0 < a.re) :
    Tendsto (fun t : ℝ => (t : ℂ)^r * Complex.exp (-(a*t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (r : ℝ) a.re ha
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp [Real.rpow_natCast, Complex.norm_exp, Complex.mul_re, abs_of_pos ht]

theorem complex_weight_derivative (r : ℕ) (a : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)^(r+1)*Complex.exp (-(a*t)))
      (((r+1 : ℕ) : ℂ)*((t : ℂ)^r*Complex.exp (-(a*t))) -
        a*((t : ℂ)^(r+1)*Complex.exp (-(a*t)))) t := by
  have hp := (hasDerivAt_id (t : ℂ)).pow (r+1)
  have he := (Complex.hasDerivAt_exp _).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_mul (-a))
  have hd := (hp.mul he).comp_ofReal
  convert! hd using 1 <;> simp [neg_mul, pow_succ] <;> ring

theorem complex_gamma_nat (r : ℕ) (a : ℂ) (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ)^r*Complex.exp (-(a*t))) =
      (r.factorial : ℂ) * (a⁻¹)^(r+1) := by
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha
  induction r with
  | zero =>
    simpa [neg_mul] using integral_exp_mul_complex_Ioi (a := -a) (by simpa) 0
  | succ r ih =>
    have hi := (complex_weight_integrable r a ha).const_mul (((r+1 : ℕ) : ℂ))
    have hj := (complex_weight_integrable (r+1) a ha).const_mul a
    have hf := integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun t (_ : t ∈ Ici (0 : ℝ)) => complex_weight_derivative r a t)
      (hi.sub hj) (complex_weight_tendsto_zero (r+1) a ha)
    rw [integral_sub hi hj, integral_const_mul, integral_const_mul] at hf
    simp only [Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero r), zero_mul,
      sub_zero] at hf
    apply (mul_left_cancel₀ ha0)
    calc
      a * (∫ t : ℝ in Ioi 0, (t : ℂ)^(r+1)*Complex.exp (-(a*t))) =
          ((r+1 : ℕ) : ℂ) * (∫ t : ℝ in Ioi 0, (t : ℂ)^r*Complex.exp (-(a*t))) :=
        (sub_eq_zero.mp hf).symm
      _ = a * ((↑(r+1).factorial : ℂ) * a⁻¹^((r+1)+1)) := by
        rw [ih, Nat.factorial_succ]
        push_cast
        simp only [pow_succ]
        field_simp

theorem weighted_norm_integrals_summable (B : ι → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun i => ∫ t : ℝ in Ioi 0,
      ‖(t : ℂ)^r * Complex.exp (-(((x : ℂ)+B i)*t))‖) := by
  have hpos : ∀ i, 0 < ((x : ℂ)+B i).re := by
    intro i
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hB i]
  simp_rw [integral_complex_weight_norm r _ (hpos _)]
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (inv_nonneg.mpr (hpos i).le) _)) _ (hs.mul_left (r.factorial : ℝ))
  intro i
  have hb : 0 < (B i).re := by linarith [hB i]
  have ha : 0 < x+(B i).re := by linarith
  have hi : (x+(B i).re)⁻¹ ≤ (B i).re⁻¹ := (inv_le_inv₀ ha hb).2 (by linarith)
  have hi1 : (x+(B i).re)⁻¹ ≤ 1 := (inv_le_one₀ ha).2 (by linarith [hB i])
  have hip : 0 ≤ (x+(B i).re)⁻¹ := by positivity
  have hp : ((x+(B i).re)⁻¹)^(r+1) ≤ (B i).re⁻¹ := by
    rw [pow_succ]
    have hh : ((x+(B i).re)⁻¹)^r * (x+(B i).re)⁻¹ ≤ (x+(B i).re)⁻¹ := by
      simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hip hi1 :
        ((x+(B i).re)⁻¹)^r ≤ 1) hip
    exact hh.trans hi
  simpa only [Complex.add_re, Complex.ofReal_re] using
    mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg r.factorial)

theorem laplace_series_identity (B : ι → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x : ℝ) (hx : 0 ≤ x) :
    (∫ t : ℝ in Ioi 0, ∑' i,
      (t : ℂ)^r * Complex.exp (-(((x : ℂ)+B i)*t))) =
      (r.factorial : ℂ) * ∑' i, (((x : ℂ)+B i)⁻¹)^(r+1) := by
  have hpos : ∀ i, 0 < ((x : ℂ)+B i).re := by
    intro i
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hB i]
  rw [← integral_tsum_of_summable_integral_norm
    (fun i => complex_weight_integrable r _ (hpos i))
    (weighted_norm_integrals_summable B r hB hs x hx)]
  simp_rw [complex_gamma_nat r _ (hpos _)]
  exact tsum_mul_left

theorem laplace_series_integrable (B : ι → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x : ℝ) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => ∑' i,
      (t : ℂ)^r * Complex.exp (-(((x : ℂ)+B i)*t))) (Ioi 0) := by
  let F : ι → ℝ → ℂ := fun i t => (t : ℂ)^r * Complex.exp (-(((x : ℂ)+B i)*t))
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hi : ∀ i, Integrable (F i) μ := by
    intro i
    apply complex_weight_integrable
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hB i]
  have hsum : Summable (fun i => ∫ t, ‖F i t‖ ∂μ) :=
    weighted_norm_integrals_summable B r hB hs x hx
  have he (i : ι) : ∫⁻ t, ‖F i t‖ₑ ∂μ = ‖∫ t, ‖F i t‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hi i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg (F i t)))]
    simp only [coe_nnnorm]
  have hfin : (∑' i, ∫⁻ t, ‖F i t‖ₑ ∂μ) < ⊤ := by
    simp_rw [he]
    exact (ENNReal.tsum_coe_ne_top_iff_summable.2
      (NNReal.summable_coe.1 hsum.abs)).lt_top
  change Integrable (fun t => ∑' i, F i t) μ
  refine ⟨?_, ?_⟩
  · apply Measurable.aestronglyMeasurable
    exact Measurable.tsum (fun i => by dsimp [F]; fun_prop)
  · rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ t, ‖∑' i, F i t‖ₑ ∂μ) ≤ ∫⁻ t, ∑' i, ‖F i t‖ₑ ∂μ :=
        lintegral_mono (fun t => enorm_tsum_le_tsum_enorm)
      _ = ∑' i, ∫⁻ t, ‖F i t‖ₑ ∂μ := lintegral_tsum (fun i => (hi i).1.enorm)
      _ < ⊤ := hfin

theorem heat_series_summable (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (t : ℝ) (ht : 0 < t) : Summable (fun i => Complex.exp (-(B i*t))) := by
  apply (hs.mul_left t⁻¹).of_norm_bounded
  intro i
  have hb : 0 < (B i).re := by linarith [hB i]
  have hp : 0 < (B i).re*t := mul_pos hb ht
  have hle : (B i).re*t ≤ Real.exp ((B i).re*t) := by
    linarith [Real.add_one_le_exp ((B i).re*t)]
  simp only [Complex.norm_exp, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [Real.exp_neg]
  calc
    (Real.exp ((B i).re*t))⁻¹ ≤ ((B i).re*t)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) hp).2 hle
    _ = t⁻¹ * (B i).re⁻¹ := by rw [mul_inv_rev]

theorem real_heat_integrand_eq (B : ι → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x t : ℝ) (ht : 0 < t) :
    (∑' i, (t : ℂ)^r * Complex.exp (-(((x : ℂ)+B i)*t))).re =
      t^r * Real.exp (-(x*t)) * ∑' i, (Complex.exp (-(B i*t))).re := by
  have he (i : ι) : (t : ℂ)^r * Complex.exp (-(((x : ℂ)+B i)*t)) =
      ((t : ℂ)^r * Complex.exp (-((x : ℂ)*t))) * Complex.exp (-(B i*t)) := by
    rw [show -(((x : ℂ)+B i)*t) = -((x : ℂ)*t) + -(B i*t) by ring,
      Complex.exp_add]
    ring
  simp_rw [he]
  rw [tsum_mul_left]
  have hc : ((t : ℂ)^r * Complex.exp (-((x : ℂ)*t))) =
      ((t^r * Real.exp (-(x*t)) : ℝ) : ℂ) := by
    norm_cast
  rw [hc, Complex.re_ofReal_mul]
  congr 1
  exact Complex.reCLM.map_tsum (heat_series_summable B hB hs t ht)

theorem real_heat_integral_identity (B : ι → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x : ℝ) (hx : 0 ≤ x) :
    (∫ t : ℝ in Ioi 0, t^r * Real.exp (-(x*t)) *
      ∑' i, (Complex.exp (-(B i*t))).re) =
      ((r.factorial : ℂ) * ∑' i, (((x : ℂ)+B i)⁻¹)^(r+1)).re := by
  rw [← laplace_series_identity B r hB hs x hx]
  have hr := integral_re (laplace_series_integrable B r hB hs x hx)
  simp only [RCLike.re_to_complex] at hr
  rw [← hr]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (real_heat_integrand_eq B r hB hs x t (mem_Ioi.mp ht)).symm

theorem real_heat_integrable (B : ι → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x : ℝ) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => t^r * Real.exp (-(x*t)) *
      ∑' i, (Complex.exp (-(B i*t))).re) (Ioi 0) := by
  apply (laplace_series_integrable B r hB hs x hx).re.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact real_heat_integrand_eq B r hB hs x t (mem_Ioi.mp ht)

end LaplaceBridge

namespace CanonicalQBridge

theorem real_log_iteratedDeriv (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (r : ℕ) (x : ℝ) (hx : -(1/2 : ℝ) < x) :
    iteratedDeriv (r+1) (fun v : ℝ => (∑' i,
      (Complex.log ((v : ℂ)+B i) - Complex.log (B i))).re) x =
      ((-1 : ℂ)^r * (r.factorial : ℂ) * ∑' i, (((x : ℂ)+B i)⁻¹)^(r+1)).re := by
  have hz : (x : ℂ) ∈ HadamardSeries.domain := hx
  induction r generalizing x with
  | zero =>
    have hd := (HadamardSeries.log_series_derivative B hB hs (x : ℂ) hz).comp_ofReal
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
    simpa [Function.comp_def] using hr.deriv
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (r+1) (fun v : ℝ => (∑' i,
        (Complex.log ((v : ℂ)+B i) - Complex.log (B i))).re) =ᶠ[𝓝 x]
        (fun v : ℝ => ((-1 : ℂ)^r*(r.factorial : ℂ)*
          ∑' i, (((v : ℂ)+B i)⁻¹)^(r+1)).re) := by
      filter_upwards [Ioi_mem_nhds hx] with v hv
      exact ih v hv hv
    rw [he.deriv_eq]
    have hd := ((HadamardSeries.pole_series_derivative B r hB hs (x : ℂ) hz).const_mul
      ((-1 : ℂ)^r*(r.factorial : ℂ))).comp_ofReal
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
    have hh := hr.deriv
    change deriv (fun v : ℝ => ((-1 : ℂ)^r*(r.factorial : ℂ)*
      ∑' i, (((v : ℂ)+B i)⁻¹)^(r+1)).re) x = _ at hh
    rw [hh]
    change (_ : ℂ).re = (_ : ℂ).re
    congr 1
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

theorem derivative_equals_heat_integral (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (r : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (-1 : ℝ)^r * iteratedDeriv (r+1) (fun v : ℝ => (∑' i,
      (Complex.log ((v : ℂ)+B i) - Complex.log (B i))).re) x =
    ∫ t : ℝ in Ioi 0, t^r * Real.exp (-(x*t)) *
      ∑' i, (Complex.exp (-(B i*t))).re := by
  rw [real_log_iteratedDeriv B hB hs r x (by linarith),
    LaplaceBridge.real_heat_integral_identity B r hB hs x hx]
  have hc : (-1 : ℂ)^r*(r.factorial : ℂ) =
      (((-1 : ℝ)^r*(r.factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.re_ofReal_mul]
  rw [show (r.factorial : ℂ) = ((r.factorial : ℝ) : ℂ) by norm_cast,
    Complex.re_ofReal_mul]
  have hsign : (-1 : ℝ)^r * (-1 : ℝ)^r = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℝ)^r * (-1 : ℝ)^r) *
      ((r.factorial : ℝ) * (∑' i, (((x : ℂ)+B i)⁻¹)^(r+1)).re) := by ring
    _ = _ := by rw [hsign, one_mul]

theorem normalized_Q_integral (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (r : ℕ) (u : ℝ) (hu : 0 < u) :
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*(-1 : ℝ)^r *
      iteratedDeriv (r+1) (fun v : ℝ => (∑' i,
        (Complex.log ((v : ℂ)+B i) - Complex.log (B i))).re) (u^2) =
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1) *
      ∫ t : ℝ in Ioi 0, t^r * Real.exp (-(u^2*t)) *
        ∑' i, (Complex.exp (-(B i*t))).re := by
  rw [mul_assoc ((2 : ℝ)^(r+1)*u^(2*(r+1)-1)),
    derivative_equals_heat_integral B hB hs r (u^2) (sq_nonneg u)]

theorem positive_function_log_identity (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (g : ℝ → ℝ) (c x : ℝ) (hc : 0 < c) (hx : 0 < x) (hg : 0 < g x)
    (hp : (((g x/c : ℝ) : ℂ)) = ∏' i, (1+(x : ℂ)/B i)) :
    Real.log (g x) - Real.log c =
      (∑' i, (Complex.log ((x : ℂ)+B i) - Complex.log (B i))).re := by
  have hz : (x : ℂ) ∈ HadamardSeries.domain := by
    change -(1/2 : ℝ) < x
    linarith
  rw [HadamardSeries.canonical_product_eq_exp B hB hs (x : ℂ) hz] at hp
  have hn := congrArg (fun z : ℂ => Real.log ‖z‖) hp
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hg hc), abs_of_pos hg, abs_of_pos hc,
    Complex.norm_exp, Real.log_exp, Real.log_div (ne_of_gt hg) (ne_of_gt hc)] using hn

theorem original_log_Q_from_product (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (g : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hg : ∀ x > 0, 0 < g x)
    (hp : ∀ x > 0, (((g x/c : ℝ) : ℂ)) = ∏' i, (1+(x : ℂ)/B i))
    (r : ℕ) (u : ℝ) (hu : 0 < u) :
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*(-1 : ℝ)^r *
      iteratedDeriv (r+1) (fun x => Real.log (g x) - Real.log c) (u^2) =
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1) *
      ∫ t : ℝ in Ioi 0, t^r * Real.exp (-(u^2*t)) *
        ∑' i, (Complex.exp (-(B i*t))).re := by
  have he : (fun x => Real.log (g x) - Real.log c) =ᶠ[𝓝 (u^2)]
      (fun x : ℝ => (∑' i,
        (Complex.log ((x : ℂ)+B i) - Complex.log (B i))).re) := by
    filter_upwards [Ioi_mem_nhds (sq_pos_of_pos hu)] with x hx
    exact positive_function_log_identity B hB hs g c x hc hx (hg x hx) (hp x hx)
  rw [he.iteratedDeriv_eq (r+1)]
  exact normalized_Q_integral B hB hs r u hu

end CanonicalQBridge



noncomputable section
namespace BranchFull

def smallRatio (t : ℝ) : ℝ :=
  ((t⁻¹)^2 + t⁻¹) * Real.exp (-t⁻¹ + (10000 + 1/4)*t)
def largeRatio (t : ℝ) : ℝ :=
  (1000000 + t⁻¹) * Real.exp (-(1000000 - 10000 - 1/4)*t)

theorem exp_neg_quartic (y : ℝ) (hy : 0 < y) :
    Real.exp (-y) ≤ 24 / y^4 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 4
  norm_num at h
  rw [Real.exp_neg]
  rw [← one_div (Real.exp y)]
  apply (div_le_div_iff₀ (Real.exp_pos y) (pow_pos hy 4)).2
  nlinarith

theorem small_ratio_y (y : ℝ) (hy : 10000 ≤ y) :
    (y^2+y) * Real.exp (-y+(10000+1/4)/y) < 1/2 := by
  have hp : 0 < y := by linarith
  have he : -y+(10000+1/4)/y ≤ -(y/2) := by
    have hd : (10000+1/4)/y ≤ y/2 := by
      apply (div_le_iff₀ hp).2
      nlinarith
    linarith
  have hb := Real.exp_le_exp.mpr he
  have hq := exp_neg_quartic (y/2) (by positivity)
  have hm : (y^2+y)*Real.exp (-y+(10000+1/4)/y) ≤
      (y^2+y)*(24/(y/2)^4) :=
    mul_le_mul_of_nonneg_left (hb.trans hq) (by positivity)
  have hid : (y^2+y)*(24/(y/2)^4) = 384*(1/y^2+1/y^3) := by
    field_simp
    <;> ring
  rw [hid] at hm
  have h2 : (1:ℝ)/y^2 ≤ 1/10000^2 := by gcongr
  have h3 : (1:ℝ)/y^3 ≤ 1/10000^3 := by gcongr
  linarith

theorem small_ratio_lt_half (t : ℝ) (ht : 0 < t) (hc : t ≤ 1/10000) :
    smallRatio t < 1/2 := by
  have hi : (10000:ℝ) ≤ t⁻¹ := by
    rw [← one_div t]
    apply (le_div_iff₀ ht).2
    linarith
  have h := small_ratio_y (t⁻¹) hi
  simpa [smallRatio, div_eq_mul_inv] using h

theorem large_ratio_lt_half (t : ℝ) (ht : 1/10000 ≤ t) :
    largeRatio t < 1/2 := by
  have hp : 0 < t := by linarith
  have hi : t⁻¹ ≤ (10000:ℝ) := by
    rw [← one_div t]
    apply (div_le_iff₀ hp).2
    linarith
  have he : -(1000000-10000-1/4)*t ≤ (-98:ℝ) := by linarith
  have hExp := (Real.exp_le_exp.mpr he).trans (exp_neg_quartic 98 (by norm_num))
  have hm : largeRatio t ≤ 1010000*(24/98^4) := by
    unfold largeRatio
    exact mul_le_mul (by linarith) hExp (Real.exp_pos _).le (by norm_num)
  norm_num at hm ⊢
  linarith

theorem heat_lower_bound (K : ℝ → ℝ)
    (hs : ∀ t > 0, t ≤ 1/10000 →
      Real.exp (-10000*t)*(1-smallRatio t) ≤ K t)
    (hl : ∀ t > 0, 1/10000 ≤ t →
      Real.exp (-10000*t)*(1-largeRatio t) ≤ K t) :
    ∀ t > 0, (1/2)*Real.exp (-10000*t) < K t := by
  intro t ht
  have hp := Real.exp_pos (-10000*t)
  by_cases h : t ≤ 1/10000
  · have hr := small_ratio_lt_half t ht h
    have hk := hs t ht h
    nlinarith
  · have hr := large_ratio_lt_half t (le_of_lt (lt_of_not_ge h))
    have hk := hl t ht (le_of_lt (lt_of_not_ge h))
    nlinarith
end BranchFull

open MeasureTheory Set
noncomputable section
namespace QnAudit

def weight (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (n - 1) * Real.exp (-x * t)

def moment (K : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), weight x n t * K t

def oldQ (K : ℝ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * u ^ (2 * n - 1) * moment K (u ^ 2) n

def newQ (K : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (Nat.factorial (n - 1) : ℝ) * moment K x n

theorem weight_pos (x : ℝ) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    0 < weight x n t := by
  exact mul_pos (pow_pos ht _) (Real.exp_pos _)

theorem positive_integral_Ioi (f : ℝ → ℝ)
    (hf : ∀ t > 0, 0 < f t)
    (hi : IntegrableOn f (Ioi 0)) :
    0 < ∫ t in Ioi (0 : ℝ), f t := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact le_of_lt (hf t ht)
  apply (integral_pos_iff_support_of_nonneg_ae hnonneg hi).2
  have hsub : Ioc (0 : ℝ) 1 ⊆ Function.support f := by
    intro t ht
    exact ne_of_gt (hf t ht.1)
  have hmeasure : (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 1) = 1 := by
    rw [Measure.restrict_apply measurableSet_Ioc]
    have hinter : Ioc (0 : ℝ) 1 ∩ Ioi 0 = Ioc 0 1 :=
      inter_eq_left.mpr (fun _ ht => ht.1)
    rw [hinter, Real.volume_Ioc]
    norm_num
  calc
    0 < (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 1) := by rw [hmeasure]; norm_num
    _ ≤ (volume.restrict (Ioi (0 : ℝ))) (Function.support f) := measure_mono hsub

theorem moment_pos (K : ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hK : ∀ t > 0, 0 < K t)
    (hi : IntegrableOn (fun t => weight x n t * K t) (Ioi 0)) :
    0 < moment K x n := by
  exact positive_integral_Ioi _ (fun t ht => mul_pos (weight_pos x n t ht) (hK t ht)) hi

theorem oldQ_pos (K : ℝ → ℝ) (u : ℝ) (n : ℕ)
    (hu : 0 < u) (hK : ∀ t > 0, 0 < K t)
    (hi : IntegrableOn (fun t => weight (u ^ 2) n t * K t) (Ioi 0)) :
    0 < oldQ K u n := by
  exact mul_pos (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _) (pow_pos hu _))
    (moment_pos K (u ^ 2) n hK hi)

theorem newQ_pos (K : ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hK : ∀ t > 0, 0 < K t)
    (hi : IntegrableOn (fun t => weight x n t * K t) (Ioi 0)) :
    0 < newQ K x n := by
  have hfac : (0 : ℝ) < (Nat.factorial (n - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n - 1)
  exact mul_pos (div_pos (pow_pos hx _) hfac) (moment_pos K x n hK hi)

theorem positive_head_controls_signed_tail (H N E r : ℝ)
    (hH : 0 < H) (hN : 0 ≤ N) (hr : r < 1) (hE : |E| ≤ r * H) :
    0 < H + N + E := by
  have he := neg_abs_le E
  have hm : r * H < H := by nlinarith
  linarith

theorem heat_pos_from_two_regimes (K H N E r : ℝ → ℝ) (t0 : ℝ)
    (hsplit : ∀ t > 0, K t = H t + N t + E t)
    (hH : ∀ t > 0, 0 < H t) (hN : ∀ t > 0, 0 ≤ N t)
    (hE : ∀ t > 0, |E t| ≤ r t * H t)
    (hsmall : ∀ t > 0, t ≤ t0 → r t < 1)
    (hlarge : ∀ t > 0, t0 < t → r t < 1) :
    ∀ t > 0, 0 < K t := by
  intro t ht
  rw [hsplit t ht]
  apply positive_head_controls_signed_tail _ _ _ _ (hH t ht) (hN t ht)
  · by_cases h : t ≤ t0
    · exact hsmall t ht h
    · exact hlarge t ht (lt_of_not_ge h)
  · exact hE t ht

theorem ordinary_Q_positive_from_heat_representation
    (Q : ℕ → ℝ → ℝ) (K : ℝ → ℝ)
    (hrep : ∀ n ≥ 1, ∀ u > 0, Q n u = oldQ K u n)
    (hK : ∀ t > 0, 0 < K t)
    (hint : ∀ n ≥ 1, ∀ u > 0,
      IntegrableOn (fun t => weight (u ^ 2) n t * K t) (Ioi 0)) :
    ∀ n ≥ 1, ∀ u > 0, 0 < Q n u := by
  intro n hn u hu
  rw [hrep n hn u hu]
  exact oldQ_pos K u n hu hK (hint n hn u hu)

end QnAudit

namespace BranchSpectral
open Set

def atom (g e t : ℝ) := Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)
def gaussian (g t : ℝ) := Real.exp (-g^2*t)
def kernel (g e : ι → ℝ) (t : ℝ) := ∑' j, atom (g j) (e j) t

theorem atom_abs_bound (g e t : ℝ) (he : |e| ≤ 1/2) (ht : 0 < t) :
    |atom g e t| ≤ Real.exp (t/4)*gaussian g t := by
  have he2 : e^2 ≤ 1/4 := by
    obtain ⟨h1,h2⟩ := abs_le.mp he
    nlinarith
  unfold atom gaussian
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(g^2-e^2)*t)*1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ ≤ Real.exp (t/4)*Real.exp (-g^2*t) := by
      rw [mul_one, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith

theorem kernel_summable (g e : ι → ℝ) (t : ℝ)
    (he : ∀ j, |e j| ≤ 1/2) (ht : 0 < t)
    (hg : Summable (fun j => gaussian (g j) t)) :
    Summable (fun j => atom (g j) (e j) t) := by
  apply (hg.mul_left (Real.exp (t/4))).of_norm_bounded
  intro j
  simpa only [Real.norm_eq_abs] using atom_abs_bound (g j) (e j) t (he j) ht

theorem atom_near_nonneg (g e t : ℝ) (hg : 0 < g)
    (he : |e| ≤ 1/2) (ht : 0 < t) (hnear : g ≤ t⁻¹) :
    0 ≤ atom g e t := by
  have hgt : g*t ≤ 1 := by
    rw [← one_div t] at hnear
    exact (le_div_iff₀ ht).mp hnear
  have hab : |2*e*g*t| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos ht, abs_of_pos hg]
    norm_num
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-2*|e|) (le_of_lt (mul_pos hg ht))]
  apply mul_nonneg (Real.exp_pos _).le
  apply Real.cos_nonneg_of_mem_Icc
  have hp := Real.pi_gt_three
  have hb := abs_le.mp hab
  constructor <;> linarith

theorem critical_atom_nonneg (g t : ℝ) : 0 ≤ atom g 0 t := by
  simp only [atom, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_zero, zero_mul,
    Real.cos_zero, mul_one]
  exact (Real.exp_pos _).le

theorem anchor_bound (g t : ℝ) (hg : 0 < g) (h100 : g ≤ 100) (ht : 0 < t) :
    Real.exp (-10000*t) ≤ atom g 0 t := by
  simp only [atom, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_zero, zero_mul,
    Real.cos_zero, mul_one]
  apply Real.exp_le_exp.mpr
  have hs : g^2 ≤ 10000 := by nlinarith
  nlinarith

-- A generic infinite-sum lemma: no positivity of the total is assumed.
theorem head_tail_sum_bound (f G : ι → ℝ) (j0 : ι) (H C L : ℝ)
    (hf : Summable f) (hG : Summable G) (hC : 0 ≤ C)
    (hhead : H ≤ f j0) (hzero : G j0 = 0)
    (hpoint : ∀ j, j ≠ j0 → -C*G j ≤ f j)
    (htail : (∑' j, G j) ≤ L) :
    H-C*L ≤ ∑' j, f j := by
  classical
  let head : ι → ℝ := fun j => if j = j0 then H else 0
  have hh : Summable head := summable_of_ne_finset_zero (s := {j0}) (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [head,hj])
  have hdom : ∀ j, head j-C*G j ≤ f j := by
    intro j
    by_cases h : j = j0
    · subst j
      simpa [head,hzero] using hhead
    · simpa [head,h] using hpoint j h
  have hi := (hh.sub (hG.mul_left C)).tsum_le_tsum hdom hf
  rw [hh.tsum_sub (hG.mul_left C), tsum_mul_left] at hi
  have hs : (∑' j, head j) = H := by simp [head]
  rw [hs] at hi
  nlinarith

structure SpectralInput where
  gamma : ι → ℝ
  eps : ι → ℝ
  gamma_pos : ∀ j, 0 < gamma j
  strip : ∀ j, |eps j| ≤ 1/2
  verified : ∀ j, gamma j ≤ 1000 → eps j = 0
  anchor : ι
  anchor_low : gamma anchor ≤ 100
  gauss_sum : ∀ t > 0, Summable (fun j => gaussian (gamma j) t)
  gauss_tail : ∀ t > 0, ∀ L ≥ 10,
    (∑' j, if L < gamma j then gaussian (gamma j) t else 0) ≤
      (L^2+t⁻¹)*Real.exp (-L^2*t)

theorem spectral_head_tail (S : SpectralInput (ι := ι)) (t L : ℝ) (ht : 0 < t)
    (hL : 10 ≤ L) (ha : S.gamma S.anchor ≤ L)
    (hnear : ∀ j, S.gamma j ≤ L → 0 ≤ atom (S.gamma j) (S.eps j) t) :
    Real.exp (-10000*t) - Real.exp (t/4)*(L^2+t⁻¹)*Real.exp (-L^2*t) ≤
      kernel S.gamma S.eps t := by
  classical
  let G : ι → ℝ := fun j => if L < S.gamma j then gaussian (S.gamma j) t else 0
  have hGs : Summable G := (S.gauss_sum t ht).of_nonneg_of_le
    (by intro j; simp only [G]; split_ifs
        · exact (Real.exp_pos _).le
        · exact le_rfl)
    (by intro j; simp only [G]; split_ifs; exact le_rfl; exact (Real.exp_pos _).le)
  have he0 : S.eps S.anchor = 0 := S.verified _ (by linarith [S.anchor_low])
  have hz : G S.anchor = 0 := by simp [G, not_lt.mpr ha]
  have hhead : Real.exp (-10000*t) ≤ atom (S.gamma S.anchor) (S.eps S.anchor) t := by
    rw [he0]
    exact anchor_bound _ t (S.gamma_pos _) S.anchor_low ht
  have hpoint : ∀ j, j ≠ S.anchor →
      -Real.exp (t/4)*G j ≤ atom (S.gamma j) (S.eps j) t := by
    intro j hj
    by_cases h : L < S.gamma j
    · simp only [G, if_pos h]
      have hb := atom_abs_bound (S.gamma j) (S.eps j) t (S.strip j) ht
      have hn := neg_abs_le (atom (S.gamma j) (S.eps j) t)
      nlinarith
    · simp only [G, if_neg h, mul_zero]
      exact hnear j (le_of_not_gt h)
  have h := head_tail_sum_bound _ G S.anchor (Real.exp (-10000*t))
    (Real.exp (t/4)) ((L^2+t⁻¹)*Real.exp (-L^2*t))
    (kernel_summable S.gamma S.eps t S.strip ht (S.gauss_sum t ht)) hGs
    (Real.exp_pos _).le hhead hz hpoint (S.gauss_tail t ht L hL)
  simpa only [kernel, mul_assoc] using h
end BranchSpectral

namespace BranchSpectral
open BranchFull MeasureTheory Set

theorem spectral_small_bound (S : SpectralInput (ι := ι)) (t : ℝ) (ht : 0 < t)
    (hc : t ≤ 1/10000) :
    Real.exp (-10000*t)*(1-smallRatio t) ≤ kernel S.gamma S.eps t := by
  have hi : (10000:ℝ) ≤ t⁻¹ := by
    rw [← one_div t]
    apply (le_div_iff₀ ht).2
    linarith
  have h := spectral_head_tail S t t⁻¹ ht (by linarith)
    (le_trans S.anchor_low (by linarith))
    (fun j hj => atom_near_nonneg _ _ _ (S.gamma_pos j) (S.strip j) ht hj)
  have he : -10000*t + (-t⁻¹+(10000+1/4)*t) = t/4 + (-(t⁻¹)^2*t) := by
    field_simp
    <;> ring
  have heq : Real.exp (-10000*t)*smallRatio t =
      Real.exp (t/4)*((t⁻¹)^2+t⁻¹)*Real.exp (-(t⁻¹)^2*t) := by
    unfold smallRatio
    calc
      _ = ((t⁻¹)^2+t⁻¹)*(Real.exp (-10000*t)*Real.exp (-t⁻¹+(10000+1/4)*t)) := by ring
      _ = ((t⁻¹)^2+t⁻¹)*Real.exp (t/4+(-(t⁻¹)^2*t)) := by rw [← Real.exp_add, he]
      _ = _ := by rw [Real.exp_add]; ring
  rw [← heq] at h
  nlinarith

theorem spectral_large_bound (S : SpectralInput (ι := ι)) (t : ℝ) (ht : 0 < t) :
    Real.exp (-10000*t)*(1-largeRatio t) ≤ kernel S.gamma S.eps t := by
  have h := spectral_head_tail S t 1000 ht (by norm_num)
    (by linarith [S.anchor_low]) (by
      intro j hj
      rw [S.verified j hj]
      exact critical_atom_nonneg _ _)
  have he : -10000*t + (-(1000000-10000-1/4)*t) = t/4 + (-(1000:ℝ)^2*t) := by ring
  have heq : Real.exp (-10000*t)*largeRatio t =
      Real.exp (t/4)*((1000:ℝ)^2+t⁻¹)*Real.exp (-(1000:ℝ)^2*t) := by
    unfold largeRatio
    calc
      _ = (1000000+t⁻¹)*(Real.exp (-10000*t)*Real.exp (-(1000000-10000-1/4)*t)) := by ring
      _ = (1000000+t⁻¹)*Real.exp (t/4+(-(1000:ℝ)^2*t)) := by rw [← Real.exp_add, he]
      _ = _ := by rw [Real.exp_add]; ring
  rw [← heq] at h
  nlinarith

theorem spectral_kernel_lower_bound (S : SpectralInput (ι := ι)) :
    ∀ t > 0, (1/2)*Real.exp (-10000*t) < kernel S.gamma S.eps t := by
  exact heat_lower_bound _ (spectral_small_bound S)
    (fun t ht _ => spectral_large_bound S t ht)

theorem spectral_kernel_pos (S : SpectralInput (ι := ι)) :
    ∀ t > 0, 0 < kernel S.gamma S.eps t := by
  intro t ht
  have h := spectral_kernel_lower_bound S t ht
  have hpos := Real.exp_pos (-10000*t)
  linarith

-- Contracts to be proved for the actual xi-derived Q, not declarations of axioms.
structure BaseInput (S : SpectralInput (ι := ι)) where
  Q : ℕ → ℝ → ℝ
  representation : ∀ n ≥ 1, ∀ u > 0, Q n u = QnAudit.oldQ (kernel S.gamma S.eps) u n
  integrable : ∀ n ≥ 1, ∀ u > 0,
    IntegrableOn (fun t => QnAudit.weight (u^2) n t * kernel S.gamma S.eps t) (Ioi 0)

def NegativeSeed {S : SpectralInput (ι := ι)} (D : BaseInput S) : Prop :=
  ∃ n ≥ 1, ∃ u > 0, D.Q n u < 0

def OffLine (S : SpectralInput (ι := ι)) : Set ι := {j | S.eps j ≠ 0}

-- The analytic contradiction is uniform in the cardinality of OffLine.
theorem negative_seed_impossible (S : SpectralInput (ι := ι)) (D : BaseInput S) :
    ¬ NegativeSeed D := by
  rintro ⟨n, hn, u, hu, hneg⟩
  rw [D.representation n hn u hu] at hneg
  have hp := QnAudit.oldQ_pos (kernel S.gamma S.eps) u n hu
    (spectral_kernel_pos S) (D.integrable n hn u hu)
  exact (not_lt_of_ge hp.le) hneg

theorem branch2_finite (S : SpectralInput (ι := ι)) (D : BaseInput S) :
    ¬ (NegativeSeed D ∧ (OffLine S).Finite ∧ (OffLine S).Nonempty) := by
  intro h
  exact negative_seed_impossible S D h.1

theorem branch3_infinite (S : SpectralInput (ι := ι)) (D : BaseInput S) :
    ¬ (NegativeSeed D ∧ (OffLine S).Infinite) := by
  intro h
  exact negative_seed_impossible S D h.1

-- The logical closure requested by the project, independent of the analytic proof.
theorem nonnegative_via_branches (Q : ℕ → ℝ → ℝ) (off : Set ι)
    (hRH : off = ∅ → ∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u)
    (b2 : ¬ ((∃ n ≥ 1, ∃ u > 0, Q n u < 0) ∧ off.Finite ∧ off.Nonempty))
    (b3 : ¬ ((∃ n ≥ 1, ∃ u > 0, Q n u < 0) ∧ off.Infinite)) :
    ∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u := by
  classical
  intro n hn u hu
  by_contra h
  have hneg : Q n u < 0 := lt_of_not_ge h
  have seed : ∃ m ≥ 1, ∃ v > 0, Q m v < 0 := ⟨n,hn,u,hu,hneg⟩
  by_cases he : off = ∅
  · exact (not_lt_of_ge (hRH he n hn u hu)) hneg
  · have hne : off.Nonempty := Set.nonempty_iff_ne_empty.mpr he
    by_cases hf : off.Finite
    · exact b2 ⟨seed,hf,hne⟩
    · exact b3 ⟨seed,hf⟩

-- RH direction obtained solely from nonnegative critical atoms.
theorem critical_kernel_pos (S : SpectralInput (ι := ι)) (hoff : OffLine S = ∅)
    (t : ℝ) (ht : 0 < t) : 0 < kernel S.gamma S.eps t := by
  have he0 : ∀ j, S.eps j = 0 := by
    intro j
    by_contra hj
    have hm : j ∈ OffLine S := hj
    rw [hoff] at hm
    exact hm
  have hs := kernel_summable S.gamma S.eps t S.strip ht (S.gauss_sum t ht)
  have hhead : Real.exp (-10000*t) ≤ atom (S.gamma S.anchor) (S.eps S.anchor) t := by
    rw [he0]
    exact anchor_bound _ _ (S.gamma_pos _) S.anchor_low ht
  have h := head_tail_sum_bound (fun j => atom (S.gamma j) (S.eps j) t)
    (fun _ => 0) S.anchor (Real.exp (-10000*t)) 0 0 hs (by simp)
    (by norm_num) hhead rfl (by
      intro j _
      rw [he0]
      simpa using critical_atom_nonneg (S.gamma j) t) (by simp)
  have hh : Real.exp (-10000*t) ≤ kernel S.gamma S.eps t := by
    simpa [kernel] using h
  exact lt_of_lt_of_le (Real.exp_pos _) hh

theorem critical_implies_base_nonnegative (S : SpectralInput (ι := ι)) (D : BaseInput S)
    (hoff : OffLine S = ∅) : ∀ n ≥ 1, ∀ u > 0, 0 ≤ D.Q n u := by
  intro n hn u hu
  rw [D.representation n hn u hu]
  exact (QnAudit.oldQ_pos _ u n hu (critical_kernel_pos S hoff)
    (D.integrable n hn u hu)).le

theorem base_nonnegative_by_logical_chain (S : SpectralInput (ι := ι)) (D : BaseInput S) :
    ∀ n ≥ 1, ∀ u > 0, 0 ≤ D.Q n u := by
  exact nonnegative_via_branches D.Q (OffLine S) (critical_implies_base_nonnegative S D)
    (branch2_finite S D) (branch3_infinite S D)

-- A stronger consequence of the same analytic inputs; no RH premise.
theorem base_strict_positive (S : SpectralInput (ι := ι)) (D : BaseInput S) :
    ∀ n ≥ 1, ∀ u > 0, 0 < D.Q n u := by
  exact QnAudit.ordinary_Q_positive_from_heat_representation D.Q
    (kernel S.gamma S.eps) D.representation (spectral_kernel_pos S) D.integrable
end BranchSpectral


open Set Filter
noncomputable section

namespace CountedQBridge
open MeasureTheory Set Filter Topology

def pole (gamma eps : ℝ) : ℂ :=
  ((gamma^2-eps^2 : ℝ) : ℂ) - ((2*eps*gamma : ℝ) : ℂ)*Complex.I

theorem pole_re (gamma eps : ℝ) : (pole gamma eps).re = gamma^2-eps^2 := by
  simp only [pole, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]

theorem pole_im (gamma eps : ℝ) : (pole gamma eps).im = -(2*eps*gamma) := by
  simp only [pole, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_sub]

theorem pole_exp_real (gamma eps t : ℝ) :
    (Complex.exp (-(pole gamma eps*t))).re = BranchSpectral.atom gamma eps t := by
  rw [Complex.exp_re]
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero, pole_re, pole_im,
    neg_mul, neg_neg, zero_add]
  simp only [BranchSpectral.atom, neg_mul]

theorem pole_real_lower (gamma eps : ℝ) (hg : 2 ≤ gamma) (he : |eps| ≤ 1/2) :
    1 ≤ (pole gamma eps).re ∧ gamma^2/2 ≤ (pole gamma eps).re := by
  rw [pole_re]
  obtain ⟨h1,h2⟩ := abs_le.mp he
  have he2 : eps^2 ≤ 1/4 := by nlinarith
  constructor <;> nlinarith

theorem pole_inverse_summable (gamma eps : ι → ℝ)
    (hg : ∀ j, 2 ≤ gamma j) (he : ∀ j, |eps j| ≤ 1/2)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ j ∈ F, (gamma j)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p) :
    Summable (fun j => (pole (gamma j) (eps j)).re⁻¹) := by
  have hs := (ReciprocalCounting.summable_inverse_from_sublinear_count
    (fun j => (gamma j)^2) (fun j => by nlinarith [hg j]) C p hp hcount).1
  apply (hs.mul_left 2).of_nonneg_of_le
  · intro j
    exact inv_nonneg.mpr (le_trans (by norm_num) (pole_real_lower _ _ (hg j) (he j)).1)
  · intro j
    have hb := pole_real_lower _ _ (hg j) (he j)
    have hp1 : 0 < (pole (gamma j) (eps j)).re := by linarith
    have hg1 : 0 < (gamma j)^2/2 := by nlinarith [hg j]
    calc
      _ ≤ ((gamma j)^2/2)⁻¹ := (inv_le_inv₀ hp1 hg1).2 hb.2
      _ = 2*((gamma j)^2)⁻¹ := by rw [inv_div]; ring

theorem original_Q_positive_from_counting
    (gamma eps : ι → ℝ) (hg : ∀ j, 2 ≤ gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (quadratic_count : ∀ T ≥ (10 : ℝ), ∀ F : Finset ι,
      (∀ j ∈ F, gamma j ≤ T) → (F.card : ℝ) ≤ T^2)
    (C p : ℝ) (hp : p < 1)
    (sublinear_count : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ j ∈ F, (gamma j)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p)
    (g : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (gpos : ∀ x > 0, 0 < g x)
    (product_identity : ∀ x > 0, (((g x/c : ℝ) : ℂ)) =
      ∏' j, (1+(x : ℂ)/pole (gamma j) (eps j)))
    (r : ℕ) (u : ℝ) (hu : 0 < u) :
    0 < (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*(-1 : ℝ)^r *
      iteratedDeriv (r+1) (fun x => Real.log (g x) - Real.log c) (u^2) := by
  have hgauss := CountingTail.gaussian_from_counting gamma (fun j => by linarith [hg j])
    quadratic_count
  let S : BranchSpectral.SpectralInput (ι := ι) :=
    ⟨gamma, eps, (fun j => by linarith [hg j]), strip, verified, anchor, anchor_low,
      hgauss.1, hgauss.2⟩
  have hB := fun j => (pole_real_lower (gamma j) (eps j) (hg j) (strip j)).1
  have hs := pole_inverse_summable gamma eps hg strip C p hp sublinear_count
  rw [CanonicalQBridge.original_log_Q_from_product _ hB hs g c hc gpos product_identity r u hu]
  have hkernel (t : ℝ) :
      (∑' j, (Complex.exp (-(pole (gamma j) (eps j)*t))).re) =
        BranchSpectral.kernel gamma eps t := by
    simp only [pole_exp_real, BranchSpectral.kernel]
  simp_rw [hkernel]
  apply mul_pos (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _) (pow_pos hu _))
  apply QnAudit.positive_integral_Ioi
  · intro t ht
    exact mul_pos (mul_pos (pow_pos ht _) (Real.exp_pos _))
      (BranchSpectral.spectral_kernel_pos S t ht)
  · have hi := LaplaceBridge.real_heat_integrable _ r hB hs (u^2) (sq_nonneg u)
    simpa only [hkernel] using hi

theorem original_Q_positive_single_count
    (gamma eps : ι → ℝ) (hg : ∀ j, 2 ≤ gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (count : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ j ∈ F, (gamma j)^2 ≤ y) → (F.card : ℝ) ≤ y^((3 : ℝ)/4))
    (g : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (gpos : ∀ x > 0, 0 < g x)
    (product_identity : ∀ x > 0, (((g x/c : ℝ) : ℂ)) =
      ∏' j, (1+(x : ℂ)/pole (gamma j) (eps j)))
    (r : ℕ) (u : ℝ) (hu : 0 < u) :
    0 < (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*(-1 : ℝ)^r *
      iteratedDeriv (r+1) (fun x => Real.log (g x) - Real.log c) (u^2) := by
  apply original_Q_positive_from_counting gamma eps hg strip verified anchor anchor_low
    ?_ 1 (3/4) (by norm_num) ?_ g c hc gpos product_identity r u hu
  · intro T hT F hF
    have hT2 : 1 ≤ T^2 := by nlinarith
    have hh := count (T^2) hT2 F (by
      intro j hj
      have h1 := hF j hj
      nlinarith [hg j])
    calc
      (F.card : ℝ) ≤ (T^2)^((3 : ℝ)/4) := hh
      _ ≤ (T^2)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT2 (by norm_num)
      _ = T^2 := Real.rpow_one _
  · simpa only [one_mul] using count

end CountedQBridge




set_option maxRecDepth 4000

open scoped BigOperators
open Filter Topology

namespace EtaQBridge

-- This definition includes the removable values at s = 0 and s = 1.
noncomputable def xi (s : ℂ) : ℂ :=
  (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

theorem xi_differentiable : Differentiable ℂ xi := by
  have hz := differentiable_completedZeta₀
  unfold xi
  fun_prop

theorem xi_functional_equation (s : ℂ) : xi (1-s) = xi s := by
  simp only [xi, completedRiemannZeta₀_one_sub]
  ring

theorem xi_centered_even (u : ℂ) : xi (1/2-u) = xi (1/2+u) := by
  convert xi_functional_equation (1/2+u) using 1 <;> congr 1 <;> ring

theorem xi_eq_completed (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s-1) * completedRiemannZeta s / 2 := by
  rw [completedRiemannZeta_eq]
  unfold xi
  have h : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  <;> ring

theorem xi_eq_zeta (s : ℂ) (hr : 0 < s.re) (h1 : s ≠ 1) :
    xi s = s * (s-1) * Complex.Gammaℝ s * riemannZeta s / 2 := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  rw [xi_eq_completed s h0 h1, riemannZeta_def_of_ne_zero h0]
  have hg := Complex.Gammaℝ_ne_zero_of_re_pos hr
  field_simp


end EtaQBridge

namespace XiZeroGeometry
open EtaQBridge Set

theorem xi_zero_value : xi 0 = 1/2 := by simp [xi]
theorem xi_one_value : xi 1 = 1/2 := by simp [xi]

theorem xi_ne_zero_right (s : ℂ) (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases h1 : s = 1
  · rw [h1, xi_one_value]; norm_num
  have hr : 0 < s.re := by linarith
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  rw [xi_eq_zeta s hr h1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0
    (sub_ne_zero.mpr h1)) (Complex.Gammaℝ_ne_zero_of_re_pos hr))
    (riemannZeta_ne_zero_of_one_le_re hs)) (by norm_num)

theorem xi_ne_zero_left (s : ℂ) (hs : s.re ≤ 0) : xi s ≠ 0 := by
  rw [← xi_functional_equation s]
  apply xi_ne_zero_right
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem xi_zero_iff (s : ℂ) :
    xi s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro hx
    have hr : 0 < s.re := lt_of_not_ge (fun h => xi_ne_zero_left s h hx)
    have hl : s.re < 1 := lt_of_not_ge (fun h => xi_ne_zero_right s h hx)
    have h0 : s ≠ 0 := by intro h; simp [h] at hr
    have h1 : s ≠ 1 := by intro h; simp [h] at hl
    rw [xi_eq_zeta s hr h1] at hx
    have hz : riemannZeta s = 0 := by
      rcases (div_eq_zero_iff).mp hx with hh | hh
      · exact (mul_eq_zero.mp hh).resolve_left
          (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
            (Complex.Gammaℝ_ne_zero_of_re_pos hr))
      · norm_num at hh
    exact ⟨hz, hr, hl⟩
  · rintro ⟨hz, hr, hl⟩
    have h1 : s ≠ 1 := by intro h; simp [h] at hl
    rw [xi_eq_zeta s hr h1, hz]
    ring

theorem xi_zero_reflection (s : ℂ) : xi (1-s) = 0 ↔ xi s = 0 := by
  rw [xi_functional_equation]

theorem xi_zeros_compact_finite (S : Set ℂ) (hS : IsCompact S) :
    (S ∩ {s | xi s = 0}).Finite := by
  apply hS.inter_riemannZetaZeros_finite.subset
  intro s hs
  exact ⟨hs.1, (xi_zero_iff s).mp hs.2 |>.1⟩

theorem centered_zero_strip (s : ℂ) (hs : xi s = 0) : |s.re - 1/2| < 1/2 := by
  have h := (xi_zero_iff s).mp hs
  rw [abs_lt]
  constructor <;> linarith [h.2.1, h.2.2]

end XiZeroGeometry

namespace XiMultiplicity
open EtaQBridge Set Filter Topology

theorem xi_analytic (s : ℂ) : AnalyticAt ℂ xi s := xi_differentiable.analyticAt s

theorem xi_order_finite (s : ℂ) : analyticOrderAt xi s ≠ ⊤ := by
  intro h
  have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s xi_analytic).mp h
  have hh := congrFun hz 0
  rw [XiZeroGeometry.xi_zero_value] at hh
  norm_num at hh

theorem xi_multiplicity_pos (s : ℂ) (hs : xi s = 0) :
    0 < analyticOrderNatAt xi s := by
  exact ENat.toNat_pos ((xi_analytic s).analyticOrderAt_ne_zero.mpr hs) (xi_order_finite s)

theorem xi_zeta_order_eq (s : ℂ) (hr : 0 < s.re) (h1 : s ≠ 1) :
    analyticOrderAt xi s = analyticOrderAt riemannZeta s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  have hg0 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hr
  have hg : AnalyticAt ℂ Complex.Gammaℝ s := by
    have hh := (Complex.differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero hg0)
    simpa only [Pi.inv_def, inv_inv] using hh
  let a : ℂ → ℂ := fun z => z*(z-1)*Complex.Gammaℝ z/2
  have ha : AnalyticAt ℂ a s := by
    dsimp [a]
    exact ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hg).div_const
  have ha0 : a s ≠ 0 := div_ne_zero
    (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) hg0) (by norm_num)
  have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s h1
  have he : xi =ᶠ[𝓝 s] a*riemannZeta := by
    have hR : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hr
    filter_upwards [hR, eventually_ne_nhds h1] with z hz hz1
    rw [xi_eq_zeta z hz hz1]
    simp only [Pi.mul_apply, a]
    ring
  rw [analyticOrderAt_congr he, analyticOrderAt_mul ha hz,
    ha.analyticOrderAt_eq_zero.mpr ha0, zero_add]

theorem xi_zeta_multiplicity_eq (s : ℂ) (hs : xi s = 0) :
    analyticOrderNatAt xi s = analyticOrderNatAt riemannZeta s := by
  have h := (XiZeroGeometry.xi_zero_iff s).mp hs
  have h1 : s ≠ 1 := by intro he; simp [he] at h
  unfold analyticOrderNatAt
  rw [xi_zeta_order_eq s h.2.1 h1]

theorem xi_zero_set_countable : {s : ℂ | xi s = 0}.Countable := by
  have hc : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) (n : ℝ) ∩ {s | xi s = 0}).Countable :=
    Set.countable_iUnion (fun n =>
      (XiZeroGeometry.xi_zeros_compact_finite _ (isCompact_closedBall _ _)).countable)
  apply hc.mono
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_gt ‖s‖
  exact mem_iUnion.mpr ⟨n, ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hn.le, hs⟩⟩

def UpperZero := {s : ℂ // xi s = 0 ∧ 0 < s.im}

instance upperZero_countable : Countable UpperZero :=
  (xi_zero_set_countable.mono (fun s hs => hs.1)).to_subtype

def Occurrence := (s : UpperZero) × Fin (analyticOrderNatAt xi s.val)

instance occurrence_countable : Countable Occurrence := by
  unfold Occurrence
  infer_instance

def location (z : Occurrence) : ℂ := z.1.val

theorem occurrence_location (z : Occurrence) :
    riemannZeta (location z) = 0 ∧ 0 < (location z).re ∧
      (location z).re < 1 ∧ 0 < (location z).im := by
  have h := (XiZeroGeometry.xi_zero_iff z.1.val).mp z.1.property.1
  exact ⟨h.1, h.2.1, h.2.2, z.1.property.2⟩

theorem every_upper_zero_occurs (s : ℂ) (hz : riemannZeta s = 0)
    (hr : 0 < s.re) (hl : s.re < 1) (hi : 0 < s.im) :
    ∃ z : Occurrence, location z = s := by
  have hx := (XiZeroGeometry.xi_zero_iff s).mpr ⟨hz,hr,hl⟩
  exact ⟨⟨⟨s,hx,hi⟩,⟨0,xi_multiplicity_pos s hx⟩⟩,rfl⟩

def fiberEquiv (s : UpperZero) : {z : Occurrence // z.1 = s} ≃
    Fin (analyticOrderNatAt xi s.val) where
  toFun z := z.property ▸ z.val.2
  invFun k := ⟨⟨s,k⟩,rfl⟩
  left_inv := by
    rintro ⟨⟨v,k⟩,h⟩
    dsimp at h
    subst v
    rfl
  right_inv := by intro k; rfl

theorem fiber_card (s : UpperZero) :
    Nat.card {z : Occurrence // z.1 = s} = analyticOrderNatAt riemannZeta s.val := by
  rw [Nat.card_congr (fiberEquiv s), Nat.card_fin,
    xi_zeta_multiplicity_eq s.val s.property.1]

theorem occurrences_compact_finite (K : Set ℂ) (hK : IsCompact K) :
    {z : Occurrence | location z ∈ K}.Finite := by
  have hf : {s : UpperZero | s.val ∈ K}.Finite := by
    have hh := Set.Finite.preimage (f := fun s : UpperZero => s.val)
      (fun _ _ _ _ h => Subtype.ext h) (XiZeroGeometry.xi_zeros_compact_finite K hK)
    exact hh.subset (fun s hs => ⟨hs,s.property.1⟩)
  have hfi (s : UpperZero) : {z : Occurrence | z.1 = s}.Finite := by
    exact Set.finite_coe_iff.mp (Finite.of_equiv
      (Fin (analyticOrderNatAt xi s.val)) (fiberEquiv s).symm)
  apply (hf.biUnion (fun s _ => hfi s)).subset
  intro z hz
  exact mem_iUnion.mpr ⟨z.1,mem_iUnion.mpr ⟨hz,rfl⟩⟩

theorem occurrences_bounded_height_finite (T : ℝ) :
    {z : Occurrence | (location z).im ≤ T}.Finite := by
  apply (occurrences_compact_finite (Metric.closedBall 0 (|T|+1))
    (isCompact_closedBall _ _)).subset
  intro z hz
  have h := occurrence_location z
  rw [mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  calc
    ‖location z‖ ≤ |(location z).re|+|(location z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |T|+1 := by rw [abs_of_pos h.2.1, abs_of_pos h.2.2.2]; linarith [h.2.2.1, (show (location z).im ≤ T from hz), le_abs_self T]

theorem occurrence_indexing : ∃ code : Occurrence → ℕ, Function.Injective code :=
  Countable.exists_injective_nat Occurrence

def locationFiberEquiv (s : UpperZero) :
    {z : Occurrence // location z = s.val} ≃ {z : Occurrence // z.1 = s} where
  toFun z := ⟨z.val, Subtype.ext z.property⟩
  invFun z := ⟨z.val, congrArg Subtype.val z.property⟩
  left_inv := by intro z; rfl
  right_inv := by intro z; rfl

theorem complete_countable_zero_index :
    ∃ I : Type, Countable I ∧ ∃ rho : I → ℂ,
      (∀ s : ℂ, (∃ i, rho i = s) ↔
        riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im) ∧
      (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → 0 < s.im →
        Nat.card {i : I // rho i = s} = analyticOrderNatAt riemannZeta s) ∧
      (∀ T : ℝ, {i : I | (rho i).im ≤ T}.Finite) := by
  refine ⟨Occurrence, inferInstance, location, ?_, ?_, occurrences_bounded_height_finite⟩
  · intro s
    constructor
    · rintro ⟨i,rfl⟩
      exact occurrence_location i
    · rintro ⟨hz,hr,hl,hi⟩
      exact every_upper_zero_occurs s hz hr hl hi
  · intro s hz hr hl hi
    let v : UpperZero := ⟨s,(XiZeroGeometry.xi_zero_iff s).mpr ⟨hz,hr,hl⟩,hi⟩
    exact (Nat.card_congr (locationFiberEquiv v)).trans (fiber_card v)

theorem xi_meromorphic_order (s : ℂ) :
    meromorphicOrderAt xi s = ((analyticOrderNatAt xi s : ℕ) : WithTop ℤ) := by
  rw [(xi_analytic s).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (xi_order_finite s)]
  simp

end XiMultiplicity

namespace ActualXiBranches
open EtaQBridge XiMultiplicity Set
noncomputable def G (x : ℝ) : ℝ := (xi (1/2 + (Real.sqrt x : ℂ))).re

theorem G_continuous : Continuous G := by
  exact Complex.continuous_re.comp (xi_differentiable.continuous.comp
    (continuous_const.add (Complex.continuous_ofReal.comp Real.continuous_sqrt)))

theorem G_quarter : G (1/4) = 1/2 := by
  have h : Real.sqrt (1/4) = (1/2 : ℝ) := by
    rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  simp only [G, h]
  norm_num [show (1/2 : ℂ) + ((1/2 : ℝ) : ℂ) = 1 by norm_num,
    XiZeroGeometry.xi_one_value]

theorem continuous_nonzero_positive (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ x ≥ 0, f x ≠ 0) (a : ℝ) (ha : 0 ≤ a) (hfa : 0 < f a) :
    ∀ x ≥ 0, 0 < f x := by
  intro x hx
  by_contra h
  have hfx : f x ≤ 0 := le_of_not_gt h
  rcases le_total x a with hxa | hax
  · obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc hxa hf.continuousOn
      (show (0 : ℝ) ∈ Icc (f x) (f a) from ⟨hfx, hfa.le⟩)
    exact hn y (le_trans hx hy.1) hfy
  · obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc' hax hf.continuousOn
      (show (0 : ℝ) ∈ Icc (f x) (f a) from ⟨hfx, hfa.le⟩)
    exact hn y (le_trans ha hy.1) hfy

theorem G_positive_from_product (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (hp : ∀ x > 0, ((G x / G 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i)) :
    ∀ x ≥ 0, 0 < G x := by
  have hprod (x : ℝ) (hx : 0 < x) : (∏' i, (1+(x : ℂ)/B i)) ≠ 0 := by
    rw [HadamardSeries.canonical_product_eq_exp B hB hs _ (by
      change -(1/2 : ℝ) < (x : ℂ).re
      simpa using (show -(1/2 : ℝ) < x by linarith))]
    exact Complex.exp_ne_zero _
  have h0 : G 0 ≠ 0 := by
    intro he
    have hh := hp 1 (by norm_num)
    simp only [he, div_zero, Complex.ofReal_zero] at hh
    exact hprod 1 (by norm_num) hh.symm
  apply continuous_nonzero_positive G G_continuous ?_ (1/4) (by norm_num)
    (by rw [G_quarter]; norm_num)
  intro x hx
  rcases eq_or_lt_of_le hx with he | he
  · simpa [← he] using h0
  · intro hh
    have hh' := hp x he
    simp only [hh, zero_div, Complex.ofReal_zero] at hh'
    exact hprod x he hh'.symm
end ActualXiBranches

namespace ActualXiBranches
open EtaQBridge XiMultiplicity Set
noncomputable def gamma (i : Occurrence) : ℝ := (location i).im
noncomputable def eps (i : Occurrence) : ℝ := (location i).re - 1/2
noncomputable def B (i : Occurrence) : ℂ := CountedQBridge.pole (gamma i) (eps i)
noncomputable def Q (n : ℕ) (u : ℝ) : ℝ :=
  (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
    iteratedDeriv n (fun x => Real.log (G x) - Real.log (G 0)) (u^2)

theorem eps_bound (i : Occurrence) : |eps i| ≤ 1/2 :=
  (XiZeroGeometry.centered_zero_strip (location i) i.1.property.1).le

theorem B_squared_zero (i : Occurrence) : B i = -(location i-1/2)^2 := by
  apply Complex.ext <;>
    simp [B, CountedQBridge.pole, gamma, eps, Complex.mul_re, Complex.mul_im,
      pow_two] <;> ring

structure Contract : Prop where
  lower : ∀ i, 2 ≤ gamma i
  verified : ∀ i, gamma i ≤ 1000 → eps i = 0
  anchor : ∃ i, gamma i ≤ 100
  count : ∀ y ≥ (1 : ℝ), ∀ F : Finset Occurrence,
    (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ y^((3 : ℝ)/4)
  product : ∀ x > 0, ((G x / G 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i)

theorem concrete_G_positive (h : Contract) : ∀ x ≥ 0, 0 < G x := by
  have hs := CountedQBridge.pole_inverse_summable gamma eps h.lower eps_bound
    1 (3/4) (by norm_num) (by simpa only [one_mul] using h.count)
  exact G_positive_from_product B
    (fun i => (CountedQBridge.pole_real_lower _ _ (h.lower i) (eps_bound i)).1)
    hs h.product

theorem concrete_Q_positive (h : Contract) : ∀ n ≥ 1, ∀ u > 0, 0 < Q n u := by
  intro n hn u hu
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨i, hi⟩ := h.anchor
  have hg := concrete_G_positive h
  have hh := CountedQBridge.original_Q_positive_single_count gamma eps h.lower eps_bound
    h.verified i hi h.count G (G 0) (hg 0 le_rfl)
    (fun x hx => hg x hx.le) h.product r u hu
  simpa [Q] using hh

def OfflineZeros : Set ℂ := {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧
  0 < s.im ∧ s.re ≠ 1/2}

def OfflineIndices : Set Occurrence := {i | eps i ≠ 0}

theorem offline_image : location '' OfflineIndices = OfflineZeros := by
  ext s
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hh := occurrence_location i
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2,
      fun he => hi (sub_eq_zero.mpr he)⟩
  · rintro ⟨hz, hr, hl, him, hoff⟩
    obtain ⟨i, rfl⟩ := every_upper_zero_occurs s hz hr hl him
    exact ⟨i, (fun he => hoff (sub_eq_zero.mp he)), rfl⟩

theorem offline_finite_iff : OfflineIndices.Finite ↔ OfflineZeros.Finite := by
  constructor
  · intro h
    rw [← offline_image]
    exact h.image location
  · intro h
    have hf (s : ℂ) : {i : Occurrence | location i = s}.Finite := by
      apply (occurrences_compact_finite {s} (isCompact_singleton)).subset
      intro i hi
      exact hi
    apply (h.biUnion (fun s _ => hf s)).subset
    intro i hi
    exact mem_iUnion.mpr ⟨location i, mem_iUnion.mpr
      ⟨by rw [← offline_image]; exact ⟨i,hi,rfl⟩,rfl⟩⟩

theorem offline_nonempty_iff : OfflineIndices.Nonempty ↔ OfflineZeros.Nonempty := by
  rw [← offline_image, Set.image_nonempty]

theorem concrete_branches_and_base (h : Contract) :
    (¬ ((∃ n ≥ 1, ∃ u > 0, Q n u < 0) ∧ OfflineZeros.Finite ∧ OfflineZeros.Nonempty)) ∧
    (¬ ((∃ n ≥ 1, ∃ u > 0, Q n u < 0) ∧ OfflineZeros.Infinite)) ∧
    (∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u) ∧
    (∀ n ≥ 1, ∀ u > 0, 0 < Q n u) := by
  have hp := concrete_Q_positive h
  have hn : ¬ (∃ n ≥ 1, ∃ u > 0, Q n u < 0) := by
    rintro ⟨n, hn, u, hu, hh⟩
    exact (not_lt_of_ge (hp n hn u hu).le) hh
  exact ⟨fun hh => hn hh.1, fun hh => hn hh.1,
    fun n hn u hu => (hp n hn u hu).le, hp⟩
def AllOfflineZeros : Set ℂ := {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧
  s.re ≠ 1/2}

theorem full_branches_and_base (h : Contract) :
    (¬ ((∃ n ≥ 1, ∃ u > 0, Q n u < 0) ∧ AllOfflineZeros.Finite ∧ AllOfflineZeros.Nonempty)) ∧
    (¬ ((∃ n ≥ 1, ∃ u > 0, Q n u < 0) ∧ AllOfflineZeros.Infinite)) ∧
    (∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u) ∧
    (∀ n ≥ 1, ∀ u > 0, 0 < Q n u) := by
  have hp := concrete_Q_positive h
  have hn : ¬ (∃ n ≥ 1, ∃ u > 0, Q n u < 0) := by
    rintro ⟨n, hn, u, hu, hh⟩
    exact (not_lt_of_ge (hp n hn u hu).le) hh
  have b2 : ¬ ((∃ n ≥ 1, ∃ u > 0, Q n u < 0) ∧
      OfflineIndices.Finite ∧ OfflineIndices.Nonempty) := fun hh => hn hh.1
  have b3 : ¬ ((∃ n ≥ 1, ∃ u > 0, Q n u < 0) ∧
      OfflineIndices.Infinite) := fun hh => hn hh.1
  have chain := BranchSpectral.nonnegative_via_branches Q OfflineIndices
    (fun _ n hn u hu => (hp n hn u hu).le) b2 b3
  exact ⟨fun hh => hn hh.1, fun hh => hn hh.1, chain, hp⟩

end ActualXiBranches

theorem solution (I : Type*) [Countable I] (B : I → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹)) :
    let f : ℂ → ℂ := (fun s : ℂ => (1+s*(s-1)*completedRiemannZeta₀ s)/2)
    let g : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    (∀ x > 0, ((g x / g 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i)) →
    ∀ x ≥ 0, 0 < g x := by
  exact ActualXiBranches.G_positive_from_product B hB hs
