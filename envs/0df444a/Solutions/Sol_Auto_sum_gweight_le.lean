-- Prove2me | solution 1 for Auto.sum_gweight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:30:07.927671+00:00
-- url     : https://prove2.me/submissions/bb9d50e5-30c8-4efd-be05-285b059e9626

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_gaussian_le_sup
public import Theorems.Thm_Auto_gaussian_anti
public import Theorems.Thm_Auto_two_div_sqrt_le

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
namespace Auto
theorem _root_.solution {ι : Type*} [Fintype ι] (u : ι → ℝ) {h σ : ℝ} (hh : 0 < h)
    (hσ : h ^ 2 ≤ σ) (kk : ι → ℤ) (hk : Function.Injective kk) (hu : ∀ i, u i = h * kk i)
    (p : ℝ) :
    ∑ i, gweight u h σ p i ≤ 1 + √(2 / π) := by
  classical
  have hσ0 : 0 < σ := lt_of_lt_of_le (by positivity) hσ
  set g : ℝ → ℝ := fun t => gaussian σ (t - p) with hg
  have hgi : Integrable g := (integrable_gaussian' hσ0).comp_sub_right p
  have hg1 : ∫ t, g t = 1 := by
    simp only [hg]
    rw [integral_sub_right_eq_self (fun t => gaussian σ t) p, integral_gaussian_eq_one hσ0]
  have hgnn : ∀ t, 0 ≤ g t := fun t => gaussian_nonneg' _ _
  have hsep : ∀ i j, i ≠ j → h ≤ |u i - u j| := by
    intro i j hij
    rw [hu, hu, ← mul_sub, abs_mul, abs_of_pos hh]
    have : (1 : ℝ) ≤ |(kk i : ℝ) - kk j| := by
      have h1 : kk i ≠ kk j := fun h => hij (hk h)
      have h2 : (1 : ℤ) ≤ |kk i - kk j| := Int.one_le_abs (sub_ne_zero.2 h1)
      exact_mod_cast h2
    nlinarith
  set far := Finset.univ.filter (fun i => h ≤ |u i - p|)
  set mid := Finset.univ.filter (fun i => ¬ h ≤ |u i - p|)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => h ≤ |u i - p|)]
  set I : ι → Set ℝ := fun i => if p ≤ u i then Set.Ioc (u i - h) (u i) else Set.Ico (u i) (u i + h)
  have hImeas : ∀ i, MeasurableSet (I i) := fun i => by
    simp only [I]; split_ifs; exacts [measurableSet_Ioc, measurableSet_Ico]
  have hIvol : ∀ i, (volume (I i)).toReal = h := fun i => by
    simp only [I]; split_ifs <;> simp [hh.le]
  have hIlow : ∀ i ∈ far, ∀ t ∈ I i, g (u i) ≤ g t := by
    intro i hi t ht
    simp only [far, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hg]
    refine gaussian_anti hσ0 ?_
    simp only [I] at ht
    split_ifs at ht with hpu
    · have : u i - p ≥ h := by rw [abs_of_nonneg (by linarith)] at hi; linarith
      rw [abs_of_nonneg (by linarith [ht.1]), abs_of_nonneg (by linarith)]; linarith [ht.2]
    · have : p - u i ≥ h := by rw [abs_of_neg (by linarith)] at hi; linarith
      rw [abs_of_neg (by linarith [ht.2]), abs_of_neg (by linarith)]; linarith [ht.1]
  have hdisj : Set.Pairwise (↑far) (Function.onFun Disjoint I) := by
    intro i hi j hj hij
    simp only [far, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
    have hs := hsep i j hij
    refine Set.disjoint_left.2 fun t hti htj => ?_
    simp only [I] at hti htj
    split_ifs at hti htj with h1 h2 h2
    · rcases le_total (u i) (u j) with h3 | h3
      · rw [abs_of_nonpos (by linarith)] at hs; linarith [hti.2, htj.1]
      · rw [abs_of_nonneg (by linarith)] at hs; linarith [hti.1, htj.2]
    · rw [abs_of_nonneg (by linarith)] at hi
      rw [abs_of_neg (by linarith)] at hj
      linarith [hti.1, htj.2]
    · rw [abs_of_neg (by linarith)] at hi
      rw [abs_of_nonneg (by linarith)] at hj
      linarith [hti.2, htj.1]
    · rcases le_total (u i) (u j) with h3 | h3
      · rw [abs_of_nonpos (by linarith)] at hs; linarith [hti.2, htj.1]
      · rw [abs_of_nonneg (by linarith)] at hs; linarith [hti.1, htj.2]
  have hfar : ∑ i ∈ far, gweight u h σ p i ≤ 1 := by
    calc ∑ i ∈ far, gweight u h σ p i ≤ ∑ i ∈ far, ∫ t in I i, g t := by
          refine Finset.sum_le_sum fun i hi => ?_
          have := setIntegral_ge_of_const_le_real (hImeas i) (by
              simp only [I]; split_ifs <;> simp) (hIlow i hi) hgi.integrableOn
          rw [Measure.real, hIvol i] at this
          simp only [gweight, hg] at this ⊢
          linarith
      _ = ∫ t in ⋃ i ∈ far, I i, g t := (integral_biUnion_finset far (fun i _ => hImeas i) hdisj
            fun i _ => hgi.integrableOn).symm
      _ ≤ ∫ t, g t := setIntegral_le_integral hgi (Eventually.of_forall hgnn)
      _ = 1 := hg1
  have hmid_card : mid.card ≤ 2 := by
    set m0 := ⌊p / h⌋
    have hmaps : ∀ i ∈ mid, kk i ∈ ({m0, m0 + 1} : Finset ℤ) := by
      intro i hi
      simp only [mid, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
      rw [hu, abs_lt] at hi
      have h1 : p / h - 1 < kk i := by
        rw [div_sub_one hh.ne', div_lt_iff₀ hh]; linarith [hi.1]
      have h2 : (kk i : ℝ) < p / h + 1 := by
        have : (kk i : ℝ) < (p + h) / h := by rw [lt_div_iff₀ hh]; linarith [hi.2]
        rwa [add_div, div_self hh.ne'] at this
      have hf1 := Int.floor_le (p / h)
      have hf2 := Int.lt_floor_add_one (p / h)
      have a1 : m0 ≤ kk i := by
        have : (m0 : ℝ) - 1 < kk i := by linarith
        have : m0 - 1 < kk i := by exact_mod_cast this
        omega
      have a2 : kk i ≤ m0 + 1 := by
        have : (kk i : ℝ) < m0 + 2 := by linarith
        have : kk i < m0 + 2 := by exact_mod_cast this
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    calc mid.card ≤ ({m0, m0 + 1} : Finset ℤ).card :=
          Finset.card_le_card_of_injOn kk (fun i hi => hmaps i hi) (fun i _ j _ h => hk h)
      _ ≤ 2 := Finset.card_le_two
  have hmid : ∑ i ∈ mid, gweight u h σ p i ≤ 2 * (√(2 * π))⁻¹ := by
    have hterm : ∀ i, gweight u h σ p i ≤ (√(2 * π))⁻¹ := by
      intro i
      simp only [gweight]
      have h1 := gaussian_le_sup σ (u i - p)
      have h2 : h * (√(2 * π * σ))⁻¹ ≤ (√(2 * π))⁻¹ := by
        rw [Real.sqrt_mul (by positivity), mul_inv, ← mul_assoc, mul_comm h, mul_assoc]
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [mul_inv_le_iff₀ (Real.sqrt_pos.2 hσ0), one_mul]
        exact Real.le_sqrt_of_sq_le hσ
      calc h * gaussian σ (u i - p) ≤ h * (√(2 * π * σ))⁻¹ :=
            mul_le_mul_of_nonneg_left h1 hh.le
        _ ≤ _ := h2
    calc ∑ i ∈ mid, gweight u h σ p i ≤ ∑ _i ∈ mid, (√(2 * π))⁻¹ :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = mid.card * (√(2 * π))⁻¹ := by simp
      _ ≤ 2 * (√(2 * π))⁻¹ := by
          gcongr
          exact_mod_cast hmid_card
  have := two_div_sqrt_le
  linarith
end Auto
