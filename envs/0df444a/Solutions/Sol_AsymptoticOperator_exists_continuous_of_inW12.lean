-- Prove2me | solution 1 for AsymptoticOperator.exists_continuous_of_inW12
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T00:09:43.434688+00:00
-- url     : https://prove2.me/submissions/69ef4ac5-4b42-4816-b4ff-0a01fac87d61

import Definitions.Def_AsymptoticOperator_Setting
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.PSeries

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator

lemma ao13_summable_inv : Summable fun k : ℤ => 1 / (1 + (k : ℝ) ^ 2) := by
  have h1 : Summable fun k : ℤ => 1 / (k : ℝ) ^ 2 := Real.summable_one_div_int_pow.2 one_lt_two
  have h2 : Summable fun k : ℤ => if k = 0 then (1 : ℝ) else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun k hk => by simp_all
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (h1.add h2)
  by_cases hk : k = 0
  · subst hk; simp
  · simp only [hk, if_false, add_zero]
    have hk' : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    exact one_div_le_one_div_of_le hk' (by linarith)

lemma ao13_amgm (s a : ℝ) (hs : 0 < s) (ha : 0 ≤ a) : a ≤ (s * a ^ 2 + 1 / s) / 2 := by
  have : 0 ≤ (s * a - 1) ^ 2 / s := by positivity
  have e : (s * a - 1) ^ 2 / s = s * a ^ 2 + 1 / s - 2 * a := by
    field_simp
    ring
  linarith

theorem solution {n : ℕ} (f : L2 n) (hf : InW12 f) :
    ∃ φ : C(UnitAddCircle, Vec n),
      (f : UnitAddCircle → Vec n) =ᵐ[AddCircle.haarAddCircle] (φ : UnitAddCircle → Vec n) := by
  -- coordinates of `f` as complex `L²` functions
  let L : (Fin n ⊕ Fin n) → (Vec n →L[ℝ] ℂ) := fun i =>
    Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  let g : (Fin n ⊕ Fin n) → Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    fun i => (L i).compLp f
  have hint : Integrable (fun t => complexify (f t))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    (ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i) :
      Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ)).integrable_comp ((Lp.memLp f).integrable one_le_two)
  have hcoef : ∀ i k, fourierCoeff (g i : UnitAddCircle → ℂ) k = coeff f k i := by
    intro i k
    rw [fourierCoeff_congr_ae ((L i).coeFn_compLp' f)]
    exact (eval_integral (integrable_pi_iff.1 (hint.fourier_smul (-k))) i).symm
  -- absolute summability of the coefficients
  have habs : ∀ i, Summable fun k : ℤ => ‖coeff f k i‖ := by
    intro i
    have hb : Summable fun k : ℤ =>
        ((1 + (k : ℝ) ^ 2) * ∑ j, ‖coeff f k j‖ ^ 2 + 1 / (1 + (k : ℝ) ^ 2)) / 2 :=
      (hf.add ao13_summable_inv).div_const 2
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hb
    have hs : (0 : ℝ) < 1 + (k : ℝ) ^ 2 := by positivity
    have hle : ‖coeff f k i‖ ^ 2 ≤ ∑ j, ‖coeff f k j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖coeff f k j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i)
    have := ao13_amgm _ _ hs (norm_nonneg (coeff f k i))
    have h2 : (1 + (k : ℝ) ^ 2) * ‖coeff f k i‖ ^ 2 ≤ (1 + (k : ℝ) ^ 2) * ∑ j, ‖coeff f k j‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hle hs.le
    linarith
  -- the continuous coordinate functions
  have hsumC : ∀ i, Summable fun k : ℤ => coeff f k i • (fourier k : C(UnitAddCircle, ℂ)) := by
    intro i
    refine Summable.of_norm ?_
    simp_rw [norm_smul, fourier_norm, mul_one]
    exact habs i
  let F : (Fin n ⊕ Fin n) → C(UnitAddCircle, ℂ) := fun i =>
    ∑' k : ℤ, coeff f k i • (fourier k : C(UnitAddCircle, ℂ))
  have hFg : ∀ i, ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (F i) = g i := by
    intro i
    have h1 : HasSum (fun k : ℤ => coeff f k i • fourierBasis k)
        (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (F i)) := by
      have := ((ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ).hasSum
        (hsumC i).hasSum)
      simpa only [map_smul, coe_fourierBasis] using this
    have h2 : HasSum (fun k : ℤ => coeff f k i • fourierBasis k) (g i) := by
      have := fourierBasis.hasSum_repr (g i)
      simpa only [fourierBasis_repr, hcoef] using this
    exact h1.unique h2
  -- the continuous representative
  let φ : C(UnitAddCircle, Vec n) :=
    ⟨fun t => ∑ i, (F i t).re • EuclideanSpace.single i (1 : ℝ), by fun_prop⟩
  have hφ : ∀ t i, φ t i = (F i t).re := by
    intro t i
    simp [φ, EuclideanSpace.single_apply, Pi.single_apply, -Fintype.sum_sum_type]
  refine ⟨φ, ?_⟩
  have hae : ∀ i, ∀ᵐ t ∂(AddCircle.haarAddCircle : Measure UnitAddCircle),
      ((f t i : ℝ) : ℂ) = F i t := by
    intro i
    filter_upwards [(L i).coeFn_compLp' f,
      ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) (F i)]
      with t h1 h2
    rw [hFg i] at h2
    exact h1.symm.trans h2
  filter_upwards [ae_all_iff.2 hae] with t ht
  ext i
  rw [hφ, ← ht i, Complex.ofReal_re]
