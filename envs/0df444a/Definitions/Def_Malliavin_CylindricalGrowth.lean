-- Prove2me | Definitions.Def_Malliavin_CylindricalGrowth
-- name    : Malliavin_CylindricalGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:11:34.556956+00:00
-- url     : https://prove2.me/theorems/ac886459-5fc9-5ce7-be01-0b4a3524a69b
-- title:
--   Cylindrical Growth
-- statement:
--   Definitions and structural lemmas for Cylindrical Growth, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_exists_integrable_exp_sq
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mderiv_cylindrical
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
namespace Malliavin
section Truncation
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
noncomputable def truncCoord (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) : Fin n → ℝ :=
  fun i ↦ cutoff m (L i x)
end Truncation
section Growth
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
noncomputable def gaussWeight {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) : ℝ :=
  1 + ∑ i, |L i x|
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
theorem one_le_gaussWeight {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) : 1 ≤ gaussWeight L x :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
theorem one_add_norm_le_gaussWeight {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) :
    1 + ‖fun i ↦ L i x‖ ≤ gaussWeight L x := by
  unfold gaussWeight
  gcongr
  exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)).mpr fun i ↦
    (Real.norm_eq_abs _).le.trans (Finset.single_le_sum (fun j _ ↦ abs_nonneg (L j x))
      (Finset.mem_univ i))
omit [CompleteSpace W] [SecondCountableTopology W] in
/-- Powers of the Gaussian weight are integrable. -/
theorem integrable_gaussWeight_pow {n : ℕ} (L : Fin n → StrongDual ℝ W) (k : ℕ) :
    Integrable (fun x ↦ gaussWeight L x ^ k) μ := by
  have hsum : MemLp (fun x ↦ ∑ i, |L i x|) k μ :=
    memLp_finsetSum (f := fun i x ↦ |L i x|) Finset.univ fun i _ ↦
      (IsGaussian.memLp_dual μ (L i) k (by simp)).norm
  have hmem : MemLp (gaussWeight L) k μ := (memLp_const (1 : ℝ)).add hsum
  have := hmem.integrable_norm_pow'
  refine this.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (one_le_gaussWeight L x))]
theorem abs_fderiv_single_le {n : ℕ} (f : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) (i : Fin n) :
    |fderiv ℝ f y (Pi.single i 1)| ≤ ‖fderiv ℝ f y‖ := by
  rw [← Real.norm_eq_abs]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  by_cases hij : j = i <;> simp [hij]
theorem norm_mderiv_cylinder_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : (Fin n → ℝ) → ℝ} (hφ : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (L : Fin n → StrongDual ℝ W)
    (x : W) :
    ‖mderiv μ (fun y ↦ f (fun i ↦ L i y)) x‖ ≤ φ (fun i ↦ L i x) * ∑ i, ‖ofDual μ (L i)‖ := by
  rw [mderiv_cylindrical μ f L x (hf.differentiable one_ne_zero _)]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h1 : |fderiv ℝ f (fun i ↦ L i x) (Pi.single i 1)| ≤ φ (fun i ↦ L i x) :=
    (abs_fderiv_single_le f _ i).trans (hφ _)
  gcongr
theorem continuous_mderiv_cylinder {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (L : Fin n → StrongDual ℝ W) :
    Continuous (mderiv μ (fun y ↦ f (fun i ↦ L i y))) := by
  have h : mderiv μ (fun y ↦ f (fun i ↦ L i y)) =
      fun x ↦ ∑ i, fderiv ℝ f (fun i ↦ L i x) (Pi.single i 1) • ofDual μ (L i) := by
    funext x
    exact mderiv_cylindrical μ f L x (hf.differentiable one_ne_zero _)
  rw [h]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  have hc : Continuous fun x ↦ fderiv ℝ f (fun i ↦ L i x) (Pi.single i (1 : ℝ)) :=
    ((hf.continuous_fderiv one_ne_zero).comp (continuous_pi fun i ↦ (L i).continuous)).clm_apply
      continuous_const
  exact hc.smul continuous_const
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian μ] in
/-- A measurable function dominated by a square-integrable function is in `L²`. -/
theorem memLp_of_le_of_integrable_sq {E : Type*} [NormedAddCommGroup E] {g : W → E}
    (hg : AEStronglyMeasurable g μ) {ψ : W → ℝ} (hint : Integrable (fun x ↦ ψ x ^ 2) μ)
    (h : ∀ x, ‖g x‖ ≤ ψ x) : MemLp g 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm hg).mpr ?_
  refine hint.mono' (hg.norm.pow 2) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) (h x) 2
omit [CompleteSpace W] [SecondCountableTopology W] [IsGaussian μ] in
/-- A dominated `C¹` cylindrical functional is square integrable. -/
theorem memLp_cylinder_of_dominated {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (L : Fin n → StrongDual ℝ W) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ} (hφf : ∀ y, |f y| ≤ φ y)
    (hψ' : ∀ x, φ (fun i ↦ L i x) ≤ ψ x) (hint : Integrable (fun x ↦ ψ x ^ 2) μ) :
    MemLp (fun x ↦ f (fun i ↦ L i x)) 2 μ :=
  memLp_of_le_of_integrable_sq μ
    (hf.continuous.comp (continuous_pi fun i ↦ (L i).continuous)).aestronglyMeasurable hint
    fun x ↦ (Real.norm_eq_abs _).le.trans ((hφf _).trans (hψ' x))
theorem memLp_mderiv_cylinder_of_dominated {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (L : Fin n → StrongDual ℝ W) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ}
    (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (hψ' : ∀ x, φ (fun i ↦ L i x) ≤ ψ x)
    (hint : Integrable (fun x ↦ ψ x ^ 2) μ) :
    MemLp (mderiv μ (fun y ↦ f (fun i ↦ L i y))) 2 μ :=
  memLp_of_le_of_integrable_sq μ (continuous_mderiv_cylinder μ hf L).aestronglyMeasurable
    (ψ := fun x ↦ ψ x * ∑ i, ‖ofDual μ (L i)‖)
    (by simpa [mul_pow] using hint.mul_const ((∑ i, ‖ofDual μ (L i)‖) ^ 2)) fun x ↦
    (norm_mderiv_cylinder_le μ hf hφf' L x).trans
      (mul_le_mul_of_nonneg_right (hψ' x) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The growth weight `C (1 + ‖y‖)ᵏ` of the coordinates is dominated by the Gaussian weight. -/
theorem growth_coord_le {n k : ℕ} {C : ℝ} (hC : 0 ≤ C) (L : Fin n → StrongDual ℝ W) (x : W) :
    C * (1 + ‖fun i ↦ L i x‖) ^ k ≤ C * gaussWeight L x ^ k := by
  gcongr
  exact one_add_norm_le_gaussWeight L x
omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The squared Gaussian growth weight is integrable. -/
theorem integrable_growth_sq {n k : ℕ} (C : ℝ) (L : Fin n → StrongDual ℝ W) :
    Integrable (fun x ↦ (C * gaussWeight L x ^ k) ^ 2) μ := by
  simpa [mul_pow, ← pow_mul, mul_comm k 2] using
    (integrable_gaussWeight_pow μ L (2 * k)).const_mul (C ^ 2)
omit [CompleteSpace W] [SecondCountableTopology W] in
/-- A `C¹` cylindrical functional of polynomial growth is square integrable. -/
theorem memLp_cylinder_growth {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k) (L : Fin n → StrongDual ℝ W) :
    MemLp (fun x ↦ f (fun i ↦ L i x)) 2 μ :=
  memLp_cylinder_of_dominated μ hf L hfg (growth_coord_le hC L) (integrable_growth_sq μ C L)
theorem memLp_mderiv_cylinder_growth {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k)
    (L : Fin n → StrongDual ℝ W) :
    MemLp (mderiv μ (fun y ↦ f (fun i ↦ L i y))) 2 μ :=
  memLp_mderiv_cylinder_of_dominated μ hf L hfg' (growth_coord_le hC L)
    (integrable_growth_sq μ C L)
theorem integrable_exp_mul_norm (a : ℝ) : Integrable (fun x ↦ Real.exp (a * ‖x‖)) μ := by
  obtain ⟨C, hC, hint⟩ := IsGaussian.exists_integrable_exp_sq μ
  refine (hint.const_mul (Real.exp (a ^ 2 / (4 * C)))).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), ← Real.exp_add, Real.exp_le_exp]
  have h : 0 ≤ (2 * C * ‖x‖ - a) ^ 2 := sq_nonneg _
  have hC' : 0 < 4 * C := by positivity
  rw [← sub_nonneg]
  calc (0 : ℝ) = (2 * C * ‖x‖ - a) ^ 2 / (4 * C) - (2 * C * ‖x‖ - a) ^ 2 / (4 * C) := by ring
    _ ≤ (2 * C * ‖x‖ - a) ^ 2 / (4 * C) := by
        rw [sub_le_self_iff]
        positivity
    _ = a ^ 2 / (4 * C) + C * ‖x‖ ^ 2 - a * ‖x‖ := by
        field_simp
        ring
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ] in
/-- The coordinates are bounded by `(∑ᵢ ‖Lᵢ‖) ‖x‖`. -/
theorem norm_coord_le {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) :
    ‖fun i ↦ L i x‖ ≤ (∑ i, ‖L i‖) * ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  refine ((L i).le_opNorm x).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact Finset.single_le_sum (fun j _ ↦ norm_nonneg (L j)) (Finset.mem_univ i)
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The exponential weight of the coordinates is dominated by `C exp (c (∑ᵢ ‖Lᵢ‖) ‖x‖)`. -/
theorem expGrowth_coord_le {n : ℕ} {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (L : Fin n → StrongDual ℝ W) (x : W) :
    C * Real.exp (c * ‖fun i ↦ L i x‖) ≤ C * Real.exp (c * ((∑ i, ‖L i‖) * ‖x‖)) := by
  gcongr
  exact norm_coord_le L x
theorem integrable_expGrowth_sq (C c K : ℝ) :
    Integrable (fun x ↦ (C * Real.exp (c * (K * ‖x‖))) ^ 2) μ := by
  refine ((integrable_exp_mul_norm μ (2 * (c * K))).const_mul (C ^ 2)).congr
    (Filter.Eventually.of_forall fun x ↦ ?_)
  have h : Real.exp (2 * (c * K) * ‖x‖) = Real.exp (c * (K * ‖x‖)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  simp only [h, mul_pow]
theorem memLp_cylinder_expGrowth {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hfg : ∀ y, |f y| ≤ C * Real.exp (c * ‖y‖))
    (L : Fin n → StrongDual ℝ W) :
    MemLp (fun x ↦ f (fun i ↦ L i x)) 2 μ :=
  memLp_cylinder_of_dominated μ hf L (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L i‖) * ‖x‖)))
    hfg (expGrowth_coord_le hC hc L) (integrable_expGrowth_sq μ C c _)
theorem memLp_mderiv_cylinder_expGrowth {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖))
    (L : Fin n → StrongDual ℝ W) :
    MemLp (mderiv μ (fun y ↦ f (fun i ↦ L i y))) 2 μ :=
  memLp_mderiv_cylinder_of_dominated μ hf L
    (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L i‖) * ‖x‖))) hfg' (expGrowth_coord_le hC hc L)
    (integrable_expGrowth_sq μ C c _)
end Growth
section OneCoord
variable {g : ℝ → ℝ}
theorem contDiff_oneCoord (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun y : Fin 1 → ℝ ↦ g (y 0)) :=
  hg.comp (contDiff_apply ℝ ℝ 0)
theorem abs_oneCoord_le {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hg : ∀ x, |g x| ≤ C * Real.exp (c * |x|)) (y : Fin 1 → ℝ) :
    |g (y 0)| ≤ C * Real.exp (c * ‖y‖) := by
  refine (hg _).trans ?_
  gcongr
  exact (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm y 0)
theorem fderiv_oneCoord (hg : ContDiff ℝ 1 g) (y : Fin 1 → ℝ) :
    fderiv ℝ (fun y : Fin 1 → ℝ ↦ g (y 0)) y =
      deriv g (y 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0 := by
  have h : HasFDerivAt (g ∘ fun y : Fin 1 → ℝ ↦ y 0)
      (deriv g (y 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0) y :=
    (hg.differentiable one_ne_zero (y 0)).hasDerivAt.comp_hasFDerivAt y (hasFDerivAt_apply 0 y)
  exact h.fderiv
theorem norm_proj_zero_le : ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z ↦ by
    rw [one_mul, ContinuousLinearMap.proj_apply]
    exact norm_le_pi_norm z 0
theorem norm_fderiv_oneCoord_le (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hg' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|)) (y : Fin 1 → ℝ) :
    ‖fderiv ℝ (fun y : Fin 1 → ℝ ↦ g (y 0)) y‖ ≤ C * Real.exp (c * ‖y‖) := by
  rw [fderiv_oneCoord hg, norm_smul, Real.norm_eq_abs]
  calc |deriv g (y 0)| * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0‖
      ≤ (C * Real.exp (c * ‖y‖)) * 1 := by
        gcongr
        · refine (hg' _).trans ?_
          gcongr
          exact (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm y 0)
        · exact norm_proj_zero_le
    _ = C * Real.exp (c * ‖y‖) := mul_one _
theorem abs_exp_le_exp_abs (x : ℝ) : |Real.exp x| ≤ 1 * Real.exp (1 * |x|) := by
  rw [abs_of_pos (Real.exp_pos _), one_mul, one_mul]
  exact Real.exp_le_exp.mpr (le_abs_self x)
theorem abs_pow_le_exp_mul_abs (x : ℝ) {i n : ℕ} (hi : i ≤ n) :
    |x| ^ i ≤ Real.exp (n * |x|) := by
  calc |x| ^ i ≤ Real.exp |x| ^ i := by
        gcongr
        exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp |x|)
    _ = Real.exp (i * |x|) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (n * |x|) := by
        gcongr
theorem contDiff_polynomial_eval (p : Polynomial ℝ) : ContDiff ℝ 1 (fun x ↦ p.eval x) := by
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using p.contDiff_aeval (𝕜 := ℝ) 1
theorem abs_polynomial_eval_le (p : Polynomial ℝ) {n : ℕ} (hn : p.natDegree ≤ n) (x : ℝ) :
    |p.eval x| ≤ (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) * Real.exp (n * |x|) := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  rw [abs_mul, abs_pow]
  gcongr
  exact abs_pow_le_exp_mul_abs x ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hn)
noncomputable def coeffMass (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|
theorem coeffMass_nonneg (p : Polynomial ℝ) : 0 ≤ coeffMass p :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
theorem abs_polynomial_eval_le' (p : Polynomial ℝ) (x : ℝ) :
    |p.eval x| ≤ (coeffMass p + coeffMass p.derivative) * Real.exp (p.natDegree * |x|) :=
  (abs_polynomial_eval_le p le_rfl x).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (coeffMass_nonneg _))
      (Real.exp_nonneg _))
theorem abs_exp_sub_le_exp_abs (c x : ℝ) (hc : 0 ≤ c) :
    |Real.exp (x - c)| ≤ 1 * Real.exp (1 * |x|) := by
  rw [abs_of_pos (Real.exp_pos _), one_mul, one_mul, Real.exp_le_exp]
  linarith [le_abs_self x]
theorem contDiff_exp_sub (c : ℝ) : ContDiff ℝ 1 (fun x ↦ Real.exp (x - c)) :=
  Real.contDiff_exp.comp (contDiff_id.sub contDiff_const)
theorem abs_sin_le_exp_abs (x : ℝ) : |Real.sin x| ≤ 1 * Real.exp (1 * |x|) := by
  rw [one_mul, one_mul]
  exact (Real.abs_sin_le_one x).trans (Real.one_le_exp (abs_nonneg x))
end OneCoord
section Brownian
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL
omit [CompleteSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- A dominated `C¹` function of finitely many Brownian coordinates is square integrable. -/
theorem memLp_cylinder_brownian_of_dominated {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ} (hφf : ∀ y, |f y| ≤ φ y)
    (t : Fin n → ℝ≥0) (hψ' : ∀ x, φ (fun i ↦ L (t i) x) ≤ ψ x)
    (hint : Integrable (fun x ↦ ψ x ^ 2) P) :
    MemLp (fun w ↦ f (fun i ↦ B (t i) w)) 2 P := by
  have h : (fun w ↦ f (fun i ↦ B (t i) w)) = fun w ↦ f (fun i ↦ L (t i) w) := by
    funext w
    simp only [hL]
  rw [h]
  exact memLp_cylinder_of_dominated P hf _ hφf hψ' hint
omit [CompleteSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- The partial derivative `∂ᵢ f (B t₁, …, B tₙ)` is square integrable when `f'` is
dominated. -/
theorem memLp_cylinderPartial_of_dominated {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ}
    (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (t : Fin n → ℝ≥0)
    (hψ' : ∀ x, φ (fun i ↦ L (t i) x) ≤ ψ x) (hint : Integrable (fun x ↦ ψ x ^ 2) P)
    (i : Fin n) :
    MemLp (fun w ↦ fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1)) 2 P := by
  have h : (fun w ↦ fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1)) =
      fun w ↦ fderiv ℝ f (fun j ↦ L (t j) w) (Pi.single i 1) := by
    funext w
    simp only [hL]
  rw [h]
  have hc : Continuous fun w ↦ fderiv ℝ f (fun j ↦ L (t j) w) (Pi.single i (1 : ℝ)) :=
    ((hf.continuous_fderiv one_ne_zero).comp (continuous_pi fun j ↦ (L (t j)).continuous)).clm_apply
      continuous_const
  refine memLp_of_le_of_integrable_sq P hc.aestronglyMeasurable hint fun w ↦ ?_
  rw [Real.norm_eq_abs]
  exact (abs_fderiv_single_le f _ i).trans ((hφf' _).trans (hψ' w))
noncomputable def cylinderPartialD {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ} (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (t : Fin n → ℝ≥0)
    (hψ' : ∀ x, φ (fun i ↦ L (t i) x) ≤ ψ x) (hint : Integrable (fun x ↦ ψ x ^ 2) P)
    (i : Fin n) : Lp ℝ 2 P :=
  (memLp_cylinderPartial_of_dominated L hL hf hφf' t hψ' hint i).toLp _
omit [CompleteSpace W] [SecondCountableTopology W] in
/-- A `C¹` function of polynomial growth of finitely many Brownian coordinates is square
integrable. -/
theorem memLp_cylinder_growth_brownian {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k) (t : Fin n → ℝ≥0) :
    MemLp (fun w ↦ f (fun i ↦ B (t i) w)) 2 P :=
  memLp_cylinder_brownian_of_dominated L hL hf hfg t (growth_coord_le hC _)
    (integrable_growth_sq P C _)
noncomputable def cylinderPartialGrowth {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k) (t : Fin n → ℝ≥0)
    (i : Fin n) : Lp ℝ 2 P :=
  cylinderPartialD L hL hf hfg' t (growth_coord_le hC _) (integrable_growth_sq P C _) i
theorem memLp_cylinder_expGrowth_brownian {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hfg : ∀ y, |f y| ≤ C * Real.exp (c * ‖y‖))
    (t : Fin n → ℝ≥0) :
    MemLp (fun w ↦ f (fun i ↦ B (t i) w)) 2 P :=
  memLp_cylinder_brownian_of_dominated L hL hf hfg t
    (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L (t i)‖) * ‖x‖))) (expGrowth_coord_le hC hc _)
    (integrable_expGrowth_sq P C c _)
noncomputable def cylinderPartialExp {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖))
    (t : Fin n → ℝ≥0) (i : Fin n) : Lp ℝ 2 P :=
  cylinderPartialD L hL hf hfg' t (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L (t i)‖) * ‖x‖)))
    (expGrowth_coord_le hC hc _) (integrable_expGrowth_sq P C c _) i
variable {g : ℝ → ℝ}
theorem memLp_comp_brownian (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgb : ∀ x, |g x| ≤ C * Real.exp (c * |x|)) (T : ℝ≥0) :
    MemLp (fun w ↦ g (B T w)) 2 P :=
  memLp_cylinder_expGrowth_brownian L hL (contDiff_oneCoord hg) hC hc (abs_oneCoord_le hC hc hgb)
    (fun _ ↦ T)
theorem memLp_exp_brownian (T : ℝ≥0) : MemLp (fun w ↦ Real.exp (B T w)) 2 P :=
  memLp_comp_brownian L hL Real.contDiff_exp zero_le_one zero_le_one abs_exp_le_exp_abs T
theorem memLp_wickExp_brownian (T : ℝ≥0) : MemLp (fun w ↦ Real.exp (B T w - T / 2)) 2 P :=
  memLp_comp_brownian L hL (contDiff_exp_sub (T / 2)) zero_le_one zero_le_one
    (fun x ↦ abs_exp_sub_le_exp_abs (T / 2) x (by positivity)) T
theorem memLp_sin_brownian (T : ℝ≥0) : MemLp (fun w ↦ Real.sin (B T w)) 2 P :=
  memLp_comp_brownian L hL Real.contDiff_sin zero_le_one zero_le_one abs_sin_le_exp_abs T
omit [CompleteSpace W] [SecondCountableTopology W] in
/-- `cos (B T)` is square integrable. -/
theorem memLp_cos_brownian (T : ℝ≥0) : MemLp (fun w ↦ Real.cos (B T w)) 2 P := by
  have h : (fun w ↦ Real.cos (B T w)) = fun w ↦ Real.cos (L T w) := by
    funext w
    rw [hL]
  rw [h]
  exact MemLp.of_bound (Real.continuous_cos.comp (L T).continuous).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun w ↦ by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
theorem memLp_polynomial_brownian (p : Polynomial ℝ) (T : ℝ≥0) :
    MemLp (fun w ↦ p.eval (B T w)) 2 P :=
  memLp_comp_brownian L hL (contDiff_polynomial_eval p)
    (add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)) (Nat.cast_nonneg _)
    (abs_polynomial_eval_le' p) T
theorem memLp_polynomial_derivative_brownian (p : Polynomial ℝ) (T : ℝ≥0) :
    MemLp (fun w ↦ p.derivative.eval (B T w)) 2 P :=
  memLp_polynomial_brownian L hL p.derivative T
end Brownian
section TwoCoord
def mulCoord (y : Fin 2 → ℝ) : ℝ := y 0 * y 1
theorem contDiff_mulCoord : ContDiff ℝ 1 mulCoord :=
  (contDiff_apply ℝ ℝ 0).mul (contDiff_apply ℝ ℝ 1)
theorem fderiv_mulCoord (y : Fin 2 → ℝ) :
    fderiv ℝ mulCoord y = y 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
      y 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1 := by
  have h : HasFDerivAt (fun y : Fin 2 → ℝ ↦ y 0 * y 1)
      (y 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
        y 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1) y := by
    have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 ↦ ℝ) 0 y
    have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 ↦ ℝ) 1 y
    have := h0.mul h1
    rw [add_comm]
    exact this
  exact h.fderiv
theorem abs_mulCoord_le (y : Fin 2 → ℝ) : |mulCoord y| ≤ 2 * (1 + ‖y‖) ^ 2 := by
  unfold mulCoord
  rw [abs_mul]
  have h0 : |y 0| ≤ ‖y‖ := (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm y 0)
  have h1 : |y 1| ≤ ‖y‖ := (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm y 1)
  calc |y 0| * |y 1| ≤ ‖y‖ * ‖y‖ := mul_le_mul h0 h1 (abs_nonneg _) (norm_nonneg _)
    _ = ‖y‖ ^ 2 := (sq _).symm
    _ ≤ 2 * (1 + ‖y‖) ^ 2 := by linarith [norm_nonneg y, sq_nonneg ‖y‖, sq_nonneg (1 + ‖y‖)]
theorem norm_fderiv_mulCoord_le (y : Fin 2 → ℝ) : ‖fderiv ℝ mulCoord y‖ ≤ 2 * (1 + ‖y‖) ^ 2 := by
  rw [fderiv_mulCoord]
  have hp : ∀ i : Fin 2, ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) i‖ ≤ 1 :=
    fun i ↦ ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z ↦ by
      rw [one_mul, ContinuousLinearMap.proj_apply]
      exact norm_le_pi_norm z i
  have h0 : |y 0| ≤ ‖y‖ := (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm y 0)
  have h1 : |y 1| ≤ ‖y‖ := (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm y 1)
  calc ‖y 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
        y 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1‖
      ≤ ‖y 1‖ * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0‖ +
        ‖y 0‖ * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ ‖y‖ * 1 + ‖y‖ * 1 := by
        gcongr
        · rw [Real.norm_eq_abs]; exact h1
        · exact hp 0
        · rw [Real.norm_eq_abs]; exact h0
        · exact hp 1
    _ ≤ 2 * (1 + ‖y‖) ^ 2 := by linarith [norm_nonneg y, sq_nonneg ‖y‖, sq_nonneg (1 + ‖y‖)]
end TwoCoord
section Brownian
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL
omit [CompleteSpace W] [SecondCountableTopology W] in
/-- `B S · B T` is square integrable. -/
theorem memLp_mul_brownian (S T : ℝ≥0) : MemLp (fun w ↦ B S w * B T w) 2 P :=
  memLp_cylinder_growth_brownian L hL contDiff_mulCoord zero_le_two abs_mulCoord_le ![S, T]
omit [CompleteSpace W] [SecondCountableTopology W] in
theorem memLp_brownian (T : ℝ≥0) : MemLp (B T) 2 P := by
  have h : B T = fun w ↦ L T w := by
    funext w
    exact hL T w
  rw [h]
  exact (IsGaussian.memLp_dual P (L T) 2 (by simp))
end Brownian
end Malliavin


