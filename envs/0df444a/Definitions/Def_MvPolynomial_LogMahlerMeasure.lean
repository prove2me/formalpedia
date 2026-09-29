-- Prove2me | Definitions.Def_MvPolynomial_LogMahlerMeasure
-- name    : MvPolynomial_LogMahlerMeasure
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/678a460b-9cc0-5aef-b667-c049f77f905b
-- title:
--   Logarithmic Mahler measure of multivariate complex polynomials
-- statement:
--   For $n \ge 0$, [`MvPolynomial.torusBox n`](../def/MvPolynomial_LogMahlerMeasure.html#L16) is the box $(0,2\pi]^n \subseteq \mathbb{R}^n$, i.e. `Set.pi Set.univ (fun _ ↦ Set.Ioc 0 (2 * π))`, the parameter domain for the unit torus. The accompanying lemmas record that it is measurable, that its Lebesgue measure is $(2\pi)^n$ (in `ℝ≥0∞`, after `toReal`, and as a `Measure.real`), hence nonzero and finite; that the restriction of Lebesgue measure to it is the product of the restrictions of Lebesgue measure on $\mathbb{R}$ to $(0,2\pi]$; that it is contained in, and almost everywhere equal to, the closed box $[0,(2\pi,\dots,2\pi)]$ which is the domain used by Mathlib's torus integral, with the resulting identification of set integrals and of integrability on the two sets; membership criteria for `Fin.cons` and for `Fin.insertNth` insertions; the identification of the image (equivalently the preimage under the inverse) of `torusBox (n+1)` under `MeasurableEquiv.piFinSuccAbove` with $(0,2\pi] \times$ `torusBox n`; and the normalisation $((2\pi)^{-1})^n \int_{\text{torusBox } n} a = a$ for a constant $a$.
--
--   The main definition, [`MvPolynomial.logMahlerMeasure P`](../def/MvPolynomial_LogMahlerMeasure.html#L93) for $P \in \mathbb{C}[X_i : i \in \mathrm{Fin}\,n]$, is the real number
--   $$((2\pi)^{-1})^n \int_{\theta \in (0,2\pi]^n} \log \bigl\| P(e^{i\theta_1},\dots,e^{i\theta_n}) \bigr\|,$$
--   the evaluation point being `fun i ↦ circleMap 0 1 (θ i)`, which is shown to coincide with Mathlib's `torusMap 0 1 θ`. Since `Real.log 0 = 0` and the Bochner integral of a non‑integrable function is $0$, the definition is total. Further lemmas give continuity in $\theta$ of the evaluation, measurability and almost everywhere strong measurability of the integrand, the pointwise bound $\|P(z)\| \le \sum_{m \in \mathrm{supp}\,P} \|\mathrm{coeff}_m P\|$ on the torus, and the values $m(0) = 0$, $m(C c) = \log\|c\|$, $m(1) = 0$, $m(c\,X^m) = \log\|c\|$, $m(X_i) = 0$, together with $m(P) = \log\|{\rm constantCoeff}\,P\|$ in the case $n = 0$.
--
--   **Relation to Mathlib.** Mathlib has the one-variable logarithmic Mahler measure `Polynomial.logMahlerMeasure` (a circle average of $\log\|p(z)\|$); this module supplies the several-variable analogue for `MvPolynomial (Fin n) ℂ` with the same normalisation, together with the box `torusBox n = (0,2\pi]^n`, which is compared here with the closed box used by Mathlib's `torusIntegral`/`TorusIntegrable` and with `torusMap`.
--
--   **Where it is used.** The logarithmic Mahler measure serves as the archimedean device for comparing the size of a polynomial's coefficients with the mean of $\log|P|$ over the unit torus, the form in which archimedean height estimates for polynomials enter later parts of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvPolynomial_LogMahlerMeasure.lean

import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.MeasureTheory.Integral.TorusIntegral
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open MeasureTheory Real

namespace MvPolynomial

variable {n : ℕ}

def torusBox (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ : Fin n ↦ Set.Ioc 0 (2 * π)

theorem torusBox_def (n : ℕ) :
    torusBox n = Set.pi Set.univ fun _ : Fin n ↦ Set.Ioc 0 (2 * π) := rfl

theorem mem_torusBox {θ : Fin n → ℝ} : θ ∈ torusBox n ↔ ∀ i, θ i ∈ Set.Ioc 0 (2 * π) := by
  simp [torusBox]

theorem measurableSet_torusBox : MeasurableSet (torusBox n) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioc

@[simp]
theorem volume_torusBox : volume (torusBox n) = ENNReal.ofReal (2 * π) ^ n := by
  simp [torusBox, volume_pi_pi, Real.volume_Ioc]

theorem volume_torusBox_toReal : (volume (torusBox n)).toReal = (2 * π) ^ n := by
  rw [volume_torusBox, ENNReal.toReal_pow, ENNReal.toReal_ofReal two_pi_pos.le]

@[simp]
theorem volume_real_torusBox : volume.real (torusBox n) = (2 * π) ^ n := by
  rw [measureReal_def, volume_torusBox_toReal]

theorem volume_torusBox_lt_top : volume (torusBox n) < ⊤ := by
  rw [volume_torusBox]
  exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

theorem volume_restrict_torusBox (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).restrict (torusBox n) =
      Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π)) := by
  rw [torusBox, volume_pi, Measure.restrict_pi_pi]

theorem volume_torusBox_ne_zero : volume (torusBox n) ≠ 0 := by
  rw [volume_torusBox]
  exact pow_ne_zero _ (by simp [pi_pos])

theorem torusBox_subset_Icc : torusBox n ⊆ Set.Icc 0 (fun _ ↦ 2 * π) := fun _ hθ ↦
  ⟨fun i ↦ ((mem_torusBox.1 hθ) i).1.le, fun i ↦ ((mem_torusBox.1 hθ) i).2⟩

theorem torusBox_ae_eq_Icc : torusBox n =ᵐ[volume] Set.Icc (0 : Fin n → ℝ) (fun _ ↦ 2 * π) := by
  rw [volume_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

theorem setIntegral_torusBox_eq_setIntegral_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin n → ℝ) → E) :
    ∫ θ in torusBox n, f θ = ∫ θ in Set.Icc (0 : Fin n → ℝ) (fun _ ↦ 2 * π), f θ :=
  setIntegral_congr_set torusBox_ae_eq_Icc

theorem integrableOn_torusBox_iff_integrableOn_Icc {E : Type*} [NormedAddCommGroup E]
    {f : (Fin n → ℝ) → E} :
    IntegrableOn f (torusBox n) ↔ IntegrableOn f (Set.Icc (0 : Fin n → ℝ) (fun _ ↦ 2 * π)) :=
  ⟨fun h ↦ h.congr_set_ae torusBox_ae_eq_Icc.symm, fun h ↦ h.congr_set_ae torusBox_ae_eq_Icc⟩

theorem cons_mem_torusBox_iff {x : ℝ} {θ : Fin n → ℝ} :
    (Fin.cons x θ : Fin (n + 1) → ℝ) ∈ torusBox (n + 1) ↔ x ∈ Set.Ioc 0 (2 * π) ∧ θ ∈ torusBox n := by
  simp [mem_torusBox, Fin.forall_fin_succ]

theorem insertNth_mem_torusBox_iff (i : Fin (n + 1)) {x : ℝ} {θ : Fin n → ℝ} :
    i.insertNth x θ ∈ torusBox (n + 1) ↔ x ∈ Set.Ioc 0 (2 * π) ∧ θ ∈ torusBox n := by
  simp [mem_torusBox, i.forall_iff_succAbove]

theorem piFinSuccAbove_symm_preimage_torusBox (i : Fin (n + 1)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) i).symm ⁻¹' torusBox (n + 1) =
      Set.Ioc 0 (2 * π) ×ˢ torusBox n := by
  ext ⟨x, θ⟩
  simp only [Set.mem_preimage, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, insertNth_mem_torusBox_iff, Set.mem_prod]

theorem piFinSuccAbove_image_torusBox (i : Fin (n + 1)) :
    MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) i '' torusBox (n + 1) =
      Set.Ioc 0 (2 * π) ×ˢ torusBox n := by
  rw [MeasurableEquiv.image_eq_preimage_symm, piFinSuccAbove_symm_preimage_torusBox]

theorem inv_two_pi_pow_mul_setIntegral_torusBox_const (a : ℝ) :
    ((2 * π)⁻¹) ^ n * ∫ _ in torusBox n, a = a := by
  rw [setIntegral_const, volume_real_torusBox, smul_eq_mul, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ two_pi_pos.ne', one_pow, one_mul]

def logMahlerMeasure (P : MvPolynomial (Fin n) ℂ) : ℝ :=
  ((2 * π)⁻¹) ^ n * ∫ θ in torusBox n, Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖

theorem logMahlerMeasure_def (P : MvPolynomial (Fin n) ℂ) :
    P.logMahlerMeasure =
      ((2 * π)⁻¹) ^ n * ∫ θ in torusBox n, Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖ :=
  rfl

theorem circleMap_eq_torusMap (θ : Fin n → ℝ) :
    (fun i ↦ circleMap 0 1 (θ i)) = torusMap 0 1 θ := by
  ext i; simp [torusMap, circleMap]

@[simp]
theorem norm_circleMap_zero_one (t : ℝ) : ‖circleMap 0 1 t‖ = 1 := by
  simp

@[fun_prop]
theorem continuous_eval_circleMap (P : MvPolynomial (Fin n) ℂ) :
    Continuous fun θ : Fin n → ℝ ↦ eval (fun i ↦ circleMap 0 1 (θ i)) P :=
  (continuous_eval P).comp
    (continuous_pi fun i ↦ (continuous_circleMap 0 1).comp (continuous_apply i))

@[fun_prop]
theorem measurable_log_norm_eval_circleMap (P : MvPolynomial (Fin n) ℂ) :
    Measurable fun θ : Fin n → ℝ ↦ Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖ :=
  measurable_log.comp (continuous_eval_circleMap P).norm.measurable

theorem aestronglyMeasurable_log_norm_eval_circleMap (P : MvPolynomial (Fin n) ℂ)
    (μ : Measure (Fin n → ℝ)) :
    AEStronglyMeasurable (fun θ : Fin n → ℝ ↦ Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖) μ :=
  (measurable_log_norm_eval_circleMap P).aestronglyMeasurable

theorem norm_eval_circleMap_le_sum_norm_coeff (P : MvPolynomial (Fin n) ℂ) (θ : Fin n → ℝ) :
    ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖ ≤ ∑ m ∈ P.support, ‖coeff m P‖ := by
  rw [eval_eq]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun m _ ↦ ?_))
  simp [norm_prod, norm_pow]

@[simp]
theorem logMahlerMeasure_zero : (0 : MvPolynomial (Fin n) ℂ).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure]

@[simp]
theorem logMahlerMeasure_C (c : ℂ) : (C c : MvPolynomial (Fin n) ℂ).logMahlerMeasure = log ‖c‖ := by
  simp only [logMahlerMeasure, eval_C]
  exact inv_two_pi_pow_mul_setIntegral_torusBox_const _

@[simp]
theorem logMahlerMeasure_one : (1 : MvPolynomial (Fin n) ℂ).logMahlerMeasure = 0 := by
  rw [← C_1, logMahlerMeasure_C, norm_one, log_one]

@[simp]
theorem logMahlerMeasure_monomial (m : Fin n →₀ ℕ) (c : ℂ) :
    (monomial m c).logMahlerMeasure = log ‖c‖ := by
  simp only [logMahlerMeasure, eval_monomial, norm_mul, Finsupp.prod, norm_prod, norm_pow,
    norm_circleMap_zero_one, one_pow, Finset.prod_const_one, mul_one]
  exact inv_two_pi_pow_mul_setIntegral_torusBox_const _

@[simp]
theorem logMahlerMeasure_X (i : Fin n) : (X i : MvPolynomial (Fin n) ℂ).logMahlerMeasure = 0 := by
  rw [X, logMahlerMeasure_monomial, norm_one, log_one]

theorem logMahlerMeasure_eq_log_norm_constantCoeff (P : MvPolynomial (Fin 0) ℂ) :
    P.logMahlerMeasure = log ‖constantCoeff P‖ := by
  rw [P.eq_C_of_isEmpty, logMahlerMeasure_C, constantCoeff_C]

end MvPolynomial

end


