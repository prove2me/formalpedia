-- Prove2me | solution 1 for AutomorphicForm.GL2Twisted.contDiff_integral_twistedEllipticTransform_mul_chebyshevU
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/97928853-30a1-5842-81d9-faffbb5168a2

import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Twisted_contDiff_integral_twistedEllipticTransform_mul_chebyshevU

set_option autoImplicit false

open MeasureTheory Polynomial AutomorphicForm AutomorphicForm.GL2Twisted

noncomputable section

namespace TwistedEllipticModes

private abbrev Ent : Type := Fin 2 → Fin 2 → ℂ

private abbrev Box : Type := ℝ × ℝ × ℝ × ℝ

private abbrev Chart : Type := (ℝ × ℝ) × (ℂ × Box)

private def boxMeasure₃ : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod
    ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))

private def boxMeasure₂ : Measure (ℝ × ℝ × ℝ) :=
  ((volume : Measure ℝ).restrict (Set.Ioc 0 (Real.pi / 2))).prod boxMeasure₃

private def boxMeasure : Measure Box := ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod boxMeasure₂

private def radiusMeasure : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).restrict (Set.Ioc 0 Real.pi)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))

private def shearBoxMeasure : Measure (ℂ × Box) := (volume : Measure ℂ).prod boxMeasure

private def chartMeasure : Measure Chart := radiusMeasure.prod shearBoxMeasure

private scoped instance : IsFiniteMeasure boxMeasure₃ := by unfold boxMeasure₃; infer_instance
private scoped instance : IsFiniteMeasure boxMeasure₂ := by unfold boxMeasure₂; infer_instance
private scoped instance : IsFiniteMeasure boxMeasure := by unfold boxMeasure; infer_instance
private scoped instance : SFinite radiusMeasure := by unfold radiusMeasure; infer_instance
private scoped instance : SFinite shearBoxMeasure := by unfold shearBoxMeasure; infer_instance
private scoped instance : SFinite chartMeasure := by unfold chartMeasure; infer_instance

private def kMat (ψ η ξ₁ ξ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
      Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
    Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
      Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))]

private def kInv (ψ η ξ₁ ξ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(ψ * Complex.I)) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I))),
      Complex.exp (-(ψ * Complex.I)) * (-(Real.sin η * Complex.exp (ξ₂ * Complex.I)));
    Complex.exp (-(ψ * Complex.I)) * (Real.sin η * Complex.exp (-(ξ₂ * Complex.I))),
      Complex.exp (-(ψ * Complex.I)) * (Real.cos η * Complex.exp (ξ₁ * Complex.I))]

private def kBar (ψ η ξ₁ ξ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (kMat ψ η ξ₁ ξ₂).map (starRingEnd ℂ)

private def kBarInv (ψ η ξ₁ ξ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (kInv ψ η ξ₁ ξ₂).map (starRingEnd ℂ)

private def nMat (θ ρ : ℝ) (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(u * ρ * Complex.exp (-(θ / 2 * Complex.I))),
      (ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) - (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I));
    ρ * Complex.exp (-(θ / 2 * Complex.I)),
      (starRingEnd ℂ) u * ρ * Complex.exp (-(θ / 2 * Complex.I))]

private def ent₁ (θ ρ : ℝ) (u : ℂ) (ψ η ξ₁ ξ₂ : ℝ) : Ent :=
  Matrix.of.symm (kInv ψ η ξ₁ ξ₂ * nMat θ ρ u * kBar ψ η ξ₁ ξ₂)

private def entAt (ε : ℝ) (ω : Chart) : Ent :=
  ent₁ (ε * ω.1.1) ω.1.2 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2

private def modeScalar (j : ℕ) (ω : Chart) : ℝ :=
  4 * Real.sin ω.1.1 ^ 2 * (Chebyshev.U ℝ (j : ℤ)).eval (Real.cos ω.1.1) * (ω.1.2)⁻¹ * (1 / (4 * Real.pi ^ 3)) *
    (Real.sin ω.2.2.2.1 * Real.cos ω.2.2.2.1)

private theorem exp_mul_exp_neg (t : ℝ) : Complex.exp (t * Complex.I) * Complex.exp (-(t * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

private theorem cos_sq_add_sin_sq' (η : ℝ) : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq η

private theorem kInv_mul_kMat (ψ η ξ₁ ξ₂ : ℝ) : kInv ψ η ξ₁ ξ₂ * kMat ψ η ξ₁ ξ₂ = 1 := by
  have hψ := exp_mul_exp_neg ψ
  have h₁ := exp_mul_exp_neg ξ₁
  have h₂ := exp_mul_exp_neg ξ₂
  have h₃ := cos_sq_add_sin_sq' η
  rw [kInv, kMat, Matrix.mul_fin_two, Matrix.one_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination ((Real.cos η : ℂ) ^ 2 * (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I))) +
        (Real.sin η : ℂ) ^ 2 * (Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)))) * hψ +
      (Real.cos η : ℂ) ^ 2 * h₁ + (Real.sin η : ℂ) ^ 2 * h₂ + h₃
  · ring
  · ring
  · linear_combination ((Real.sin η : ℂ) ^ 2 * (Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I))) +
        (Real.cos η : ℂ) ^ 2 * (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)))) * hψ +
      (Real.sin η : ℂ) ^ 2 * h₂ + (Real.cos η : ℂ) ^ 2 * h₁ + h₃

private theorem kMat_mul_kInv (ψ η ξ₁ ξ₂ : ℝ) : kMat ψ η ξ₁ ξ₂ * kInv ψ η ξ₁ ξ₂ = 1 := by
  have hψ := exp_mul_exp_neg ψ
  have h₁ := exp_mul_exp_neg ξ₁
  have h₂ := exp_mul_exp_neg ξ₂
  have h₃ := cos_sq_add_sin_sq' η
  rw [kMat, kInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination ((Real.cos η : ℂ) ^ 2 * (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I))) +
        (Real.sin η : ℂ) ^ 2 * (Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)))) * hψ +
      (Real.cos η : ℂ) ^ 2 * h₁ + (Real.sin η : ℂ) ^ 2 * h₂ + h₃
  · ring
  · ring
  · linear_combination ((Real.sin η : ℂ) ^ 2 * (Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I))) +
        (Real.cos η : ℂ) ^ 2 * (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)))) * hψ +
      (Real.sin η : ℂ) ^ 2 * h₂ + (Real.cos η : ℂ) ^ 2 * h₁ + h₃

private theorem kBar_mul_kBarInv (ψ η ξ₁ ξ₂ : ℝ) : kBar ψ η ξ₁ ξ₂ * kBarInv ψ η ξ₁ ξ₂ = 1 := by
  rw [kBar, kBarInv, ← Matrix.map_mul, kMat_mul_kInv, Matrix.map_one] <;> simp

private theorem norm_exp_real_mul_I (t : ℝ) : ‖Complex.exp (t * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]; simp

private theorem norm_exp_neg_real_mul_I (t : ℝ) : ‖Complex.exp (-(t * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]; simp

private theorem kMat_entry_norm_le (ψ η ξ₁ ξ₂ : ℝ) (i j : Fin 2) : ‖kMat ψ η ξ₁ ξ₂ i j‖ ≤ 1 := by
  have hc : ‖(Real.cos η : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one η
  have hs : ‖(Real.sin η : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one η
  fin_cases i <;> fin_cases j <;>
    simp only [kMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, norm_mul, norm_neg, norm_exp_real_mul_I, norm_exp_neg_real_mul_I, one_mul, mul_one] <;>
    assumption

private theorem kInv_entry_norm_le (ψ η ξ₁ ξ₂ : ℝ) (i j : Fin 2) : ‖kInv ψ η ξ₁ ξ₂ i j‖ ≤ 1 := by
  have hc : ‖(Real.cos η : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one η
  have hs : ‖(Real.sin η : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one η
  fin_cases i <;> fin_cases j <;>
    simp only [kInv, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, norm_mul, norm_neg, norm_exp_real_mul_I, norm_exp_neg_real_mul_I, one_mul, mul_one] <;>
    assumption

private theorem kBarInv_entry_norm_le (ψ η ξ₁ ξ₂ : ℝ) (i j : Fin 2) : ‖kBarInv ψ η ξ₁ ξ₂ i j‖ ≤ 1 := by
  simpa [kBarInv, Matrix.map_apply, Complex.norm_conj] using kInv_entry_norm_le ψ η ξ₁ ξ₂ i j

private theorem nMat_entry_norm_le (θ ρ : ℝ) (u : ℂ) (ψ η ξ₁ ξ₂ : ℝ) (B : ℝ)
    (h : ∀ i j, ‖ent₁ θ ρ u ψ η ξ₁ ξ₂ i j‖ ≤ B) (i j : Fin 2) : ‖nMat θ ρ u i j‖ ≤ 4 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (h 0 0)
  set X : Matrix (Fin 2) (Fin 2) ℂ := kInv ψ η ξ₁ ξ₂ * nMat θ ρ u * kBar ψ η ξ₁ ξ₂ with hX
  have hX' : ∀ a b, ‖X a b‖ ≤ B := fun a b => h a b
  have hN : nMat θ ρ u = kMat ψ η ξ₁ ξ₂ * X * kBarInv ψ η ξ₁ ξ₂ := by
    rw [hX, Matrix.mul_assoc (kInv _ _ _ _), ← Matrix.mul_assoc (kMat _ _ _ _), kMat_mul_kInv, Matrix.one_mul,
      Matrix.mul_assoc, kBar_mul_kBarInv, Matrix.mul_one]
  have key : ∀ a b : Fin 2, ‖kMat ψ η ξ₁ ξ₂ i a * X a b * kBarInv ψ η ξ₁ ξ₂ b j‖ ≤ B := by
    intro a b
    rw [norm_mul, norm_mul]
    calc ‖kMat ψ η ξ₁ ξ₂ i a‖ * ‖X a b‖ * ‖kBarInv ψ η ξ₁ ξ₂ b j‖ ≤ 1 * B * 1 := by
          gcongr
          · exact kMat_entry_norm_le ψ η ξ₁ ξ₂ i a
          · exact hX' a b
          · exact kBarInv_entry_norm_le ψ η ξ₁ ξ₂ b j
      _ = B := by ring
  rw [hN, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, add_mul]
  calc ‖kMat ψ η ξ₁ ξ₂ i 0 * X 0 0 * kBarInv ψ η ξ₁ ξ₂ 0 j + kMat ψ η ξ₁ ξ₂ i 1 * X 1 0 * kBarInv ψ η ξ₁ ξ₂ 0 j +
          (kMat ψ η ξ₁ ξ₂ i 0 * X 0 1 * kBarInv ψ η ξ₁ ξ₂ 1 j + kMat ψ η ξ₁ ξ₂ i 1 * X 1 1 * kBarInv ψ η ξ₁ ξ₂ 1 j)‖
        ≤ ‖kMat ψ η ξ₁ ξ₂ i 0 * X 0 0 * kBarInv ψ η ξ₁ ξ₂ 0 j‖ + ‖kMat ψ η ξ₁ ξ₂ i 1 * X 1 0 * kBarInv ψ η ξ₁ ξ₂ 0 j‖ +
          (‖kMat ψ η ξ₁ ξ₂ i 0 * X 0 1 * kBarInv ψ η ξ₁ ξ₂ 1 j‖ +
            ‖kMat ψ η ξ₁ ξ₂ i 1 * X 1 1 * kBarInv ψ η ξ₁ ξ₂ 1 j‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ B + B + (B + B) := by gcongr <;> exact key _ _
    _ = 4 * B := by ring

private theorem slab_facts (θ ρ : ℝ) (u : ℂ) (B' : ℝ) (hρ : 0 < ρ) (h : ∀ i j, ‖nMat θ ρ u i j‖ ≤ B') :
    ρ ≤ B' ∧ |Real.sin θ| ≤ B' * ρ ∧ Complex.normSq u * ρ ≤ ρ⁻¹ + B' := by
  have h10 := h 1 0
  have h01 := h 0 1
  simp only [nMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h10 h01
  have hθm : ‖Complex.exp (-(θ / 2 * Complex.I))‖ = 1 := by
    rw [Complex.norm_exp]; simp

  have hρ' : ρ ≤ B' := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, hθm, mul_one] at h10
    exact h10
  have hB' : 0 ≤ B' := hρ.le.trans hρ'

  have hfac :
      (ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) - (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I)) =
        Complex.exp (-(θ / 2 * Complex.I)) *
        (((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (θ * Complex.I) - (Complex.normSq u * ρ : ℝ)) := by
    have he : Complex.exp (θ / 2 * Complex.I) = Complex.exp (-(θ / 2 * Complex.I)) * Complex.exp (θ * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [he]; push_cast; ring
  rw [hfac, norm_mul, hθm, one_mul] at h01
  set x : ℝ := ρ⁻¹ with hx
  set y : ℝ := Complex.normSq u * ρ with hy
  have hxpos : 0 < x := by rw [hx]; exact inv_pos.mpr hρ
  have hre : ((x : ℂ) * Complex.exp (θ * Complex.I) - (y : ℂ)).re = x * Real.cos θ - y := by
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have him : ((x : ℂ) * Complex.exp (θ * Complex.I) - (y : ℂ)).im = x * Real.sin θ := by
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hsq : (x * Real.cos θ - y) ^ 2 + (x * Real.sin θ) ^ 2 ≤ B' ^ 2 := by
    have h1 : ‖(x : ℂ) * Complex.exp (θ * Complex.I) - (y : ℂ)‖ ^ 2 =
        (x * Real.cos θ - y) ^ 2 + (x * Real.sin θ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
    rw [← h1]
    exact pow_le_pow_left₀ (norm_nonneg _) h01 2
  refine ⟨hρ', ?_, ?_⟩
  ·
    have h2 : (x * Real.sin θ) ^ 2 ≤ B' ^ 2 := le_trans (by nlinarith [sq_nonneg (x * Real.cos θ - y)]) hsq
    have h3 : |x * Real.sin θ| ≤ B' := abs_le_of_sq_le_sq h2 hB'
    rw [abs_mul, abs_of_pos hxpos] at h3
    have h4 : |Real.sin θ| = ρ * (x * |Real.sin θ|) := by
      rw [hx, ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]
    rw [h4]
    calc ρ * (x * |Real.sin θ|) ≤ ρ * B' := by gcongr
      _ = B' * ρ := mul_comm _ _
  ·
    have h2 : (x * Real.cos θ - y) ^ 2 ≤ B' ^ 2 := le_trans (by nlinarith [sq_nonneg (x * Real.sin θ)]) hsq
    have h3 : -B' ≤ x * Real.cos θ - y := (abs_le_of_sq_le_sq' h2 hB').1
    have h5 : x * Real.cos θ ≤ x := by
      calc x * Real.cos θ ≤ x * 1 := by gcongr; exact Real.cos_le_one θ
        _ = x := mul_one x
    show y ≤ x + B'
    linarith

private theorem measurable_modeScalar (j : ℕ) : Measurable (modeScalar j) := by
  unfold modeScalar
  have hU : Measurable fun ω : Chart => (Chebyshev.U ℝ (j : ℤ)).eval (Real.cos ω.1.1) :=
    (Polynomial.continuous _).measurable.comp (Real.measurable_cos.comp measurable_fst.fst)
  fun_prop

private theorem measurable_entAt (ε : ℝ) : Measurable (entAt ε) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun k => ?_
  have hexp : Measurable fun z : ℂ => Complex.exp z := Complex.continuous_exp.measurable
  have hconj : Measurable fun z : ℂ => (starRingEnd ℂ) z := Complex.continuous_conj.measurable
  have hnsq : Measurable fun z : ℂ => (Complex.normSq z : ℂ) :=
    (Complex.continuous_ofReal.comp Complex.continuous_normSq).measurable
  have hre : Measurable fun x : ℝ => (x : ℂ) := Complex.continuous_ofReal.measurable
  fin_cases i <;> fin_cases k <;>
    simp only [entAt, ent₁, kInv, nMat, kBar, kMat, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_symm_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one,
      Fin.isValue] <;>
    fun_prop

private theorem measurable_slabFn (j : ℕ) (ε B : ℝ) :
    Measurable fun ω : Chart => if ‖entAt ε ω‖ ≤ B then |modeScalar j ω| else 0 := by
  have habs : Measurable fun ω : Chart => |modeScalar j ω| := by
    have h := measurable_modeScalar j
    fun_prop
  exact Measurable.ite (measurableSet_le (measurable_entAt ε).norm measurable_const) habs measurable_const

private def angleWeight (j : ℕ) (θ : ℝ) : ℝ :=
  4 * Real.sin θ ^ 2 * |(Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ)| * (1 / (4 * Real.pi ^ 3))

private theorem angleWeight_nonneg (j : ℕ) (θ : ℝ) : 0 ≤ angleWeight j θ := by
  unfold angleWeight; positivity

private theorem abs_modeScalar_le (j : ℕ) (ω : Chart) (hρ : 0 < ω.1.2) :
    |modeScalar j ω| ≤ angleWeight j ω.1.1 * ω.1.2⁻¹ := by
  unfold modeScalar angleWeight
  have h1 : |Real.sin ω.2.2.2.1 * Real.cos ω.2.2.2.1| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _)
  have hinv : 0 < ω.1.2⁻¹ := inv_pos.mpr hρ
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.sin ω.1.1 ^ 2),
    abs_of_pos hinv, abs_of_pos (by positivity : (0 : ℝ) < 1 / (4 * Real.pi ^ 3))]
  calc 4 * Real.sin ω.1.1 ^ 2 * |(Chebyshev.U ℝ (j : ℤ)).eval (Real.cos ω.1.1)| * ω.1.2⁻¹ * (1 / (4 * Real.pi ^ 3)) *
        |Real.sin ω.2.2.2.1 * Real.cos ω.2.2.2.1|
      ≤ 4 * Real.sin ω.1.1 ^ 2 * |(Chebyshev.U ℝ (j : ℤ)).eval (Real.cos ω.1.1)| * ω.1.2⁻¹ * (1 / (4 * Real.pi ^ 3)) *
          1 := by
        gcongr
    _ = 4 * Real.sin ω.1.1 ^ 2 * |(Chebyshev.U ℝ (j : ℤ)).eval (Real.cos ω.1.1)| * (1 / (4 * Real.pi ^ 3)) *
          ω.1.2⁻¹ := by
        ring

private def radiusSet (B' : ℝ) : Set (ℝ × ℝ) := {x | |Real.sin x.1| ≤ B' * x.2 ∧ x.2 ≤ B'}

private theorem mem_radiusSet {B' : ℝ} {x : ℝ × ℝ} : x ∈ radiusSet B' ↔ |Real.sin x.1| ≤ B' * x.2 ∧ x.2 ≤ B' := Iff.rfl

private theorem measurableSet_radiusSet (B' : ℝ) : MeasurableSet (radiusSet B') := by
  have h1 : MeasurableSet {x : ℝ × ℝ | |Real.sin x.1| ≤ B' * x.2} := measurableSet_le (by fun_prop) (by fun_prop)
  have h2 : MeasurableSet {x : ℝ × ℝ | x.2 ≤ B'} := measurableSet_le measurable_snd measurable_const
  exact h1.inter h2

open Classical in

private def radiusFactor (j : ℕ) (B' : ℝ) (x : ℝ × ℝ) : ℝ := if x ∈ radiusSet B' then angleWeight j x.1 * x.2⁻¹ else 0

private theorem measurable_radiusFactor (j : ℕ) (B' : ℝ) : Measurable (radiusFactor j B') := by
  unfold radiusFactor
  refine Measurable.ite (measurableSet_radiusSet B') ?_ measurable_const
  unfold angleWeight
  have hU : Measurable fun x : ℝ × ℝ => (Chebyshev.U ℝ (j : ℤ)).eval (Real.cos x.1) :=
    (Polynomial.continuous _).measurable.comp (Real.measurable_cos.comp measurable_fst)
  fun_prop

private def shearSet (B' ρ : ℝ) : Set ℂ := {u | Complex.normSq u * ρ ≤ ρ⁻¹ + B'}

private theorem mem_shearSet {B' ρ : ℝ} {u : ℂ} : u ∈ shearSet B' ρ ↔ Complex.normSq u * ρ ≤ ρ⁻¹ + B' := Iff.rfl

private theorem measurableSet_shearSet (B' ρ : ℝ) : MeasurableSet (shearSet B' ρ) := by
  have h : MeasurableSet {u : ℂ | Complex.normSq u * ρ ≤ ρ⁻¹ + B'} :=
    measurableSet_le (Complex.continuous_normSq.mul continuous_const).measurable measurable_const
  exact h

private theorem volume_shearSet_le (B' ρ : ℝ) (hB' : 0 ≤ B') (hρ : 0 < ρ) :
    volume (shearSet B' ρ) ≤ ENNReal.ofReal (Real.pi * ((ρ⁻¹ + B') * ρ⁻¹)) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (ρ⁻¹ + B') * ρ⁻¹ := ⟨_, rfl⟩
  rw [← hR]
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hsub : shearSet B' ρ ⊆ Metric.closedBall (0 : ℂ) (Real.sqrt R) := by
    intro u hu
    have hu' : Complex.normSq u * ρ ≤ ρ⁻¹ + B' := mem_shearSet.mp hu
    have hsq : ‖u‖ ^ 2 ≤ R := by
      rw [Complex.sq_norm, hR]
      calc Complex.normSq u = Complex.normSq u * ρ * ρ⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hρ.ne', mul_one]
        _ ≤ (ρ⁻¹ + B') * ρ⁻¹ := mul_le_mul_of_nonneg_right hu' (inv_pos.mpr hρ).le
    have habs := Real.abs_le_sqrt hsq
    rw [abs_of_nonneg (norm_nonneg u)] at habs
    rw [Metric.mem_closedBall, dist_zero_right]
    exact habs
  calc volume (shearSet B' ρ) ≤ volume (Metric.closedBall (0 : ℂ) (Real.sqrt R)) := measure_mono hsub
    _ = ENNReal.ofReal (Real.sqrt R) ^ 2 * NNReal.pi := Complex.volume_closedBall 0 (Real.sqrt R)
    _ = ENNReal.ofReal R * ENNReal.ofReal Real.pi := by
        rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg R), Real.sq_sqrt hR0, ← NNReal.coe_real_pi,
          ENNReal.ofReal_coe_nnreal]
    _ = ENNReal.ofReal (Real.pi * R) := by rw [ENNReal.ofReal_mul Real.pi_pos.le, mul_comm]

private def majorant (j : ℕ) (B' : ℝ) (ω : Chart) : ENNReal :=
  ENNReal.ofReal (radiusFactor j B' ω.1) * (if Complex.normSq ω.2.1 * ω.1.2 ≤ ω.1.2⁻¹ + B' then 1 else 0)

private theorem measurable_majorant (j : ℕ) (B' : ℝ) : Measurable (majorant j B') := by
  unfold majorant
  have h1 : Measurable fun ω : Chart => ENNReal.ofReal (radiusFactor j B' ω.1) :=
    ENNReal.measurable_ofReal.comp ((measurable_radiusFactor j B').comp measurable_fst)
  have h2 : Measurable fun ω : Chart => Complex.normSq ω.2.1 * ω.1.2 :=
    (Complex.continuous_normSq.measurable.comp measurable_snd.fst).mul measurable_fst.snd
  have h3 : Measurable fun ω : Chart => ω.1.2⁻¹ + B' := measurable_fst.snd.inv.add_const B'
  have hs : MeasurableSet {ω : Chart | Complex.normSq ω.2.1 * ω.1.2 ≤ ω.1.2⁻¹ + B'} := measurableSet_le h2 h3
  exact h1.mul (Measurable.ite hs measurable_const measurable_const)

private theorem enorm_slabFn_le_majorant (j : ℕ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (B : ℝ) (ω : Chart) (hρ : 0 < ω.1.2) :
    ‖(if ‖entAt ε ω‖ ≤ B then |modeScalar j ω| else 0)‖ₑ ≤ majorant j (4 * max B 0 + 1) ω := by
  split_ifs with h
  ·
    have hent : ∀ i k, ‖ent₁ (ε * ω.1.1) ω.1.2 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2 i k‖ ≤ B := by
      intro i k
      have h1 : ‖entAt ε ω i‖ ≤ ‖entAt ε ω‖ := norm_le_pi_norm (entAt ε ω) i
      have h2 : ‖entAt ε ω i k‖ ≤ ‖entAt ε ω i‖ := norm_le_pi_norm (entAt ε ω i) k
      exact (h2.trans h1).trans h
    have hBmax : 4 * B ≤ 4 * max B 0 + 1 := by
      have := le_max_left B 0
      linarith
    have hN : ∀ i k, ‖nMat (ε * ω.1.1) ω.1.2 ω.2.1 i k‖ ≤ 4 * max B 0 + 1 :=
      fun i k => (nMat_entry_norm_le _ _ _ _ _ _ _ B hent i k).trans hBmax
    obtain ⟨h₁, h₂, h₃⟩ := slab_facts (ε * ω.1.1) ω.1.2 ω.2.1 (4 * max B 0 + 1) hρ hN
    have hsin : |Real.sin ω.1.1| = |Real.sin (ε * ω.1.1)| := by
      rcases hε with rfl | rfl
      · rw [one_mul]
      · rw [neg_one_mul, Real.sin_neg, abs_neg]
    have hmem : ω.1 ∈ radiusSet (4 * max B 0 + 1) := mem_radiusSet.mpr ⟨by rw [hsin]; exact h₂, h₁⟩
    unfold majorant radiusFactor
    rw [if_pos hmem, if_pos h₃, mul_one, Real.enorm_eq_ofReal_abs, abs_abs]
    exact ENNReal.ofReal_le_ofReal (abs_modeScalar_le j ω hρ)
  · simp

private theorem ae_radius_pos : ∀ᵐ x ∂radiusMeasure, 0 < x.2 := by
  have hmeas : MeasurableSet {x : ℝ × ℝ | 0 < x.2} := measurableSet_lt measurable_const measurable_snd
  refine (Measure.ae_prod_iff_ae_ae hmeas).2 ?_
  refine Filter.Eventually.of_forall fun θ => ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
  exact Set.mem_Ioi.mp hρ

private theorem ae_chart_pos_radius : ∀ᵐ ω ∂chartMeasure, 0 < ω.1.2 := by
  have hmeas : MeasurableSet {ω : Chart | 0 < ω.1.2} := measurableSet_lt measurable_const measurable_fst.snd
  refine (Measure.ae_prod_iff_ae_ae hmeas).2 ?_
  filter_upwards [ae_radius_pos] with x hx
  exact Filter.Eventually.of_forall fun _ => hx

private theorem lintegral_majorant_shearBox (j : ℕ) (B' : ℝ) (x : ℝ × ℝ) :
    ∫⁻ z, majorant j B' (x, z) ∂shearBoxMeasure =
      ENNReal.ofReal (radiusFactor j B' x) * (volume (shearSet B' x.2) * boxMeasure Set.univ) := by
  unfold majorant shearBoxMeasure
  show ∫⁻ z : ℂ × Box, ENNReal.ofReal (radiusFactor j B' x) *
      (if Complex.normSq z.1 * x.2 ≤ x.2⁻¹ + B' then (1 : ENNReal) else 0) ∂((volume : Measure ℂ).prod boxMeasure) = _
  have hm : Measurable fun z : ℂ × Box => if Complex.normSq z.1 * x.2 ≤ x.2⁻¹ + B' then (1 : ENNReal) else 0 :=
    Measurable.ite ((measurableSet_shearSet B' x.2).preimage measurable_fst) measurable_const measurable_const
  rw [lintegral_const_mul _ hm]
  congr 1
  have hP : ((volume : Measure ℂ).prod boxMeasure) (shearSet B' x.2 ×ˢ (Set.univ : Set Box)) =
      volume (shearSet B' x.2) * boxMeasure Set.univ := Measure.prod_prod _ _
  rw [← hP, ← lintegral_indicator_one ((measurableSet_shearSet B' x.2).prod MeasurableSet.univ)]
  congr 1
  funext z
  by_cases hz : Complex.normSq z.1 * x.2 ≤ x.2⁻¹ + B'
  · have hmem : z ∈ shearSet B' x.2 ×ˢ (Set.univ : Set Box) := Set.mem_prod.mpr ⟨mem_shearSet.mpr hz, Set.mem_univ _⟩
    rw [if_pos hz, Set.indicator_of_mem hmem, Pi.one_apply]
  · have hnot : z ∉ shearSet B' x.2 ×ˢ (Set.univ : Set Box) := fun h => hz (mem_shearSet.mp (Set.mem_prod.mp h).1)
    rw [if_neg hz, Set.indicator_of_notMem hnot]

private def radiusConst (j : ℕ) (B' θ : ℝ) : ℝ := angleWeight j θ * (Real.pi * (1 + B' ^ 2))

private theorem radiusConst_nonneg (j : ℕ) (B' θ : ℝ) : 0 ≤ radiusConst j B' θ := by
  unfold radiusConst
  exact mul_nonneg (angleWeight_nonneg j θ) (by positivity)

private theorem radiusFactor_mul_le (j : ℕ) (B' : ℝ) (x : ℝ × ℝ) (hρ : 0 < x.2) (hx : x ∈ radiusSet B') :
    radiusFactor j B' x * (Real.pi * ((x.2⁻¹ + B') * x.2⁻¹)) ≤ radiusConst j B' x.1 * x.2 ^ (-3 : ℝ) := by
  have hρB : x.2 ≤ B' := (mem_radiusSet.mp hx).2
  have hB' : 0 ≤ B' := hρ.le.trans hρB
  have hw := angleWeight_nonneg j x.1
  have hy : 0 < x.2⁻¹ := inv_pos.mpr hρ
  have hpow : x.2 ^ (-3 : ℝ) = x.2⁻¹ ^ 3 := by
    rw [Real.rpow_neg hρ.le, inv_pow]
    norm_cast
  have hcancel : x.2 * x.2⁻¹ = 1 := mul_inv_cancel₀ hρ.ne'
  have hB2 : B' * x.2⁻¹ ^ 2 ≤ B' ^ 2 * x.2⁻¹ ^ 3 := by
    calc B' * x.2⁻¹ ^ 2 = B' * x.2⁻¹ ^ 2 * (x.2 * x.2⁻¹) := by rw [hcancel, mul_one]
      _ = B' * x.2 * x.2⁻¹ ^ 3 := by ring
      _ ≤ B' * B' * x.2⁻¹ ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρB hB') (pow_nonneg hy.le 3)
      _ = B' ^ 2 * x.2⁻¹ ^ 3 := by ring
  have key : x.2⁻¹ * ((x.2⁻¹ + B') * x.2⁻¹) ≤ (1 + B' ^ 2) * x.2⁻¹ ^ 3 := by
    calc x.2⁻¹ * ((x.2⁻¹ + B') * x.2⁻¹) = x.2⁻¹ ^ 3 + B' * x.2⁻¹ ^ 2 := by ring
      _ ≤ x.2⁻¹ ^ 3 + B' ^ 2 * x.2⁻¹ ^ 3 := add_le_add_right hB2 _
      _ = (1 + B' ^ 2) * x.2⁻¹ ^ 3 := by ring
  unfold radiusFactor radiusConst
  rw [if_pos hx, hpow]
  calc angleWeight j x.1 * x.2⁻¹ * (Real.pi * ((x.2⁻¹ + B') * x.2⁻¹))
      = angleWeight j x.1 * Real.pi * (x.2⁻¹ * ((x.2⁻¹ + B') * x.2⁻¹)) := by ring
    _ ≤ angleWeight j x.1 * Real.pi * ((1 + B' ^ 2) * x.2⁻¹ ^ 3) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg hw Real.pi_pos.le)
    _ = angleWeight j x.1 * (Real.pi * (1 + B' ^ 2)) * x.2⁻¹ ^ 3 := by ring

private theorem lintegral_radius_le (j : ℕ) (B' : ℝ) (hB' : 0 < B') (θ : ℝ) (U₀ : ℝ)
    (hU : |(Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ)| ≤ U₀) :
    ∫⁻ ρ in Set.Ioi (0 : ℝ), ENNReal.ofReal (radiusConst j B' θ) *
        (if |Real.sin θ| / B' ≤ ρ then ENNReal.ofReal (ρ ^ (-3 : ℝ)) else 0) ≤
      ENNReal.ofReal (2 * U₀ * (1 / (4 * Real.pi ^ 3)) * (Real.pi * (1 + B' ^ 2)) * B' ^ 2) := by
  have hmeas : Measurable fun ρ : ℝ => (if |Real.sin θ| / B' ≤ ρ then ENNReal.ofReal (ρ ^ (-3 : ℝ)) else 0) :=
    Measurable.ite (measurableSet_le measurable_const measurable_id')
      (ENNReal.measurable_ofReal.comp (measurable_id'.pow_const (-3 : ℝ))) measurable_const
  rw [lintegral_const_mul _ hmeas]
  by_cases hs : Real.sin θ = 0
  · have h0 : radiusConst j B' θ = 0 := by simp [radiusConst, angleWeight, hs]
    rw [h0, ENNReal.ofReal_zero, zero_mul]
    exact zero_le
  · have hs' : Real.sin θ ≠ 0 := hs
    have ha : 0 < |Real.sin θ| / B' := div_pos (abs_pos.mpr hs') hB'
    have hpt : ∀ ρ : ℝ, (if |Real.sin θ| / B' ≤ ρ then ENNReal.ofReal (ρ ^ (-3 : ℝ)) else 0) =
        (Set.Ici (|Real.sin θ| / B')).indicator (fun ρ : ℝ => ENNReal.ofReal (ρ ^ (-3 : ℝ))) ρ := by
      intro ρ
      by_cases hρ : |Real.sin θ| / B' ≤ ρ
      · rw [if_pos hρ, Set.indicator_of_mem (Set.mem_Ici.mpr hρ)]
      · have hnot : ρ ∉ Set.Ici (|Real.sin θ| / B') := fun h => hρ (Set.mem_Ici.mp h)
        rw [if_neg hρ, Set.indicator_of_notMem hnot]
    have hsub : Set.Ici (|Real.sin θ| / B') ⊆ Set.Ioi (0 : ℝ) :=
      fun ρ hρ => Set.mem_Ioi.mpr (lt_of_lt_of_le ha (Set.mem_Ici.mp hρ))
    have hres : (volume : Measure ℝ).restrict (Set.Ici (|Real.sin θ| / B')) =
        (volume : Measure ℝ).restrict (Set.Ioi (|Real.sin θ| / B')) :=
      (Measure.restrict_congr_set Ioi_ae_eq_Ici).symm
    have hint : IntegrableOn (fun ρ : ℝ => ρ ^ (-3 : ℝ)) (Set.Ioi (|Real.sin θ| / B')) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) ha
    have hnn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi (|Real.sin θ| / B'))] fun ρ : ℝ => ρ ^ (-3 : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
      exact Real.rpow_nonneg (ha.le.trans (Set.mem_Ioi.mp hρ).le) _
    have hI : ∫ ρ in Set.Ioi (|Real.sin θ| / B'), ρ ^ (-3 : ℝ) =
        -(|Real.sin θ| / B') ^ ((-3 : ℝ) + 1) / ((-3 : ℝ) + 1) :=
      integral_Ioi_rpow_of_lt (by norm_num) ha
    have hval : ∫⁻ ρ in Set.Ioi (0 : ℝ), (if |Real.sin θ| / B' ≤ ρ then ENNReal.ofReal (ρ ^ (-3 : ℝ)) else 0) =
        ENNReal.ofReal (((|Real.sin θ| / B') ^ 2)⁻¹ / 2) := by
      simp only [hpt]
      rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict_of_subset hsub, hres,
        ← ofReal_integral_eq_lintegral_ofReal hint hnn, hI]
      congr 1
      rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg ha.le, Real.rpow_two, neg_div_neg_eq]
    have ha2 : ((|Real.sin θ| / B') ^ 2)⁻¹ = B' ^ 2 / Real.sin θ ^ 2 := by rw [div_pow, sq_abs, inv_div]
    rw [hval, ← ENNReal.ofReal_mul (radiusConst_nonneg j B' θ)]
    apply ENNReal.ofReal_le_ofReal
    rw [ha2]
    have hs2 : Real.sin θ ^ 2 ≠ 0 := pow_ne_zero 2 hs'
    unfold radiusConst angleWeight
    calc 4 * Real.sin θ ^ 2 * |(Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ)| * (1 / (4 * Real.pi ^ 3)) *
          (Real.pi * (1 + B' ^ 2)) * (B' ^ 2 / Real.sin θ ^ 2 / 2)
        = Real.sin θ ^ 2 * (Real.sin θ ^ 2)⁻¹ *
            (2 * |(Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ)| * (1 / (4 * Real.pi ^ 3)) * (Real.pi * (1 + B' ^ 2)) *
              B' ^ 2) := by
          ring
      _ = 2 * |(Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ)| * (1 / (4 * Real.pi ^ 3)) * (Real.pi * (1 + B' ^ 2)) *
            B' ^ 2 := by
          rw [mul_inv_cancel₀ hs2, one_mul]
      _ ≤ 2 * U₀ * (1 / (4 * Real.pi ^ 3)) * (Real.pi * (1 + B' ^ 2)) * B' ^ 2 := by
          have hc : (0 : ℝ) ≤ 1 / (4 * Real.pi ^ 3) := by positivity
          have hP : (0 : ℝ) ≤ Real.pi * (1 + B' ^ 2) := by positivity
          have hB2 : (0 : ℝ) ≤ B' ^ 2 := by positivity
          have h2U : 2 * |(Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ)| ≤ 2 * U₀ :=
            mul_le_mul_of_nonneg_left hU (by norm_num)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2U hc) hP) hB2

private theorem lintegral_majorant_lt_top (j : ℕ) (B' : ℝ) (hB' : 0 < B') :
    ∫⁻ ω, majorant j B' ω ∂chartMeasure < ⊤ := by

  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : ℝ, ∀ θ : ℝ, |(Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ)| ≤ U₀ := by
    have hc : IsCompact (Set.Icc (-1 : ℝ) 1) := isCompact_Icc
    obtain ⟨U₀, hU₀⟩ := hc.exists_bound_of_continuousOn (Polynomial.continuous (Chebyshev.U ℝ (j : ℤ))).continuousOn
    refine ⟨U₀, fun θ => ?_⟩
    have h := hU₀ (Real.cos θ) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    rwa [Real.norm_eq_abs] at h

  have hMmeas : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (radiusConst j B' x.1) *
      (if |Real.sin x.1| / B' ≤ x.2 then ENNReal.ofReal (x.2 ^ (-3 : ℝ)) else 0) := by
    have h0 : Measurable fun x : ℝ × ℝ => radiusConst j B' x.1 := by
      unfold radiusConst angleWeight
      have hU : Measurable fun x : ℝ × ℝ => (Chebyshev.U ℝ (j : ℤ)).eval (Real.cos x.1) :=
        (Polynomial.continuous _).measurable.comp (Real.measurable_cos.comp measurable_fst)
      fun_prop
    have h1 : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (radiusConst j B' x.1) := ENNReal.measurable_ofReal.comp h0
    have hs : MeasurableSet {x : ℝ × ℝ | |Real.sin x.1| / B' ≤ x.2} := measurableSet_le (by fun_prop) measurable_snd
    have h2 : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (x.2 ^ (-3 : ℝ)) :=
      ENNReal.measurable_ofReal.comp (measurable_snd.pow_const (-3 : ℝ))
    exact h1.mul (Measurable.ite hs h2 measurable_const)
  have hae : ∀ᵐ x ∂radiusMeasure,
      ENNReal.ofReal (radiusFactor j B' x) * (volume (shearSet B' x.2) * boxMeasure Set.univ) ≤
        ENNReal.ofReal (radiusConst j B' x.1) *
            (if |Real.sin x.1| / B' ≤ x.2 then ENNReal.ofReal (x.2 ^ (-3 : ℝ)) else 0) * boxMeasure Set.univ := by
    filter_upwards [ae_radius_pos] with x hρ
    by_cases hmem : x ∈ radiusSet B'
    · have ha : |Real.sin x.1| / B' ≤ x.2 := by
        rw [div_le_iff₀ hB', mul_comm]
        exact (mem_radiusSet.mp hmem).1
      have hrF : 0 ≤ radiusFactor j B' x := by
        unfold radiusFactor
        rw [if_pos hmem]
        exact mul_nonneg (angleWeight_nonneg j x.1) (inv_pos.mpr hρ).le
      rw [if_pos ha, ← ENNReal.ofReal_mul (radiusConst_nonneg j B' x.1)]
      calc ENNReal.ofReal (radiusFactor j B' x) * (volume (shearSet B' x.2) * boxMeasure Set.univ)
          ≤ ENNReal.ofReal (radiusFactor j B' x) *
              (ENNReal.ofReal (Real.pi * ((x.2⁻¹ + B') * x.2⁻¹)) * boxMeasure Set.univ) :=
            mul_le_mul_right (mul_le_mul_left (volume_shearSet_le B' x.2 hB'.le hρ) _) _
        _ = ENNReal.ofReal (radiusFactor j B' x * (Real.pi * ((x.2⁻¹ + B') * x.2⁻¹))) * boxMeasure Set.univ := by
            rw [← mul_assoc, ENNReal.ofReal_mul hrF]
        _ ≤ ENNReal.ofReal (radiusConst j B' x.1 * x.2 ^ (-3 : ℝ)) * boxMeasure Set.univ :=
            mul_le_mul_left (ENNReal.ofReal_le_ofReal (radiusFactor_mul_le j B' x hρ hmem)) _
    · have h0 : radiusFactor j B' x = 0 := by
        unfold radiusFactor
        exact if_neg hmem
      rw [h0, ENNReal.ofReal_zero, zero_mul]
      exact zero_le
  unfold chartMeasure
  rw [lintegral_prod _ (measurable_majorant j B').aemeasurable]
  simp only [lintegral_majorant_shearBox]
  refine lt_of_le_of_lt (lintegral_mono_ae hae) ?_
  rw [lintegral_mul_const _ hMmeas]
  refine ENNReal.mul_lt_top ?_ (measure_lt_top _ _)
  unfold radiusMeasure
  rw [lintegral_prod _ hMmeas.aemeasurable]
  refine lt_of_le_of_lt (lintegral_mono fun θ => lintegral_radius_le j B' hB' θ U₀ (hU₀ θ)) ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

private theorem slab_integrable (j : ℕ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (B : ℝ) :
    Integrable (fun ω : Chart => if ‖entAt ε ω‖ ≤ B then |modeScalar j ω| else 0) chartMeasure := by
  refine ⟨(measurable_slabFn j ε B).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) (lintegral_majorant_lt_top j (4 * max B 0 + 1) (by positivity))
  filter_upwards [ae_chart_pos_radius] with ω hω
  exact enorm_slabFn_le_majorant j ε hε B ω hω

section IntegralFamily

variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (sc : Ω → ℝ) (X : Ω → Ent)
variable (Q : Type) [NormedAddCommGroup Q]

private theorem exists_bound_of_family {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : Ent × Q → F)
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ M B₀ : ℝ, ∀ (c : ℝ) (x : Ent) (y : Q), ‖c • Ψ (x, y)‖ ≤ M * (if ‖x‖ ≤ B₀ then |c| else 0) := by
  obtain ⟨M, hM⟩ := hΨ.bounded_above_of_compact_support hΨc
  obtain ⟨B₀, hB₀⟩ := (hΨc : IsCompact (tsupport Ψ)).isBounded.exists_norm_le
  refine ⟨M, B₀, fun c x y => ?_⟩
  split_ifs with hx
  · rw [norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM (x, y)) (abs_nonneg c)
  · have hz : Ψ (x, y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have h1 := hB₀ (x, y) hmem
      have h2 : ‖x‖ ≤ ‖((x, y) : Ent × Q)‖ := norm_fst_le (x, y)
      exact hx (h2.trans h1)
    simp [hz]

variable (hsc : AEStronglyMeasurable sc μ) (hX : AEStronglyMeasurable X μ)
  (hslab : ∀ B : ℝ, Integrable (fun ω => if ‖X ω‖ ≤ B then |sc ω| else 0) μ)

include hsc hX in
private theorem integrand_aestronglyMeasurable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : Ent × Q → F)
    (hΨ : Continuous Ψ) (y : Q) : AEStronglyMeasurable (fun ω => sc ω • Ψ (X ω, y)) μ :=
  hsc.smul (hΨ.comp_aestronglyMeasurable (hX.prodMk aestronglyMeasurable_const))

include hsc hX hslab in
private theorem integrand_integrable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : Ent × Q → F)
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) (y : Q) : Integrable (fun ω => sc ω • Ψ (X ω, y)) μ := by
  obtain ⟨M, B₀, hMB⟩ := exists_bound_of_family Q Ψ hΨ hΨc
  refine ((hslab B₀).const_mul M).mono' (integrand_aestronglyMeasurable μ sc X Q hsc hX Ψ hΨ y) ?_
  exact Filter.Eventually.of_forall fun ω => hMB (sc ω) (X ω) y

variable [NormedSpace ℝ Q]

private def partialQ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : Ent × Q → F) (z : Ent × Q) : Q →L[ℝ] F :=
  (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inr ℝ Ent Q)

private theorem partialQ_contDiff {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : Ent × Q → F)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) : ContDiff ℝ (⊤ : ℕ∞) (partialQ Q Ψ) := by
  show ContDiff ℝ (⊤ : ℕ∞) fun z => (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inr ℝ Ent Q)
  exact (contDiff_infty_iff_fderiv.1 hΨ).2.clm_comp contDiff_const

private theorem partialQ_hasCompactSupport {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : Ent × Q → F)
    (hΨc : HasCompactSupport Ψ) : HasCompactSupport (partialQ Q Ψ) := by
  have h : HasCompactSupport
      ((fun L : Ent × Q →L[ℝ] F => L.comp (ContinuousLinearMap.inr ℝ Ent Q)) ∘ fderiv ℝ Ψ) :=
    (hΨc.fderiv ℝ).comp_left (by simp)
  exact h

private theorem partialQ_hasFDerivAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : Ent × Q → F)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (c : ℝ) (x : Ent) (y : Q) :
    HasFDerivAt (fun y : Q => c • Ψ (x, y)) (c • partialQ Q Ψ (x, y)) y := by
  have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (x, y)) (x, y) := ((contDiff_infty_iff_fderiv.1 hΨ).1 (x, y)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Q => (x, y)) (ContinuousLinearMap.inr ℝ Ent Q) y := hasFDerivAt_prodMk_right x y
  exact (h1.comp y h2).const_smul c

include hsc hX hslab in

private theorem integralFamily_hasFDerivAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Ψ : Ent × Q → F) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) (y₀ : Q) :
    HasFDerivAt (fun y : Q => ∫ ω, sc ω • Ψ (X ω, y) ∂μ) (∫ ω, sc ω • partialQ Q Ψ (X ω, y₀) ∂μ) y₀ := by
  have hΨ' := partialQ_contDiff Q Ψ hΨ
  have hΨ'c := partialQ_hasCompactSupport Q Ψ hΨc
  obtain ⟨M, B₀, hMB⟩ := exists_bound_of_family Q (partialQ Q Ψ) hΨ'.continuous hΨ'c
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun y ω => sc ω • partialQ Q Ψ (X ω, y))
    Filter.univ_mem ?_ ?_ ?_ ?_ ((hslab B₀).const_mul M) ?_
  · exact Filter.Eventually.of_forall fun y => integrand_aestronglyMeasurable μ sc X Q hsc hX Ψ hΨ.continuous y
  · exact integrand_integrable μ sc X Q hsc hX hslab Ψ hΨ.continuous hΨc y₀
  · exact integrand_aestronglyMeasurable μ sc X Q hsc hX (partialQ Q Ψ) hΨ'.continuous y₀
  · exact Filter.Eventually.of_forall fun ω y _ => hMB (sc ω) (X ω) y
  · exact Filter.Eventually.of_forall fun ω y _ => partialQ_hasFDerivAt Q Ψ hΨ (sc ω) (X ω) y

include hsc hX hslab in

private theorem contDiff_integral_family_nat (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Ψ : Ent × Q → F),
      ContDiff ℝ (⊤ : ℕ∞) Ψ → HasCompactSupport Ψ → ContDiff ℝ n (fun y : Q => ∫ ω, sc ω • Ψ (X ω, y) ∂μ) := by
  induction n with
  | zero =>
    intro F _ _ _ Ψ hΨ hΨc
    have key : Continuous fun y : Q => ∫ ω, sc ω • Ψ (X ω, y) ∂μ :=
      continuous_iff_continuousAt.2 fun y₀ =>
        (integralFamily_hasFDerivAt μ sc X Q hsc hX hslab Ψ hΨ hΨc y₀).continuousAt
    exact_mod_cast (contDiff_zero.2 key : ContDiff ℝ 0 fun y : Q => ∫ ω, sc ω • Ψ (X ω, y) ∂μ)
  | succ n ih =>
    intro F _ _ _ Ψ hΨ hΨc
    have key := (contDiff_succ_iff_hasFDerivAt (n := n)).2 ⟨fun y : Q => ∫ ω, sc ω • partialQ Q Ψ (X ω, y) ∂μ,
      ih (Q →L[ℝ] F) (partialQ Q Ψ) (partialQ_contDiff Q Ψ hΨ) (partialQ_hasCompactSupport Q Ψ hΨc),
      fun y₀ => integralFamily_hasFDerivAt μ sc X Q hsc hX hslab Ψ hΨ hΨc y₀⟩
    exact_mod_cast key

include hsc hX hslab in
private theorem contDiff_integral_family (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Ψ : Ent × Q → F) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Q => ∫ ω, sc ω • Ψ (X ω, y) ∂μ) :=
  contDiff_infty.2 fun n => contDiff_integral_family_nat μ sc X Q hsc hX hslab n F Ψ hΨ hΨc

end IntegralFamily

private theorem hasCompactSupport_rescale {P : Type} [NormedAddCommGroup P] (Φ : Ent × P → ℂ)
    (hΦc : HasCompactSupport Φ) (s : ℝ) (hs : s ≠ 0) : HasCompactSupport fun z : Ent × P => Φ (s • z.1, z.2) := by
  have hK : IsCompact ((fun w : Ent × P => (s⁻¹ • w.1, w.2)) '' tsupport Φ) :=
    (hΦc : IsCompact (tsupport Φ)).image ((continuous_const.fun_smul continuous_fst).prodMk continuous_snd)
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro z hz
  rw [Function.mem_support] at hz
  have hmem : ((s • z.1, z.2) : Ent × P) ∈ tsupport Φ := subset_tsupport Φ (Function.mem_support.mpr hz)
  refine ⟨(s • z.1, z.2), hmem, ?_⟩
  show ((s⁻¹ • (s • z.1), z.2) : Ent × P) = z
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul]

private theorem rescale_contDiffAt (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (z : Ent × (ℝ × P))
    (hz : 0 < z.2.1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z : Ent × (ℝ × P) => (Real.sqrt z.2.1 • z.1, z.2.2)) z := by
  have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : Ent × (ℝ × P) => Real.sqrt z.2.1) z :=
    (Real.contDiffAt_sqrt hz.ne').comp z contDiffAt_snd.fst
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : Ent × (ℝ × P) => Real.sqrt z.2.1 • z.1) z := hsqrt.smul contDiffAt_fst
  exact h1.prodMk contDiffAt_snd.snd

private theorem rescaled_contDiff (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : Ent × P → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Set.Ioi 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Ent × (ℝ × P) => χ z.2.1 • Φ (Real.sqrt z.2.1 • z.1, z.2.2)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : 0 < z.2.1
  · have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : Ent × (ℝ × P) => χ z.2.1) z := hχ.contDiffAt.comp z contDiffAt_snd.fst
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : Ent × (ℝ × P) => Φ (Real.sqrt z.2.1 • z.1, z.2.2)) z :=
      hΦ.contDiffAt.comp z (rescale_contDiffAt P z hz)
    exact h1.smul h2
  ·
    have hopen : IsOpen ((fun w : Ent × (ℝ × P) => w.2.1) ⁻¹' (tsupport χ)ᶜ) :=
      (isClosed_tsupport χ).isOpen_compl.preimage continuous_snd.fst
    have hmem : z ∈ (fun w : Ent × (ℝ × P) => w.2.1) ⁻¹' (tsupport χ)ᶜ := fun h => hz (hχs h)
    have hev : (fun z : Ent × (ℝ × P) => χ z.2.1 • Φ (Real.sqrt z.2.1 • z.1, z.2.2)) =ᶠ[nhds z]
        fun _ => (0 : ℂ) := by
      filter_upwards [hopen.mem_nhds hmem] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
    exact contDiffAt_const.congr_of_eventuallyEq hev

private theorem rescaled_hasCompactSupport (P : Type) [NormedAddCommGroup P] (Φ : Ent × P → ℂ)
    (hΦc : HasCompactSupport Φ) (χ : ℝ → ℝ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Set.Ioi 0) :
    HasCompactSupport (fun z : Ent × (ℝ × P) => χ z.2.1 • Φ (Real.sqrt z.2.1 • z.1, z.2.2)) := by
  have hScomp : IsCompact (tsupport Φ ×ˢ tsupport χ) :=
    (hΦc : IsCompact (tsupport Φ)).prod (hχc : IsCompact (tsupport χ))
  have hm : ContinuousOn (fun w : (Ent × P) × ℝ => (((Real.sqrt w.2)⁻¹ • w.1.1 : Ent), (w.2, w.1.2)))
      (tsupport Φ ×ˢ tsupport χ) := by
    have hsq : ContinuousOn (fun w : (Ent × P) × ℝ => (Real.sqrt w.2)⁻¹) (tsupport Φ ×ˢ tsupport χ) := by
      refine (Real.continuous_sqrt.comp continuous_snd).continuousOn.inv₀ ?_
      intro w hw
      exact (Real.sqrt_pos.mpr (hχs hw.2)).ne'
    exact (hsq.smul continuous_fst.fst.continuousOn).prodMk
      (continuous_snd.continuousOn.prodMk continuous_fst.snd.continuousOn)
  have hK : IsCompact ((fun w : (Ent × P) × ℝ => (((Real.sqrt w.2)⁻¹ • w.1.1 : Ent), (w.2, w.1.2))) ''
      (tsupport Φ ×ˢ tsupport χ)) := hScomp.image_of_continuousOn hm
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro z hz
  rw [Function.mem_support] at hz
  have hχz : z.2.1 ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr fun h => hz (by simp [h]))
  have hΦz : ((Real.sqrt z.2.1 • z.1, z.2.2) : Ent × P) ∈ tsupport Φ :=
    subset_tsupport Φ (Function.mem_support.mpr fun h => hz (by simp [h]))
  have hr : 0 < z.2.1 := hχs hχz
  refine ⟨((Real.sqrt z.2.1 • z.1, z.2.2), z.2.1), ⟨hΦz, hχz⟩, ?_⟩
  show (((Real.sqrt z.2.1)⁻¹ • (Real.sqrt z.2.1 • z.1) : Ent), (z.2.1, z.2.2)) = z
  rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr hr).ne', one_smul]

private def modeFun (P : Type) [NormedAddCommGroup P] (Φ : Ent × P → ℂ) (j : ℕ) (q : ℝ × P) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2)) q.1 θ *
      (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)

private theorem unitaryElt_val (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = kMat ψ η ξ₁ ξ₂ := rfl

private theorem unitaryElt_inv_val (ψ η ξ₁ ξ₂ : ℝ) :
    (((unitaryElt ψ η ξ₁ ξ₂)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = kInv ψ η ξ₁ ξ₂ := by
  refine Units.inv_eq_of_mul_eq_one_left ?_
  rw [unitaryElt_val]
  exact kInv_mul_kMat ψ η ξ₁ ξ₂

private theorem conjEntries_val (k : GL (Fin 2) ℂ) :
    ((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) :=
  rfl

private theorem conjEntries_unitaryElt_val (ψ η ξ₁ ξ₂ : ℝ) :
    ((conjEntries (unitaryElt ψ η ξ₁ ξ₂) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = kBar ψ η ξ₁ ξ₂ := rfl

private theorem twistedEllipticElt_val (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    ((twistedEllipticElt r θ ρ u hr hρ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (Real.sqrt r : ℂ) • nMat θ ρ u := by
  unfold twistedEllipticElt nMat
  ext i k
  fin_cases i <;> fin_cases k <;> rfl

private theorem entries_eq (r θ ρ : ℝ) (u : ℂ) (ψ η ξ₁ ξ₂ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) :
    Matrix.of.symm (((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * twistedEllipticElt r θ ρ u hr hρ * conjEntries (unitaryElt ψ η ξ₁ ξ₂) :
        GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Real.sqrt r • ent₁ θ ρ u ψ η ξ₁ ξ₂ := by
  rw [Units.val_mul, Units.val_mul, unitaryElt_inv_val, conjEntries_unitaryElt_val, twistedEllipticElt_val,
    Matrix.mul_smul, Matrix.smul_mul]
  funext i k
  simp only [ent₁, Matrix.of_symm_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Complex.real_smul]

private theorem det_nMat (θ ρ : ℝ) (u : ℂ) (hρ : 0 < ρ) : Matrix.det (nMat θ ρ u) = -1 := by
  rw [nMat, Matrix.det_fin_two_of]
  have hE : Complex.exp (θ / 2 * Complex.I) * Complex.exp (-(θ / 2 * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hρi : (ρ : ℂ)⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ'
  have hu : (starRingEnd ℂ) u * u = (Complex.normSq u : ℂ) := Complex.normSq_eq_conj_mul_self.symm
  linear_combination (-(ρ : ℂ) ^ 2 * Complex.exp (-(θ / 2 * Complex.I)) ^ 2) * hu -
    (Complex.exp (θ / 2 * Complex.I) * Complex.exp (-(θ / 2 * Complex.I))) * hρi - hE

private theorem norm_det_eq (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) (k : GL (Fin 2) ℂ) :
    ‖Matrix.det ((k⁻¹ * twistedEllipticElt r θ ρ u hr hρ * conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)‖ =
      r := by
  have hdet : Matrix.det ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  have hconj : Matrix.det ((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (starRingEnd ℂ) (Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [conjEntries_val, RingHom.map_det]; rfl
  have hM : Matrix.det ((twistedEllipticElt r θ ρ u hr hρ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -(r : ℂ) := by
    rw [twistedEllipticElt_val, Matrix.det_smul, det_nMat θ ρ u hρ, Fintype.card_fin]
    have : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by exact_mod_cast Real.sq_sqrt hr.le
    rw [this]; ring
  have hn : ‖Matrix.det ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)‖ *
      ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
    rw [← norm_mul, hdet, norm_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hM, hconj, norm_mul, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_conj]
  calc ‖Matrix.det ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)‖ * r * ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖
      = ‖Matrix.det ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)‖ * ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ *
          r := by ring
    _ = r := by rw [hn, one_mul]

private theorem unitaryAverage_zero : unitaryAverage (fun _ => (0 : ℂ)) = 0 := by
  simp [unitaryAverage]

private theorem transform_eq_zero_of_slice (φ : GL (Fin 2) ℂ → ℂ) (r θ : ℝ)
    (hφ : ∀ g : GL (Fin 2) ℂ, ‖Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ)‖ = r → φ g = 0) :
    twistedEllipticTransform φ r θ = 0 := by
  unfold twistedEllipticTransform
  by_cases hr : 0 < r
  · rw [dif_pos hr]
    have h : ∀ (θ' ρ : ℝ) (hρ : 0 < ρ) (u : ℂ) (k : GL (Fin 2) ℂ),
        φ (k⁻¹ * twistedEllipticElt r θ' ρ u hr hρ * conjEntries k) = 0 :=
      fun θ' ρ hρ u k => hφ _ (norm_det_eq r θ' ρ u hr hρ k)
    simp [h, unitaryAverage_zero]
  · rw [dif_neg hr]

private def detNorm (P : Type) (q : Ent × P) : ℝ := ‖Matrix.det (Matrix.of q.1)‖

private theorem continuous_detNorm (P : Type) [TopologicalSpace P] : Continuous (detNorm P) := by
  have h : Continuous fun q : Ent × P => Matrix.of q.1 := by
    refine continuous_matrix fun i k => ?_
    simp only [Matrix.of_apply]
    exact (continuous_apply k).comp ((continuous_apply i).comp continuous_fst)
  exact h.matrix_det.norm

private theorem transform_eq_zero_outside (P : Type) [NormedAddCommGroup P] (Φ : Ent × P → ℂ)
    (hΦc : HasCompactSupport Φ) (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ∃ c C : ℝ, 0 < c ∧ ∃ K : Set P, IsCompact K ∧ ∀ (r θ : ℝ) (p : P), (r < c ∨ C < r ∨ p ∉ K) →
      twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r θ = 0 := by
  have hcomp : IsCompact (tsupport Φ) := hΦc
  rcases (tsupport Φ).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, 1, one_pos, ∅, isCompact_empty, fun r θ p _ => ?_⟩
    apply transform_eq_zero_of_slice
    intro g _
    show Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p) = 0
    apply image_eq_zero_of_notMem_tsupport
    rw [hemp]
    exact Set.notMem_empty _
  · obtain ⟨q₀, hq₀, hmin⟩ := hcomp.exists_isMinOn hne (continuous_detNorm P).continuousOn
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn (continuous_detNorm P).continuousOn
    have hc : 0 < detNorm P q₀ := by
      have hunit : IsUnit (Matrix.det (Matrix.of q₀.1)) := hΦinv hq₀
      show 0 < ‖Matrix.det (Matrix.of q₀.1)‖
      exact norm_pos_iff.mpr hunit.ne_zero
    refine ⟨detNorm P q₀, C, hc, Prod.snd '' tsupport Φ, hcomp.image continuous_snd, fun r θ p hout => ?_⟩
    apply transform_eq_zero_of_slice
    intro g hg
    show Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p) = 0
    by_contra hne'
    have hmem : ((Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p) : Ent × P) ∈ tsupport Φ :=
      subset_tsupport Φ (Function.mem_support.mpr hne')
    have hval : detNorm P (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p) = r := by
      show ‖Matrix.det (Matrix.of (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ)))‖ = r
      rw [Equiv.apply_symm_apply]
      exact hg
    rcases hout with h | h | h
    · have h1 := isMinOn_iff.mp hmin _ hmem
      rw [hval] at h1
      exact absurd h1 (not_le.mpr h)
    · have h1 := hC _ hmem
      rw [Real.norm_eq_abs] at h1
      have h2 := (le_abs_self _).trans h1
      rw [hval] at h2
      exact absurd h2 (not_le.mpr h)
    · exact h ⟨_, hmem, rfl⟩

private def thetaWeight (j : ℕ) (θ : ℝ) : ℝ := 4 * Real.sin θ ^ 2 * (Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ)

private theorem modeScalar_eq (j : ℕ) (ω : Chart) :
    modeScalar j ω =
      thetaWeight j ω.1.1 * ω.1.2⁻¹ * (1 / (4 * Real.pi ^ 3)) * (Real.sin ω.2.2.2.1 * Real.cos ω.2.2.2.1) := rfl

private theorem integrable_of_continuous_of_bounded {α : Type} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℂ) (hf : Continuous f) (M : ℝ)
    (hM : ∀ x, ‖f x‖ ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall hM)

private theorem boxMeasure_integral_eq (g : Box → ℂ) (hg : Continuous g) (M : ℝ) (hM : ∀ b, ‖g b‖ ≤ M) :
    ∫ b, g b ∂boxMeasure =
      ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), g (ψ, η, ξ₁, ξ₂) := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hπ2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  simp only [intervalIntegral.integral_of_le h2π, intervalIntegral.integral_of_le hπ2]
  have h₁ : Integrable g boxMeasure := integrable_of_continuous_of_bounded boxMeasure g hg M hM
  unfold boxMeasure at h₁ ⊢
  rw [integral_prod _ h₁]
  congr 1
  funext ψ
  have h₂ : Integrable (fun y => g (ψ, y)) boxMeasure₂ :=
    integrable_of_continuous_of_bounded boxMeasure₂ _ (hg.comp (continuous_const.prodMk continuous_id)) M
      fun y => hM _
  unfold boxMeasure₂ at h₂ ⊢
  rw [integral_prod _ h₂]
  congr 1
  funext η
  have h₃ : Integrable (fun y => g (ψ, η, y)) boxMeasure₃ :=
    integrable_of_continuous_of_bounded boxMeasure₃ _
      (hg.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))) M fun y => hM _
  unfold boxMeasure₃ at h₃ ⊢
  rw [integral_prod _ h₃]

private theorem continuous_ent₁_angles (θ' ρ : ℝ) (u : ℂ) :
    Continuous fun b : Box => ent₁ θ' ρ u b.1 b.2.1 b.2.2.1 b.2.2.2 := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have hexp : Continuous fun z : ℂ => Complex.exp z := Complex.continuous_exp
  have hconj : Continuous fun z : ℂ => (starRingEnd ℂ) z := Complex.continuous_conj
  have hre : Continuous fun x : ℝ => (x : ℂ) := Complex.continuous_ofReal
  fin_cases i <;> fin_cases k <;>
    simp only [ent₁, kInv, nMat, kBar, kMat, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_symm_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one,
      Fin.isValue] <;>
    fun_prop

private theorem unitaryAverage_eq_boxIntegral (P : Type) [NormedAddCommGroup P] (Φ : Ent × P → ℂ) (hΦ : Continuous Φ)
    (M : ℝ) (hM : ∀ z, ‖Φ z‖ ≤ M) (r θ' ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) (p : P) :
    unitaryAverage (fun k => Φ (Matrix.of.symm ((k⁻¹ * twistedEllipticElt r θ' ρ u hr hρ * conjEntries k :
        GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), p)) =
      (1 / (4 * Real.pi ^ 3) : ℝ) •
        ∫ b, (Real.sin b.2.1 * Real.cos b.2.1) • Φ (Real.sqrt r • ent₁ θ' ρ u b.1 b.2.1 b.2.2.1 b.2.2.2, p)
          ∂boxMeasure := by
  have hg : Continuous fun b : Box =>
      (Real.sin b.2.1 * Real.cos b.2.1) • Φ (Real.sqrt r • ent₁ θ' ρ u b.1 b.2.1 b.2.2.1 b.2.2.2, p) := by
    have h1 : Continuous fun b : Box => Real.sin b.2.1 * Real.cos b.2.1 := by fun_prop
    have h2 : Continuous fun b : Box => Φ (Real.sqrt r • ent₁ θ' ρ u b.1 b.2.1 b.2.2.1 b.2.2.2, p) :=
      hΦ.comp ((continuous_const.fun_smul (continuous_ent₁_angles θ' ρ u)).prodMk continuous_const)
    exact h1.smul h2
  have hgM : ∀ b : Box,
      ‖(Real.sin b.2.1 * Real.cos b.2.1) • Φ (Real.sqrt r • ent₁ θ' ρ u b.1 b.2.1 b.2.2.1 b.2.2.2, p)‖ ≤ M := by
    intro b
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    calc |Real.sin b.2.1| * |Real.cos b.2.1| * ‖Φ (Real.sqrt r • ent₁ θ' ρ u b.1 b.2.1 b.2.2.1 b.2.2.2, p)‖
        ≤ 1 * 1 * M := by
          gcongr
          · exact Real.abs_sin_le_one _
          · exact Real.abs_cos_le_one _
          · exact hM _
      _ = M := by ring
  rw [boxMeasure_integral_eq _ hg M hgM]
  unfold unitaryAverage
  simp only [entries_eq, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_pow, Complex.ofReal_ofNat]

private theorem box_integral_eq (P : Type) [NormedAddCommGroup P] (Φ : Ent × P → ℂ) (hΦ : Continuous Φ) (M : ℝ)
    (hM : ∀ z, ‖Φ z‖ ≤ M) (j : ℕ) (ε r : ℝ) (hr : 0 < r) (p : P) (x : ℝ × ℝ) (hρ : 0 < x.2) (u : ℂ) :
    (∫ b, modeScalar j ((x, (u, b)) : Chart) • Φ (Real.sqrt r • entAt ε ((x, (u, b)) : Chart), p) ∂boxMeasure) =
      (thetaWeight j x.1 * x.2⁻¹) • unitaryAverage (fun k => Φ (Matrix.of.symm
        ((k⁻¹ * twistedEllipticElt r (ε * x.1) x.2 u hr hρ * conjEntries k : GL (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ), p)) := by
  rw [unitaryAverage_eq_boxIntegral P Φ hΦ M hM r (ε * x.1) x.2 u hr hρ p, ← integral_smul, ← integral_smul]
  congr 1
  funext b
  simp only [modeScalar_eq, entAt, mul_smul]

private theorem integrable_of_integrable_const_smul {f : ℂ → ℂ} {c : ℝ} (hc : c ≠ 0)
    (h : Integrable (fun u => c • f u) (volume : Measure ℂ)) : Integrable f (volume : Measure ℂ) :=
  (integrable_smul_iff hc f).mp h

private theorem modeFun_eq_integral (P : Type) [NormedAddCommGroup P] (Φ : Ent × P → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (j : ℕ) (q : ℝ × P) (hq : 0 < q.1) :
    modeFun P Φ j q =
      (∫ ω, modeScalar j ω • Φ (Real.sqrt q.1 • entAt 1 ω, q.2) ∂chartMeasure) +
        ∫ ω, modeScalar j ω • Φ (Real.sqrt q.1 • entAt (-1) ω, q.2) ∂chartMeasure := by
  obtain ⟨M, hM⟩ := hΦ.bounded_above_of_compact_support hΦc

  have hsqrt : Real.sqrt q.1 ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hΨ : Continuous fun z : Ent × P => Φ (Real.sqrt q.1 • z.1, z.2) :=
    hΦ.comp ((continuous_const.fun_smul continuous_fst).prodMk continuous_snd)
  have hΨc : HasCompactSupport fun z : Ent × P => Φ (Real.sqrt q.1 • z.1, z.2) :=
    hasCompactSupport_rescale Φ hΦc (Real.sqrt q.1) hsqrt
  have hf : ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
      Integrable (fun ω : Chart => modeScalar j ω • Φ (Real.sqrt q.1 • entAt ε ω, q.2)) chartMeasure :=
    fun ε hε => integrand_integrable chartMeasure (modeScalar j) (entAt ε) P
      (measurable_modeScalar j).aestronglyMeasurable (measurable_entAt ε).aestronglyMeasurable
      (slab_integrable j ε hε) _ hΨ hΨc q.2
  have hfP := hf 1 (Or.inl rfl)
  have hfM := hf (-1) (Or.inr rfl)

  have hGP := hfP.integral_prod_left
  have hGM := hfM.integral_prod_left
  have hzsecP := Measure.ae_ae_of_ae_prod hfP.prod_right_ae
  have hzsecM := Measure.ae_ae_of_ae_prod hfM.prod_right_ae
  unfold chartMeasure at hfP hfM ⊢
  rw [integral_prod _ hfP, integral_prod _ hfM]
  unfold radiusMeasure at hGP hGM ⊢
  rw [integral_prod _ hGP, integral_prod _ hGM, ← integral_add hGP.integral_prod_left hGM.integral_prod_left]

  unfold modeFun
  rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  refine integral_congr_ae ?_
  filter_upwards [hGP.prod_right_ae, hGM.prod_right_ae, hzsecP, hzsecM] with θ hplus hminus hzP hzM
  rw [← integral_add hplus hminus]

  unfold twistedEllipticTransform
  rw [dif_pos hq]
  have hcast : ∀ X : ℂ, (4 * Real.sin θ ^ 2 : ℂ) * X * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) =
      thetaWeight j θ • X := by
    intro X
    rw [thetaWeight, Complex.real_smul]
    push_cast
    ring
  rw [hcast, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [hzP, hzM, ae_restrict_mem measurableSet_Ioi] with ρ hρzP hρzM hρ
  have hρ' : (0 : ℝ) < ρ := hρ
  simp only [dif_pos hρ']

  have hboxP := hρzP.integral_prod_left
  have hboxM := hρzM.integral_prod_left
  unfold shearBoxMeasure at hρzP hρzM ⊢
  rw [integral_prod _ hρzP, integral_prod _ hρzM]
  simp only [box_integral_eq P Φ hΦ M hM j _ q.1 hq q.2 (θ, ρ) hρ', one_mul, neg_one_mul] at hboxP hboxM ⊢
  by_cases htw : thetaWeight j θ = 0
  · simp [htw]
  · have hc : thetaWeight j θ * ρ⁻¹ ≠ 0 := mul_ne_zero htw (inv_ne_zero hρ'.ne')
    have hAP := integrable_of_integrable_const_smul hc hboxP
    have hAM := integrable_of_integrable_const_smul hc hboxM
    rw [integral_smul, integral_smul]
    have hinner : ∀ Y : ℂ, (ρ : ℂ)⁻¹ * Y = ρ⁻¹ • Y := by
      intro Y
      rw [Complex.real_smul, Complex.ofReal_inv]
    simp only [hinner]
    rw [integral_smul, integral_add hAP hAM, smul_smul, smul_add]

private theorem modeFun_contDiffAt (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : Ent × P → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (j : ℕ) (q₀ : ℝ × P) (hq₀ : 0 < q₀.1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (modeFun P Φ j) q₀ := by
  have hΦcont : Continuous Φ := hΦ.continuous
  let χ : ContDiffBump q₀.1 := ⟨q₀.1 / 4, q₀.1 / 2, by positivity, by linarith⟩
  have hχs : tsupport (χ : ℝ → ℝ) ⊆ Set.Ioi 0 := by
    rw [χ.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq] at hx
    have hx' := (abs_le.1 hx).1
    have hr : χ.rOut = q₀.1 / 2 := rfl
    show 0 < x
    linarith
  have hΨ := rescaled_contDiff P Φ hΦ χ χ.contDiff hχs
  have hΨc := rescaled_hasCompactSupport P Φ hΦc χ χ.hasCompactSupport hχs
  have h₁ := contDiff_integral_family chartMeasure (modeScalar j) (entAt 1) (ℝ × P)
    (measurable_modeScalar j).aestronglyMeasurable (measurable_entAt 1).aestronglyMeasurable
    (slab_integrable j 1 (Or.inl rfl)) ℂ _ hΨ hΨc
  have h₂ := contDiff_integral_family chartMeasure (modeScalar j) (entAt (-1)) (ℝ × P)
    (measurable_modeScalar j).aestronglyMeasurable (measurable_entAt (-1)).aestronglyMeasurable
    (slab_integrable j (-1) (Or.inr rfl)) ℂ _ hΨ hΨc
  have hev₁ : ∀ᶠ q : ℝ × P in nhds q₀, (χ : ℝ → ℝ) q.1 = 1 :=
    (continuous_fst.continuousAt (x := q₀)).eventually χ.eventuallyEq_one
  have hev₂ : ∀ᶠ q : ℝ × P in nhds q₀, 0 < q.1 := (continuous_fst.continuousAt (x := q₀)).eventually (lt_mem_nhds hq₀)
  refine ((h₁.add h₂).contDiffAt).congr_of_eventuallyEq ?_
  filter_upwards [hev₁, hev₂] with q hχq hq
  rw [modeFun_eq_integral P Φ hΦcont hΦc j q hq]
  simp only [hχq, one_smul]

end TwistedEllipticModes
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_contDiff_integral_twistedEllipticTransform_mul_chebyshevU.TwistedEllipticModes"

open TwistedEllipticModes in

theorem solution
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
        twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2)) q.1 θ *
            (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ∧
      HasCompactSupport (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
        twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2)) q.1 θ *
            (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ∧
      tsupport (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
          twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2)) q.1 θ *
            (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ⊆
        Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set P) := by
  change ContDiff ℝ (⊤ : ℕ∞) (modeFun P Φ j) ∧ HasCompactSupport (modeFun P Φ j) ∧
    tsupport (modeFun P Φ j) ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set P)
  obtain ⟨c, C, hc, K, hK, hzero⟩ := transform_eq_zero_outside P Φ hΦc hΦinv

  have hmode : ∀ q : ℝ × P, (q.1 < c ∨ C < q.1 ∨ q.2 ∉ K) → modeFun P Φ j q = 0 := by
    intro q hq
    have h : ∀ θ : ℝ,
        twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2)) q.1 θ = 0 :=
      fun θ => hzero q.1 θ q.2 hq
    simp only [modeFun, h, zero_mul, intervalIntegral.integral_zero]
  have hsupp : Function.support (modeFun P Φ j) ⊆ Set.Icc c C ×ˢ K := by
    intro q hq
    by_contra hnot
    apply hq
    apply hmode
    by_cases h1 : q.1 < c
    · exact Or.inl h1
    by_cases h2 : C < q.1
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr fun hqK => hnot ⟨⟨not_lt.1 h1, not_lt.1 h2⟩, hqK⟩)
  have hKc : IsCompact (Set.Icc c C ×ˢ K) := isCompact_Icc.prod hK
  have htsupp : tsupport (modeFun P Φ j) ⊆ Set.Icc c C ×ˢ K := closure_minimal hsupp hKc.isClosed
  refine ⟨?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro q₀
    by_cases hq₀ : q₀.1 < c
    · have hopen : IsOpen {q : ℝ × P | q.1 < c} := isOpen_lt continuous_fst continuous_const
      have hev : ∀ᶠ q : ℝ × P in nhds q₀, modeFun P Φ j q = (fun _ : ℝ × P => (0 : ℂ)) q := by
        filter_upwards [hopen.mem_nhds hq₀] with q hq
        exact hmode q (Or.inl hq)
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact modeFun_contDiffAt P Φ hΦ hΦc j q₀ (lt_of_lt_of_le hc (not_lt.1 hq₀))
  · exact hKc.of_isClosed_subset (isClosed_tsupport _) htsupp
  · refine htsupp.trans (Set.prod_mono (fun r hr => ?_) (Set.subset_univ _))
    exact lt_of_lt_of_le hc hr.1

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_contDiff_integral_twistedEllipticTransform_mul_chebyshevU.TwistedEllipticModes"

end S_AutomorphicForm_GL2Twisted_contDiff_integral_twistedEllipticTransform_mul_chebyshevU
end P2MW
export P2MW.S_AutomorphicForm_GL2Twisted_contDiff_integral_twistedEllipticTransform_mul_chebyshevU (solution)
