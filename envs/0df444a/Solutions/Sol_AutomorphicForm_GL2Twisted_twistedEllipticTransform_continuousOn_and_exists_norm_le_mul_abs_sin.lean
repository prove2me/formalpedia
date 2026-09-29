-- Prove2me | solution 1 for AutomorphicForm.GL2Twisted.twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8c0c2302-8779-5331-82b3-e7b2edace39f

import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Twisted_twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Twisted

noncomputable section

namespace TwistedEllipticContinuity

private abbrev Ent : Type := Fin 2 → Fin 2 → ℂ

private abbrev Box : Type := ℝ × ℝ × ℝ × ℝ

private def boxMeasure₃ : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod
    ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))

private def boxMeasure₂ : Measure (ℝ × ℝ × ℝ) :=
  ((volume : Measure ℝ).restrict (Set.Ioc 0 (Real.pi / 2))).prod boxMeasure₃

private def boxMeasure : Measure Box := ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod boxMeasure₂

private def shearBoxMeasure : Measure (ℂ × Box) := (volume : Measure ℂ).prod boxMeasure

private abbrev Slab : Type := ℝ × (ℂ × Box)

private def slabMeasure : Measure Slab := ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod shearBoxMeasure

private scoped instance : IsFiniteMeasure boxMeasure₃ := by unfold boxMeasure₃; infer_instance
private scoped instance : IsFiniteMeasure boxMeasure₂ := by unfold boxMeasure₂; infer_instance
private scoped instance : IsFiniteMeasure boxMeasure := by unfold boxMeasure; infer_instance
private scoped instance : SFinite shearBoxMeasure := by unfold shearBoxMeasure; infer_instance
private scoped instance : SFinite slabMeasure := by unfold slabMeasure; infer_instance

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

private def entAt (θ ε : ℝ) (ω : Slab) : Ent :=
  ent₁ (ε * θ) ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2

private def scal (θ : ℝ) (ω : Slab) : ℝ :=
  4 * Real.sin θ ^ 2 * ω.1⁻¹ * (1 / (4 * Real.pi ^ 3)) * (Real.sin ω.2.2.2.1 * Real.cos ω.2.2.2.1)

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
    ρ ≤ B' ∧ |Real.sin θ| ≤ B' * ρ ∧ |Complex.normSq u * ρ - ρ⁻¹ * Real.cos θ| ≤ B' := by
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
    have h3 := abs_le_of_sq_le_sq' h2 hB'
    show |y - x * Real.cos θ| ≤ B'
    rw [abs_sub_comm]
    exact abs_le.mpr h3

private theorem measurable_entAt (θ ε : ℝ) : Measurable (entAt θ ε) := by
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

private theorem measurable_scal (θ : ℝ) : Measurable (scal θ) := by
  unfold scal
  fun_prop

private theorem measurable_slabFn (θ ε B : ℝ) :
    Measurable fun ω : Slab => if ‖entAt θ ε ω‖ ≤ B then |scal θ ω| else 0 := by
  have habs : Measurable fun ω : Slab => |scal θ ω| := by
    have h := measurable_scal θ
    fun_prop
  exact Measurable.ite (measurableSet_le (measurable_entAt θ ε).norm measurable_const) habs measurable_const

private theorem abs_scal_le (θ : ℝ) (ω : Slab) (hρ : 0 < ω.1) :
    |scal θ ω| ≤ Real.sin θ ^ 2 / Real.pi ^ 3 * ω.1⁻¹ := by
  unfold scal
  have h1 : |Real.sin ω.2.2.2.1 * Real.cos ω.2.2.2.1| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _)
  have hinv : 0 < ω.1⁻¹ := inv_pos.mpr hρ
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.sin θ ^ 2), abs_of_pos hinv,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (4 * Real.pi ^ 3))]
  calc 4 * Real.sin θ ^ 2 * ω.1⁻¹ * (1 / (4 * Real.pi ^ 3)) * |Real.sin ω.2.2.2.1 * Real.cos ω.2.2.2.1|
      ≤ 4 * Real.sin θ ^ 2 * ω.1⁻¹ * (1 / (4 * Real.pi ^ 3)) * 1 := by gcongr
    _ = Real.sin θ ^ 2 / Real.pi ^ 3 * ω.1⁻¹ := by ring

private def slabSet (θ B' : ℝ) : Set Slab :=
  {ω | ω.1 ≤ B' ∧ |Real.sin θ| ≤ B' * ω.1 ∧ |Complex.normSq ω.2.1 * ω.1 - ω.1⁻¹ * Real.cos θ| ≤ B'}

private theorem mem_slabSet {θ B' : ℝ} {ω : Slab} :
    ω ∈ slabSet θ B' ↔ ω.1 ≤ B' ∧ |Real.sin θ| ≤ B' * ω.1 ∧ |Complex.normSq ω.2.1 * ω.1 - ω.1⁻¹ * Real.cos θ| ≤ B' :=
  Iff.rfl

private theorem measurableSet_slabSet (θ B' : ℝ) : MeasurableSet (slabSet θ B') := by
  have hnsq : Measurable fun ω : Slab => Complex.normSq ω.2.1 :=
    Complex.continuous_normSq.measurable.comp measurable_snd.fst
  have h1 : MeasurableSet {ω : Slab | ω.1 ≤ B'} := measurableSet_le measurable_fst measurable_const
  have h2 : MeasurableSet {ω : Slab | |Real.sin θ| ≤ B' * ω.1} := measurableSet_le measurable_const (by fun_prop)
  have h3 : MeasurableSet {ω : Slab | |Complex.normSq ω.2.1 * ω.1 - ω.1⁻¹ * Real.cos θ| ≤ B'} :=
    measurableSet_le (by fun_prop) measurable_const
  exact h1.inter (h2.inter h3)

private def annulus (θ ρ B' : ℝ) : Set ℂ := {u | |Complex.normSq u * ρ - ρ⁻¹ * Real.cos θ| ≤ B'}

private theorem measurableSet_annulus (θ ρ B' : ℝ) : MeasurableSet (annulus θ ρ B') :=
  measurableSet_le (by have := Complex.continuous_normSq.measurable; fun_prop) measurable_const

private theorem volume_annulus_le (θ ρ B' : ℝ) (hρ : 0 < ρ) (hB' : 0 ≤ B') :
    volume (annulus θ ρ B') ≤ ENNReal.ofReal (2 * Real.pi * B' / ρ) := by

  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (ρ⁻¹ * Real.cos θ - B') / ρ := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (ρ⁻¹ * Real.cos θ + B') / ρ := ⟨_, rfl⟩
  have hβα : β - α = 2 * B' / ρ := by
    rw [hα, hβ, ← sub_div]
    congr 1
    ring
  have hαβ : α ≤ β := by
    have h0 : 0 ≤ 2 * B' / ρ := by positivity
    linarith
  have hmem : ∀ u ∈ annulus θ ρ B', α ≤ Complex.normSq u ∧ Complex.normSq u ≤ β := by
    intro u hu
    have hu' : |Complex.normSq u * ρ - ρ⁻¹ * Real.cos θ| ≤ B' := hu
    obtain ⟨h1, h2⟩ := abs_le.mp hu'
    rw [hα, hβ]
    constructor
    · rw [div_le_iff₀ hρ]
      linarith
    · rw [le_div_iff₀ hρ]
      linarith

  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : ℝ, α₀ = max α 0 := ⟨_, rfl⟩
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : ℝ, β₀ = max β 0 := ⟨_, rfl⟩
  have hα₀0 : 0 ≤ α₀ := by rw [hα₀]; exact le_max_right _ _
  have hβ₀0 : 0 ≤ β₀ := by rw [hβ₀]; exact le_max_right _ _
  have hαα₀ : α ≤ α₀ := by rw [hα₀]; exact le_max_left _ _
  have hα₀β₀ : α₀ ≤ β₀ := by rw [hα₀, hβ₀]; exact max_le_max hαβ le_rfl
  have hsub : annulus θ ρ B' ⊆ Metric.closedBall (0 : ℂ) (Real.sqrt β₀) \ Metric.ball (0 : ℂ) (Real.sqrt α₀) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hmem u hu
    have hn : ‖u‖ ^ 2 = Complex.normSq u := Complex.sq_norm u
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hsq : ‖u‖ ^ 2 ≤ β₀ := by
        rw [hn, hβ₀]
        exact h2.trans (le_max_left _ _)
      have habs := Real.abs_le_sqrt hsq
      rwa [abs_of_nonneg (norm_nonneg u)] at habs
    · rw [Metric.mem_ball, dist_zero_right, not_lt]
      have h3 : α₀ ≤ ‖u‖ ^ 2 := by
        rw [hn, hα₀]
        exact max_le h1 (Complex.normSq_nonneg u)
      calc Real.sqrt α₀ ≤ Real.sqrt (‖u‖ ^ 2) := Real.sqrt_le_sqrt h3
        _ = ‖u‖ := Real.sqrt_sq (norm_nonneg u)
  have hball : volume (Metric.ball (0 : ℂ) (Real.sqrt α₀)) = ENNReal.ofReal (Real.pi * α₀) := by
    calc volume (Metric.ball (0 : ℂ) (Real.sqrt α₀)) = ENNReal.ofReal (Real.sqrt α₀) ^ 2 * NNReal.pi :=
          Complex.volume_ball 0 (Real.sqrt α₀)
      _ = ENNReal.ofReal α₀ * ENNReal.ofReal Real.pi := by
          rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg α₀), Real.sq_sqrt hα₀0, ← NNReal.coe_real_pi,
            ENNReal.ofReal_coe_nnreal]
      _ = ENNReal.ofReal (Real.pi * α₀) := by rw [ENNReal.ofReal_mul Real.pi_pos.le, mul_comm]
  have hcball : volume (Metric.closedBall (0 : ℂ) (Real.sqrt β₀)) = ENNReal.ofReal (Real.pi * β₀) := by
    calc volume (Metric.closedBall (0 : ℂ) (Real.sqrt β₀)) = ENNReal.ofReal (Real.sqrt β₀) ^ 2 * NNReal.pi :=
          Complex.volume_closedBall 0 (Real.sqrt β₀)
      _ = ENNReal.ofReal β₀ * ENNReal.ofReal Real.pi := by
          rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg β₀), Real.sq_sqrt hβ₀0, ← NNReal.coe_real_pi,
            ENNReal.ofReal_coe_nnreal]
      _ = ENNReal.ofReal (Real.pi * β₀) := by rw [ENNReal.ofReal_mul Real.pi_pos.le, mul_comm]
  have hballsub : Metric.ball (0 : ℂ) (Real.sqrt α₀) ⊆ Metric.closedBall (0 : ℂ) (Real.sqrt β₀) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (Real.sqrt_le_sqrt hα₀β₀))
  calc volume (annulus θ ρ B')
      ≤ volume (Metric.closedBall (0 : ℂ) (Real.sqrt β₀) \ Metric.ball (0 : ℂ) (Real.sqrt α₀)) := measure_mono hsub
    _ = volume (Metric.closedBall (0 : ℂ) (Real.sqrt β₀)) - volume (Metric.ball (0 : ℂ) (Real.sqrt α₀)) :=
        measure_diff hballsub measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne
    _ = ENNReal.ofReal (Real.pi * β₀ - Real.pi * α₀) := by
        rw [hcball, hball, ENNReal.ofReal_sub _ (by positivity)]
    _ ≤ ENNReal.ofReal (2 * Real.pi * B' / ρ) := by
        apply ENNReal.ofReal_le_ofReal
        have hfinal : Real.pi * (β - α) = 2 * Real.pi * B' / ρ := by
          rw [hβα]
          ring
        rw [← hfinal]

        by_cases hb : 0 ≤ β
        · have hβ₀' : β₀ = β := by rw [hβ₀]; exact max_eq_left hb
          rw [hβ₀']
          nlinarith [Real.pi_pos, hαα₀]
        · have hβ₀' : β₀ = 0 := by rw [hβ₀]; exact max_eq_right (not_le.mp hb).le
          rw [hβ₀']
          nlinarith [Real.pi_pos, hα₀0, hαβ]

private theorem mem_slabSet_of_norm_entAt_le (θ ε : ℝ) (hε : ε = 1 ∨ ε = -1) (B : ℝ) (ω : Slab) (hρ : 0 < ω.1)
    (h : ‖entAt θ ε ω‖ ≤ B) : ω ∈ slabSet θ (4 * max B 0 + 1) := by
  have hent : ∀ i k, ‖ent₁ (ε * θ) ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2 i k‖ ≤ B := by
    intro i k
    have h1 : ‖entAt θ ε ω i‖ ≤ ‖entAt θ ε ω‖ := norm_le_pi_norm (entAt θ ε ω) i
    have h2 : ‖entAt θ ε ω i k‖ ≤ ‖entAt θ ε ω i‖ := norm_le_pi_norm (entAt θ ε ω i) k
    exact (h2.trans h1).trans h
  have hBmax : 4 * B ≤ 4 * max B 0 + 1 := by
    have := le_max_left B 0
    linarith
  have hN : ∀ i k, ‖nMat (ε * θ) ω.1 ω.2.1 i k‖ ≤ 4 * max B 0 + 1 :=
    fun i k => (nMat_entry_norm_le _ _ _ _ _ _ _ B hent i k).trans hBmax
  obtain ⟨h₁, h₂, h₃⟩ := slab_facts (ε * θ) ω.1 ω.2.1 (4 * max B 0 + 1) hρ hN
  have hsin : |Real.sin θ| = |Real.sin (ε * θ)| := by
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, Real.sin_neg, abs_neg]
  have hcos : Real.cos (ε * θ) = Real.cos θ := by
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, Real.cos_neg]
  exact mem_slabSet.mpr ⟨h₁, by rw [hsin]; exact h₂, by rw [← hcos]; exact h₃⟩

private theorem enorm_slabFn_le (θ ε : ℝ) (hε : ε = 1 ∨ ε = -1) (B : ℝ) (ω : Slab) (hρ : 0 < ω.1) :
    ‖(if ‖entAt θ ε ω‖ ≤ B then |scal θ ω| else 0)‖ₑ ≤
      ENNReal.ofReal (Real.sin θ ^ 2 / Real.pi ^ 3) *
        (slabSet θ (4 * max B 0 + 1)).indicator (fun ω : Slab => ENNReal.ofReal ω.1⁻¹) ω := by
  split_ifs with h
  · rw [Set.indicator_of_mem (mem_slabSet_of_norm_entAt_le θ ε hε B ω hρ h), Real.enorm_eq_ofReal_abs, abs_abs,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (abs_scal_le θ ω hρ)
  · simp

private theorem ae_slab_pos : ∀ᵐ ω ∂slabMeasure, 0 < ω.1 := by
  unfold slabMeasure
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
  exact Filter.Eventually.of_forall fun _ => Set.mem_Ioi.mp hρ

private theorem lintegral_slab_le (θ B' : ℝ) (hB' : 0 < B') (hs : Real.sin θ ≠ 0) :
    ∫⁻ ω, (slabSet θ B').indicator (fun ω : Slab => ENNReal.ofReal ω.1⁻¹) ω ∂slabMeasure ≤
      ENNReal.ofReal (2 * Real.pi * B' * (B' / |Real.sin θ|)) * boxMeasure Set.univ := by
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = |Real.sin θ| / B' := ⟨_, rfl⟩
  have ha : 0 < a := by rw [ha_def]; exact div_pos (abs_pos.mpr hs) hB'
  have hind : Measurable fun ω : Slab => (slabSet θ B').indicator (fun ω : Slab => ENNReal.ofReal ω.1⁻¹) ω :=
    (ENNReal.measurable_ofReal.comp measurable_fst.inv).indicator (measurableSet_slabSet θ B')

  have hinner : ∀ ρ : ℝ, 0 < ρ →
      ∫⁻ z, (slabSet θ B').indicator (fun ω : Slab => ENNReal.ofReal ω.1⁻¹) (ρ, z) ∂shearBoxMeasure ≤
        (if a ≤ ρ then ENNReal.ofReal (ρ ^ (-2 : ℝ)) else 0) *
          (ENNReal.ofReal (2 * Real.pi * B') * boxMeasure Set.univ) := by
    intro ρ hρ
    by_cases hrad : ρ ≤ B' ∧ |Real.sin θ| ≤ B' * ρ
    · have haρ : a ≤ ρ := by
        rw [ha_def, div_le_iff₀ hB']
        linarith [hrad.2]
      have hsec : ∀ z : ℂ × Box, (slabSet θ B').indicator (fun ω : Slab => ENNReal.ofReal ω.1⁻¹) (ρ, z) =
          ENNReal.ofReal ρ⁻¹ * (annulus θ ρ B' ×ˢ (Set.univ : Set Box)).indicator (fun _ => (1 : ENNReal)) z := by
        intro z
        by_cases hz : z.1 ∈ annulus θ ρ B'
        · have hmem : ((ρ, z) : Slab) ∈ slabSet θ B' := mem_slabSet.mpr ⟨hrad.1, hrad.2, hz⟩
          have hmem' : z ∈ annulus θ ρ B' ×ˢ (Set.univ : Set Box) := Set.mem_prod.mpr ⟨hz, Set.mem_univ _⟩
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem', mul_one]
        · have hnot : ((ρ, z) : Slab) ∉ slabSet θ B' := fun h => hz (mem_slabSet.mp h).2.2
          have hnot' : z ∉ annulus θ ρ B' ×ˢ (Set.univ : Set Box) := fun h => hz (Set.mem_prod.mp h).1
          rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hnot', mul_zero]
      have hAmeas : MeasurableSet (annulus θ ρ B' ×ˢ (Set.univ : Set Box)) :=
        (measurableSet_annulus θ ρ B').prod MeasurableSet.univ
      simp only [hsec]
      rw [lintegral_const_mul _ (measurable_const.indicator hAmeas), lintegral_indicator_const hAmeas 1, one_mul,
        if_pos haρ]
      unfold shearBoxMeasure
      rw [Measure.prod_prod]
      have h1 : ρ⁻¹ * (2 * Real.pi * B' / ρ) = ρ ^ (-2 : ℝ) * (2 * Real.pi * B') := by
        rw [Real.rpow_neg hρ.le, Real.rpow_two]
        ring
      calc ENNReal.ofReal ρ⁻¹ * (volume (annulus θ ρ B') * boxMeasure Set.univ)
          ≤ ENNReal.ofReal ρ⁻¹ * (ENNReal.ofReal (2 * Real.pi * B' / ρ) * boxMeasure Set.univ) := by
            gcongr
            exact volume_annulus_le θ ρ B' hρ hB'.le
        _ = ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal (2 * Real.pi * B' / ρ) * boxMeasure Set.univ := (mul_assoc _ _ _).symm
        _ = ENNReal.ofReal (ρ⁻¹ * (2 * Real.pi * B' / ρ)) * boxMeasure Set.univ := by
            rw [ENNReal.ofReal_mul (inv_pos.mpr hρ).le]
        _ = ENNReal.ofReal (ρ ^ (-2 : ℝ) * (2 * Real.pi * B')) * boxMeasure Set.univ := by rw [h1]
        _ = ENNReal.ofReal (ρ ^ (-2 : ℝ)) * ENNReal.ofReal (2 * Real.pi * B') * boxMeasure Set.univ := by
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
        _ = ENNReal.ofReal (ρ ^ (-2 : ℝ)) * (ENNReal.ofReal (2 * Real.pi * B') * boxMeasure Set.univ) :=
            mul_assoc _ _ _
    · have hsec : ∀ z : ℂ × Box, (slabSet θ B').indicator (fun ω : Slab => ENNReal.ofReal ω.1⁻¹) (ρ, z) = 0 := by
        intro z
        have hnot : ((ρ, z) : Slab) ∉ slabSet θ B' := fun h => hrad ⟨(mem_slabSet.mp h).1, (mem_slabSet.mp h).2.1⟩
        exact Set.indicator_of_notMem hnot _
      simp only [hsec, lintegral_zero]
      exact zero_le

  unfold slabMeasure
  rw [lintegral_prod _ hind.aemeasurable]
  have hae : ∀ᵐ ρ ∂(volume : Measure ℝ).restrict (Set.Ioi 0),
      (∫⁻ z, (slabSet θ B').indicator (fun ω : Slab => ENNReal.ofReal ω.1⁻¹) (ρ, z) ∂shearBoxMeasure) ≤
        (if a ≤ ρ then ENNReal.ofReal (ρ ^ (-2 : ℝ)) else 0) *
          (ENNReal.ofReal (2 * Real.pi * B') * boxMeasure Set.univ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    exact hinner ρ (Set.mem_Ioi.mp hρ)
  refine (lintegral_mono_ae hae).trans ?_
  have hmeas : Measurable fun ρ : ℝ => if a ≤ ρ then ENNReal.ofReal (ρ ^ (-2 : ℝ)) else 0 :=
    Measurable.ite (measurableSet_le measurable_const measurable_id')
      (ENNReal.measurable_ofReal.comp (measurable_id'.pow_const (-2 : ℝ))) measurable_const
  rw [lintegral_mul_const _ hmeas]

  have hpt : ∀ ρ : ℝ, (if a ≤ ρ then ENNReal.ofReal (ρ ^ (-2 : ℝ)) else 0) =
      (Set.Ici a).indicator (fun ρ : ℝ => ENNReal.ofReal (ρ ^ (-2 : ℝ))) ρ := by
    intro ρ
    by_cases hρ : a ≤ ρ
    · rw [if_pos hρ, Set.indicator_of_mem (Set.mem_Ici.mpr hρ)]
    · have hnot : ρ ∉ Set.Ici a := fun h => hρ (Set.mem_Ici.mp h)
      rw [if_neg hρ, Set.indicator_of_notMem hnot]
  have hsub : Set.Ici a ⊆ Set.Ioi (0 : ℝ) := fun ρ hρ => Set.mem_Ioi.mpr (lt_of_lt_of_le ha (Set.mem_Ici.mp hρ))
  have hres : (volume : Measure ℝ).restrict (Set.Ici a) = (volume : Measure ℝ).restrict (Set.Ioi a) :=
    (Measure.restrict_congr_set Ioi_ae_eq_Ici).symm
  have hint : IntegrableOn (fun ρ : ℝ => ρ ^ (-2 : ℝ)) (Set.Ioi a) := integrableOn_Ioi_rpow_of_lt (by norm_num) ha
  have hnn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi a)] fun ρ : ℝ => ρ ^ (-2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    exact Real.rpow_nonneg (ha.le.trans (Set.mem_Ioi.mp hρ).le) _
  have hI : ∫ ρ in Set.Ioi a, ρ ^ (-2 : ℝ) = -a ^ ((-2 : ℝ) + 1) / ((-2 : ℝ) + 1) :=
    integral_Ioi_rpow_of_lt (by norm_num) ha
  have hval : ∫⁻ ρ in Set.Ioi (0 : ℝ), (if a ≤ ρ then ENNReal.ofReal (ρ ^ (-2 : ℝ)) else 0) = ENNReal.ofReal a⁻¹ := by
    simp only [hpt]
    rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict_of_subset hsub, hres,
      ← ofReal_integral_eq_lintegral_ofReal hint hnn, hI]
    congr 1
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, neg_div_neg_eq, div_one]
  rw [hval, ha_def, inv_div]
  apply le_of_eq
  calc ENNReal.ofReal (B' / |Real.sin θ|) * (ENNReal.ofReal (2 * Real.pi * B') * boxMeasure Set.univ)
      = ENNReal.ofReal (B' / |Real.sin θ|) * ENNReal.ofReal (2 * Real.pi * B') * boxMeasure Set.univ :=
        (mul_assoc _ _ _).symm
    _ = ENNReal.ofReal (2 * Real.pi * B' * (B' / |Real.sin θ|)) * boxMeasure Set.univ := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_comm (B' / |Real.sin θ|)]

private theorem slab_integrable (θ ε : ℝ) (hε : ε = 1 ∨ ε = -1) (B : ℝ) :
    Integrable (fun ω : Slab => if ‖entAt θ ε ω‖ ≤ B then |scal θ ω| else 0) slabMeasure := by
  by_cases hs : Real.sin θ = 0
  · have hzero : (fun ω : Slab => if ‖entAt θ ε ω‖ ≤ B then |scal θ ω| else 0) = fun _ => 0 := by
      funext ω
      simp [scal, hs]
    have h0 : Integrable (fun _ : Slab => (0 : ℝ)) slabMeasure := integrable_zero Slab ℝ slabMeasure
    rw [hzero]
    exact h0
  · refine ⟨(measurable_slabFn θ ε B).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hbound : ∀ᵐ ω ∂slabMeasure, ‖(if ‖entAt θ ε ω‖ ≤ B then |scal θ ω| else 0)‖ₑ ≤
        ENNReal.ofReal (Real.sin θ ^ 2 / Real.pi ^ 3) *
          (slabSet θ (4 * max B 0 + 1)).indicator (fun ω : Slab => ENNReal.ofReal ω.1⁻¹) ω :=
      ae_slab_pos.mono fun ω hω => enorm_slabFn_le θ ε hε B ω hω
    refine lt_of_le_of_lt (lintegral_mono_ae hbound) ?_
    have hmeas : Measurable fun ω : Slab => (slabSet θ (4 * max B 0 + 1)).indicator
        (fun ω : Slab => ENNReal.ofReal ω.1⁻¹) ω :=
      (ENNReal.measurable_ofReal.comp measurable_fst.inv).indicator (measurableSet_slabSet _ _)
    rw [lintegral_const_mul _ hmeas]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (lintegral_slab_le θ _ (by positivity) hs) ?_)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

private def rateConst (B : ℝ) : ℝ := 2 * (4 * max B 0 + 1) ^ 2 / Real.pi ^ 2 * (boxMeasure Set.univ).toReal

private theorem integral_slabFn_le (θ ε : ℝ) (hε : ε = 1 ∨ ε = -1) (B : ℝ) (hs : Real.sin θ ≠ 0) :
    (∫ ω, (if ‖entAt θ ε ω‖ ≤ B then |scal θ ω| else 0) ∂slabMeasure) ≤ rateConst B * |Real.sin θ| := by
  have hnn : ∀ ω : Slab, 0 ≤ (if ‖entAt θ ε ω‖ ≤ B then |scal θ ω| else 0) := by
    intro ω
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
    (measurable_slabFn θ ε B).aestronglyMeasurable]
  obtain ⟨B', hB'_def⟩ : ∃ B' : ℝ, B' = 4 * max B 0 + 1 := ⟨_, rfl⟩
  have hB' : 0 < B' := by rw [hB'_def]; positivity
  have hbound : ∀ᵐ ω ∂slabMeasure, ENNReal.ofReal (if ‖entAt θ ε ω‖ ≤ B then |scal θ ω| else 0) ≤
      ENNReal.ofReal (Real.sin θ ^ 2 / Real.pi ^ 3) *
        (slabSet θ B').indicator (fun ω : Slab => ENNReal.ofReal ω.1⁻¹) ω := by
    filter_upwards [ae_slab_pos] with ω hω
    rw [← Real.enorm_of_nonneg (hnn ω), hB'_def]
    exact enorm_slabFn_le θ ε hε B ω hω
  have hmeas : Measurable fun ω : Slab => (slabSet θ B').indicator (fun ω : Slab => ENNReal.ofReal ω.1⁻¹) ω :=
    (ENNReal.measurable_ofReal.comp measurable_fst.inv).indicator (measurableSet_slabSet _ _)
  have hlin : ∫⁻ ω, ENNReal.ofReal (if ‖entAt θ ε ω‖ ≤ B then |scal θ ω| else 0) ∂slabMeasure ≤
      ENNReal.ofReal (Real.sin θ ^ 2 / Real.pi ^ 3) *
        (ENNReal.ofReal (2 * Real.pi * B' * (B' / |Real.sin θ|)) * boxMeasure Set.univ) := by
    refine (lintegral_mono_ae hbound).trans ?_
    rw [lintegral_const_mul _ hmeas]
    gcongr
    exact lintegral_slab_le θ B' hB' hs
  have hfin : ENNReal.ofReal (Real.sin θ ^ 2 / Real.pi ^ 3) *
      (ENNReal.ofReal (2 * Real.pi * B' * (B' / |Real.sin θ|)) * boxMeasure Set.univ) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))).ne
  refine (ENNReal.toReal_mono hfin hlin).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  unfold rateConst
  rw [← hB'_def]
  have habs : |Real.sin θ| ≠ 0 := abs_ne_zero.mpr hs
  have hsin : Real.sin θ ^ 2 = |Real.sin θ| * |Real.sin θ| := by rw [← sq, sq_abs]
  rw [hsin]
  field_simp

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

private theorem integrable_of_integrable_const_smul {f : ℂ → ℂ} {c : ℝ} (hc : c ≠ 0)
    (h : Integrable (fun u => c • f u) (volume : Measure ℂ)) : Integrable f (volume : Measure ℂ) :=
  (integrable_smul_iff hc f).mp h

private theorem box_integral_eq (P : Type) [NormedAddCommGroup P] (Φ : Ent × P → ℂ) (hΦ : Continuous Φ) (M : ℝ)
    (hM : ∀ z, ‖Φ z‖ ≤ M) (θ ε r : ℝ) (hr : 0 < r) (p : P) (ρ : ℝ) (hρ : 0 < ρ) (u : ℂ) :
    (∫ b, scal θ ((ρ, (u, b)) : Slab) • Φ (Real.sqrt r • entAt θ ε ((ρ, (u, b)) : Slab), p) ∂boxMeasure) =
      (4 * Real.sin θ ^ 2 * ρ⁻¹) • unitaryAverage (fun k => Φ (Matrix.of.symm
        ((k⁻¹ * twistedEllipticElt r (ε * θ) ρ u hr hρ * conjEntries k : GL (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ), p)) := by
  rw [unitaryAverage_eq_boxIntegral P Φ hΦ M hM r (ε * θ) ρ u hr hρ p, ← integral_smul, ← integral_smul]
  congr 1
  funext b
  simp only [scal, entAt, mul_smul]

private theorem transform_eq (P : Type) [NormedAddCommGroup P] (Φ : Ent × P → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (r θ : ℝ) (hr : 0 < r) (p : P) :
    twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r θ =
      (∫ ω, scal θ ω • Φ (Real.sqrt r • entAt θ 1 ω, p) ∂slabMeasure) +
        ∫ ω, scal θ ω • Φ (Real.sqrt r • entAt θ (-1) ω, p) ∂slabMeasure := by
  obtain ⟨M, hM⟩ := hΦ.bounded_above_of_compact_support hΦc

  have hsqrt : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have hΨ : Continuous fun z : Ent × P => Φ (Real.sqrt r • z.1, z.2) :=
    hΦ.comp ((continuous_const.fun_smul continuous_fst).prodMk continuous_snd)
  have hΨc : HasCompactSupport fun z : Ent × P => Φ (Real.sqrt r • z.1, z.2) :=
    hasCompactSupport_rescale Φ hΦc (Real.sqrt r) hsqrt
  have hf : ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
      Integrable (fun ω : Slab => scal θ ω • Φ (Real.sqrt r • entAt θ ε ω, p)) slabMeasure :=
    fun ε hε => integrand_integrable slabMeasure (scal θ) (entAt θ ε) P (measurable_scal θ).aestronglyMeasurable
      (measurable_entAt θ ε).aestronglyMeasurable (slab_integrable θ ε hε) _ hΨ hΨc p
  have hfP := hf 1 (Or.inl rfl)
  have hfM := hf (-1) (Or.inr rfl)
  have hzP := hfP.prod_right_ae
  have hzM := hfM.prod_right_ae
  unfold slabMeasure at hfP hfM hzP hzM ⊢
  rw [integral_prod _ hfP, integral_prod _ hfM, ← integral_add hfP.integral_prod_left hfM.integral_prod_left]

  unfold twistedEllipticTransform
  rw [dif_pos hr]
  have hcast : ∀ X : ℂ, (4 * Real.sin θ ^ 2 : ℂ) * X = (4 * Real.sin θ ^ 2 : ℝ) • X := by
    intro X
    rw [Complex.real_smul]
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
  simp only [box_integral_eq P Φ hΦ M hM θ _ r hr p ρ hρ', one_mul, neg_one_mul] at hboxP hboxM ⊢
  by_cases hs : Real.sin θ = 0
  · simp [hs]
  · have hc : 4 * Real.sin θ ^ 2 * ρ⁻¹ ≠ 0 := by positivity
    have hAP := integrable_of_integrable_const_smul hc hboxP
    have hAM := integrable_of_integrable_const_smul hc hboxM
    rw [integral_smul, integral_smul]
    have hinner : ∀ Y : ℂ, (ρ : ℂ)⁻¹ * Y = ρ⁻¹ • Y := by
      intro Y
      rw [Complex.real_smul, Complex.ofReal_inv]
    simp only [hinner]
    rw [integral_smul, integral_add hAP hAM, smul_smul, smul_add]

private theorem continuous_entAt_angle (ε : ℝ) (ω : Slab) : Continuous fun θ : ℝ => entAt θ ε ω := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have hexp : Continuous fun z : ℂ => Complex.exp z := Complex.continuous_exp
  have hconj : Continuous fun z : ℂ => (starRingEnd ℂ) z := Complex.continuous_conj
  fin_cases i <;> fin_cases k <;>
    simp only [entAt, ent₁, kInv, nMat, kBar, kMat, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_symm_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one,
      Fin.isValue] <;>
    fun_prop

private theorem continuousOn_transform (P : Type) [NormedAddCommGroup P] (Φ : Ent × P → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) :
    ContinuousOn (fun q : ℝ × ℝ × P =>
        twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1)
        {q | 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi} := by
  obtain ⟨M, hM⟩ := hΦ.bounded_above_of_compact_support hΦc
  obtain ⟨B₀, hB₀⟩ := (hΦc : IsCompact (tsupport Φ)).isBounded.exists_norm_le
  have hopen : IsOpen {q : ℝ × ℝ × P | 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi} := by
    have h1 : IsOpen {q : ℝ × ℝ × P | 0 < q.1} := isOpen_lt continuous_const continuous_fst
    have h2 : IsOpen {q : ℝ × ℝ × P | 0 < q.2.1} := isOpen_lt continuous_const continuous_snd.fst
    have h3 : IsOpen {q : ℝ × ℝ × P | q.2.1 < Real.pi} := isOpen_lt continuous_snd.fst continuous_const
    exact h1.inter (h2.inter h3)
  intro q₀ hq₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨hr₀, hθ₀, hθ₀'⟩ := hq₀
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ((0 : Ent), q₀.2.2))
  have hsin₀ : 0 < Real.sin q₀.2.1 := Real.sin_pos_of_pos_of_lt_pi hθ₀ hθ₀'

  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ℝ, r₁ = q₀.1 / 2 := ⟨_, rfl⟩
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, s₀ = Real.sin q₀.2.1 / 2 := ⟨_, rfl⟩
  have hr₁pos : 0 < r₁ := by rw [hr₁]; exact half_pos hr₀
  have hs₀pos : 0 < s₀ := by rw [hs₀]; exact half_pos hsin₀
  have hN : {q : ℝ × ℝ × P | r₁ < q.1 ∧ s₀ < Real.sin q.2.1} ∈ nhds q₀ := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_const (Real.continuous_sin.comp continuous_snd.fst))
    · exact ⟨by rw [hr₁]; linarith, by rw [hs₀]; linarith⟩

  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = B₀ / Real.sqrt r₁ := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : ℝ, B' = 4 * max Bc 0 + 1 := ⟨_, rfl⟩
  have hB'pos : 0 < B' := by rw [hB']; positivity
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, R₀ = (B' / s₀ + B') * (B' / s₀) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Set Slab, E = {ω | s₀ / B' ≤ ω.1 ∧ ω.1 ≤ B' ∧ Complex.normSq ω.2.1 ≤ R₀} := ⟨_, rfl⟩
  have hEmeas : MeasurableSet E := by
    rw [hE]
    have hnsq : Measurable fun ω : Slab => Complex.normSq ω.2.1 :=
      Complex.continuous_normSq.measurable.comp measurable_snd.fst
    have h1 : MeasurableSet {ω : Slab | s₀ / B' ≤ ω.1} := measurableSet_le measurable_const measurable_fst
    have h2 : MeasurableSet {ω : Slab | ω.1 ≤ B'} := measurableSet_le measurable_fst measurable_const
    have h3 : MeasurableSet {ω : Slab | Complex.normSq ω.2.1 ≤ R₀} := measurableSet_le hnsq measurable_const
    exact h1.inter (h2.inter h3)
  have hEfin : slabMeasure E < ⊤ := by
    have hsub : E ⊆ Set.Icc (s₀ / B') B' ×ˢ (Metric.closedBall (0 : ℂ) (Real.sqrt R₀) ×ˢ (Set.univ : Set Box)) := by
      intro ω hω
      rw [hE] at hω
      obtain ⟨h1, h2, h3⟩ := hω
      refine Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨h1, h2⟩, Set.mem_prod.mpr ⟨?_, Set.mem_univ _⟩⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have hsq : ‖ω.2.1‖ ^ 2 ≤ R₀ := by rw [Complex.sq_norm]; exact h3
      have habs := Real.abs_le_sqrt hsq
      rwa [abs_of_nonneg (norm_nonneg _)] at habs
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    unfold slabMeasure shearBoxMeasure
    rw [Measure.prod_prod, Measure.prod_prod, Measure.restrict_apply measurableSet_Icc]
    refine ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top measure_closedBall_lt_top (measure_lt_top _ _))
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_Icc_lt_top
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = M * (1 / Real.pi ^ 3 * (B' / s₀)) := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  have hbound_int : Integrable (E.indicator fun _ : Slab => c₀) slabMeasure :=
    (integrableOn_const (C := c₀) hEfin.ne).integrable_indicator hEmeas

  have hpt : ∀ q : ℝ × ℝ × P, r₁ < q.1 → s₀ < Real.sin q.2.1 → ∀ ε : ℝ, ε = 1 ∨ ε = -1 → ∀ ω : Slab, 0 < ω.1 →
      ‖scal q.2.1 ω • Φ (Real.sqrt q.1 • entAt q.2.1 ε ω, q.2.2)‖ ≤ E.indicator (fun _ : Slab => c₀) ω := by
    intro q hqr hqs ε hε ω hω
    by_cases hΦ0 : Φ (Real.sqrt q.1 • entAt q.2.1 ε ω, q.2.2) = 0
    · rw [hΦ0, smul_zero, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hc₀0) ω

    have hq1 : 0 < q.1 := hr₁pos.trans hqr
    have hent : ‖entAt q.2.1 ε ω‖ ≤ Bc := by
      have hmem : ((Real.sqrt q.1 • entAt q.2.1 ε ω, q.2.2) : Ent × P) ∈ tsupport Φ :=
        subset_tsupport Φ (Function.mem_support.mpr hΦ0)
      have h1 := hB₀ _ hmem
      have h2 : ‖Real.sqrt q.1 • entAt q.2.1 ε ω‖ ≤ ‖((Real.sqrt q.1 • entAt q.2.1 ε ω, q.2.2) : Ent × P)‖ :=
        norm_fst_le (Real.sqrt q.1 • entAt q.2.1 ε ω, q.2.2)
      have h3 : ‖Real.sqrt q.1 • entAt q.2.1 ε ω‖ = Real.sqrt q.1 * ‖entAt q.2.1 ε ω‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hq1)]
      have hsr : Real.sqrt r₁ ≤ Real.sqrt q.1 := Real.sqrt_le_sqrt hqr.le
      rw [hBc, le_div_iff₀ (Real.sqrt_pos.mpr hr₁pos)]
      calc ‖entAt q.2.1 ε ω‖ * Real.sqrt r₁ ≤ ‖entAt q.2.1 ε ω‖ * Real.sqrt q.1 := by gcongr
        _ = ‖Real.sqrt q.1 • entAt q.2.1 ε ω‖ := by rw [h3, mul_comm]
        _ ≤ B₀ := h2.trans h1

    have hslab := mem_slabSet_of_norm_entAt_le q.2.1 ε hε Bc ω hω hent
    rw [← hB'] at hslab
    obtain ⟨h₁, h₂, h₃⟩ := mem_slabSet.mp hslab
    have hρs : s₀ / B' ≤ ω.1 := by
      rw [div_le_iff₀ hB'pos]
      have hle : Real.sin q.2.1 ≤ |Real.sin q.2.1| := le_abs_self _
      linarith
    have hinv : ω.1⁻¹ ≤ B' / s₀ := by
      have h := inv_anti₀ (div_pos hs₀pos hB'pos) hρs
      rwa [inv_div] at h
    have hmemE : ω ∈ E := by
      rw [hE]
      refine ⟨hρs, h₁, ?_⟩
      have hupper : Complex.normSq ω.2.1 * ω.1 ≤ ω.1⁻¹ + B' := by
        have h := (abs_le.mp h₃).2
        have hc : ω.1⁻¹ * Real.cos q.2.1 ≤ ω.1⁻¹ := by
          calc ω.1⁻¹ * Real.cos q.2.1 ≤ ω.1⁻¹ * 1 := by gcongr; exact Real.cos_le_one _
            _ = ω.1⁻¹ := mul_one _
        linarith
      have hR : ω.1⁻¹ + B' ≤ B' / s₀ + B' := by linarith
      calc Complex.normSq ω.2.1 = Complex.normSq ω.2.1 * ω.1 * ω.1⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hω.ne', mul_one]
        _ ≤ (B' / s₀ + B') * (B' / s₀) :=
            mul_le_mul (hupper.trans hR) hinv (inv_pos.mpr hω).le (by positivity)
        _ = R₀ := hR₀.symm

    rw [Set.indicator_of_mem hmemE, norm_smul, Real.norm_eq_abs, hc₀]
    have hsc : |scal q.2.1 ω| ≤ 1 / Real.pi ^ 3 * (B' / s₀) := by
      refine (abs_scal_le _ ω hω).trans ?_
      have h1 : Real.sin q.2.1 ^ 2 ≤ 1 := Real.sin_sq_le_one q.2.1
      gcongr
    calc |scal q.2.1 ω| * ‖Φ (Real.sqrt q.1 • entAt q.2.1 ε ω, q.2.2)‖
        ≤ 1 / Real.pi ^ 3 * (B' / s₀) * M := mul_le_mul hsc (hM _) (norm_nonneg _) (by positivity)
      _ = M * (1 / Real.pi ^ 3 * (B' / s₀)) := mul_comm _ _

  have hcontAt : ∀ ε : ℝ, ε = 1 ∨ ε = -1 → ContinuousAt (fun q : ℝ × ℝ × P =>
      ∫ ω, scal q.2.1 ω • Φ (Real.sqrt q.1 • entAt q.2.1 ε ω, q.2.2) ∂slabMeasure) q₀ := by
    intro ε hε
    refine continuousAt_of_dominated ?_ ?_ hbound_int ?_
    · refine Filter.Eventually.of_forall fun q => ?_
      exact integrand_aestronglyMeasurable slabMeasure (scal q.2.1) (entAt q.2.1 ε) P
        (measurable_scal _).aestronglyMeasurable (measurable_entAt _ _).aestronglyMeasurable
        (fun z : Ent × P => Φ (Real.sqrt q.1 • z.1, z.2))
        (hΦ.comp ((continuous_const.fun_smul continuous_fst).prodMk continuous_snd)) q.2.2
    · filter_upwards [hN] with q hq
      filter_upwards [ae_slab_pos] with ω hω
      exact hpt q hq.1 hq.2 ε hε ω hω
    · refine Filter.Eventually.of_forall fun ω => ?_
      apply Continuous.continuousAt
      have h1 : Continuous fun q : ℝ × ℝ × P => scal q.2.1 ω := by
        unfold scal
        fun_prop
      have h2 : Continuous fun q : ℝ × ℝ × P => entAt q.2.1 ε ω :=
        (continuous_entAt_angle ε ω).comp continuous_snd.fst
      have h3 : Continuous fun q : ℝ × ℝ × P => Φ (Real.sqrt q.1 • entAt q.2.1 ε ω, q.2.2) :=
        hΦ.comp (((Real.continuous_sqrt.comp continuous_fst).fun_smul h2).prodMk continuous_snd.snd)
      exact h1.smul h3
  have hsum : ContinuousAt (fun q : ℝ × ℝ × P =>
      (∫ ω, scal q.2.1 ω • Φ (Real.sqrt q.1 • entAt q.2.1 1 ω, q.2.2) ∂slabMeasure) +
        ∫ ω, scal q.2.1 ω • Φ (Real.sqrt q.1 • entAt q.2.1 (-1) ω, q.2.2) ∂slabMeasure) q₀ :=
    (hcontAt 1 (Or.inl rfl)).add (hcontAt (-1) (Or.inr rfl))
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hopen.mem_nhds ⟨hr₀, hθ₀, hθ₀'⟩] with q hq
  exact transform_eq P Φ hΦ hΦc q.1 q.2.1 hq.1 q.2.2

private theorem exists_bound_transform (P : Type) [NormedAddCommGroup P] (Φ : Ent × P → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (C : Set ℝ) (hC : IsCompact C) (hC0 : C ⊆ Set.Ioi 0) :
    ∃ K : ℝ, ∀ r ∈ C, ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ p : P,
      ‖twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r θ‖ ≤
        K * |Real.sin θ| := by
  obtain ⟨M, hM⟩ := hΦ.bounded_above_of_compact_support hΦc
  obtain ⟨B₀, hB₀⟩ := (hΦc : IsCompact (tsupport Φ)).isBounded.exists_norm_le
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · subst hCe
    exact ⟨0, fun r hr => absurd hr (Set.notMem_empty r)⟩
  obtain ⟨rmin, hrminC, hrmin⟩ := hC.exists_isMinOn hCne continuousOn_id
  have hrmin0 : 0 < rmin := hC0 hrminC
  have hsrmin : 0 < Real.sqrt rmin := Real.sqrt_pos.mpr hrmin0
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = B₀ / Real.sqrt rmin := ⟨_, rfl⟩
  refine ⟨2 * M * rateConst Bc, fun r hr θ hθ p => ?_⟩
  have hr0 : 0 < r := hC0 hr
  have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ((0 : Ent), p))
  rw [transform_eq P Φ hΦ hΦc r θ hr0 p]

  have hpiece : ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
      ‖∫ ω, scal θ ω • Φ (Real.sqrt r • entAt θ ε ω, p) ∂slabMeasure‖ ≤ M * (rateConst Bc * |Real.sin θ|) := by
    intro ε hε
    have hint := (slab_integrable θ ε hε Bc).const_mul M
    refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun ω => ?_)).trans ?_
    · show ‖scal θ ω • Φ (Real.sqrt r • entAt θ ε ω, p)‖ ≤ M * (if ‖entAt θ ε ω‖ ≤ Bc then |scal θ ω| else 0)
      rw [norm_smul, Real.norm_eq_abs]
      split_ifs with he
      · rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
      · have hz : Φ (Real.sqrt r • entAt θ ε ω, p) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          apply he
          have h1 := hB₀ _ hmem
          have h2 : ‖Real.sqrt r • entAt θ ε ω‖ ≤ ‖((Real.sqrt r • entAt θ ε ω, p) : Ent × P)‖ :=
            norm_fst_le (Real.sqrt r • entAt θ ε ω, p)
          have h3 : ‖Real.sqrt r • entAt θ ε ω‖ = Real.sqrt r * ‖entAt θ ε ω‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hr0)]
          have hsr : Real.sqrt rmin ≤ Real.sqrt r := Real.sqrt_le_sqrt (isMinOn_iff.mp hrmin r hr)
          rw [hBc, le_div_iff₀ hsrmin]
          calc ‖entAt θ ε ω‖ * Real.sqrt rmin ≤ ‖entAt θ ε ω‖ * Real.sqrt r := by gcongr
            _ = ‖Real.sqrt r • entAt θ ε ω‖ := by rw [h3, mul_comm]
            _ ≤ B₀ := h2.trans h1
        rw [hz, norm_zero, mul_zero, mul_zero]
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_slabFn_le θ ε hε Bc hs) hM0
  calc ‖(∫ ω, scal θ ω • Φ (Real.sqrt r • entAt θ 1 ω, p) ∂slabMeasure) +
          ∫ ω, scal θ ω • Φ (Real.sqrt r • entAt θ (-1) ω, p) ∂slabMeasure‖
      ≤ M * (rateConst Bc * |Real.sin θ|) + M * (rateConst Bc * |Real.sin θ|) :=
        norm_add_le_of_le (hpiece 1 (Or.inl rfl)) (hpiece (-1) (Or.inr rfl))
    _ = 2 * M * rateConst Bc * |Real.sin θ| := by ring

end TwistedEllipticContinuity
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin.TwistedEllipticContinuity"

open TwistedEllipticContinuity in

theorem solution
    (P : Type) [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ContinuousOn (fun q : ℝ × ℝ × P =>
        twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1)
        {q | 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi} ∧
      (∀ C : Set ℝ, IsCompact C → C ⊆ Set.Ioi 0 →
        ∃ K : ℝ, ∀ r ∈ C, ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ p : P,
          ‖twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r θ‖ ≤
            K * |Real.sin θ|) ∧
      ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
        ∀ (r θ : ℝ) (p : P), (r, p) ∉ K →
          twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r θ = 0 := by
  refine ⟨continuousOn_transform P Φ hΦ hΦc, fun C hC hC0 => exists_bound_transform P Φ hΦ hΦc C hC hC0, ?_⟩
  obtain ⟨c, C, hc, K, hK, hzero⟩ := transform_eq_zero_outside P Φ hΦc hΦinv
  refine ⟨Set.Icc c C ×ˢ K, isCompact_Icc.prod hK, ?_, fun r θ p hout => ?_⟩
  · intro q hq
    obtain ⟨hq1, -⟩ := Set.mem_prod.mp hq
    exact Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr (lt_of_lt_of_le hc (Set.mem_Icc.mp hq1).1), Set.mem_univ _⟩
  · by_cases h : r < c
    · exact hzero r θ p (Or.inl h)
    by_cases h' : C < r
    · exact hzero r θ p (Or.inr (Or.inl h'))
    have h1 : c ≤ r := not_lt.mp h
    have h2 : r ≤ C := not_lt.mp h'
    by_cases hp : p ∈ K
    · exact absurd (Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨h1, h2⟩, hp⟩) hout
    · exact hzero r θ p (Or.inr (Or.inr hp))

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin.TwistedEllipticContinuity"

end S_AutomorphicForm_GL2Twisted_twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin
end P2MW
export P2MW.S_AutomorphicForm_GL2Twisted_twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin (solution)
