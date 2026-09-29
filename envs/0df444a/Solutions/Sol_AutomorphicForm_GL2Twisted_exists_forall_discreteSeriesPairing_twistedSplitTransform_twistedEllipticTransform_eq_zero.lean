-- Prove2me | solution 1 for AutomorphicForm.GL2Twisted.exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/2563e0a8-c1c7-5d26-ba92-78f2d2a7a069

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Definitions.Def_AutomorphicForm_GL2TwistedMonomialFibres
import Theorems.Thm_AutomorphicForm_GL2Twisted_twistedTransforms_monomialInput_eq_fibreSides
import Theorems.Thm_AutomorphicForm_GL2Twisted_ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing
import Theorems.Thm_AutomorphicForm_GL2Twisted_unitaryAverage_translate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted"
set_option autoImplicit false
p2m_open "MeasureTheory Polynomial P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.Polynomial"
namespace TorusAverage
p2m_open "AutomorphicForm.GL2Twisted P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted"

private noncomputable def diagOf (s₁ s₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(s₁ : ℂ), (s₂ : ℂ)]

private theorem coe_conjEntries' (k : GL (Fin 2) ℂ) :
    ((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (k : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) := rfl

private theorem map_conj_map_conj (K : Matrix (Fin 2) (Fin 2) ℂ) :
    (K.map (starRingEnd ℂ)).map (starRingEnd ℂ) = K := by
  ext i j; simp

private theorem map_conj_diagOf (s₁ s₂ : ℝ) : (diagOf s₁ s₂).map (starRingEnd ℂ) = diagOf s₁ s₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagOf, Matrix.diagonal, Complex.conj_ofReal]

private theorem conjTranspose_diagOf (s₁ s₂ : ℝ) : (diagOf s₁ s₂).conjTranspose = diagOf s₁ s₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagOf, Matrix.diagonal, Complex.conj_ofReal]

private theorem diagOf_entries (s₁ s₂ : ℝ) :
    diagOf s₁ s₂ 0 0 = s₁ ∧ diagOf s₁ s₂ 0 1 = 0 ∧ diagOf s₁ s₂ 1 0 = 0 ∧ diagOf s₁ s₂ 1 1 = s₂ := by
  simp [diagOf, Matrix.diagonal]

private theorem trace_diagOf_mul (s₁ s₂ : ℝ) (W : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (diagOf s₁ s₂ * W * diagOf s₁ s₂ * W.map (starRingEnd ℂ)) =
      ((s₁ ^ 2 : ℝ) : ℂ) * (W 0 0 * (starRingEnd ℂ) (W 0 0)) + ((s₂ ^ 2 : ℝ) : ℂ) * (W 1 1 * (starRingEnd ℂ) (W 1 1)) +
        ((s₁ * s₂ : ℝ) : ℂ) * (W 0 1 * (starRingEnd ℂ) (W 1 0) + W 1 0 * (starRingEnd ℂ) (W 0 1)) := by
  obtain ⟨h00, h01, h10, h11⟩ := diagOf_entries s₁ s₂
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, h00, h01, h10, h11]
  push_cast
  ring

private theorem trace_diagOf_mul_sq (s₁ s₂ : ℝ) (W : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (diagOf s₁ s₂ * W * diagOf s₁ s₂ * W.map (starRingEnd ℂ) * (diagOf s₁ s₂ * diagOf s₁ s₂)) =
      ((s₁ ^ 4 : ℝ) : ℂ) * (W 0 0 * (starRingEnd ℂ) (W 0 0)) + ((s₂ ^ 4 : ℝ) : ℂ) * (W 1 1 * (starRingEnd ℂ) (W 1 1)) +
        ((s₁ * s₂ : ℝ) : ℂ) *
          (((s₁ ^ 2 : ℝ) : ℂ) * (W 0 1 * (starRingEnd ℂ) (W 1 0)) +
            ((s₂ ^ 2 : ℝ) : ℂ) * (W 1 0 * (starRingEnd ℂ) (W 0 1))) := by
  obtain ⟨h00, h01, h10, h11⟩ := diagOf_entries s₁ s₂
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, h00, h01, h10, h11]
  push_cast
  ring

private theorem trace_diagOf_mul_diagOf (s₁ s₂ : ℝ) :
    Matrix.trace (diagOf s₁ s₂ * diagOf s₁ s₂) = (s₁ : ℂ) ^ 2 + (s₂ : ℂ) ^ 2 := by
  obtain ⟨h00, h01, h10, h11⟩ := diagOf_entries s₁ s₂
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11]
  ring

private theorem det_diagOf (s₁ s₂ : ℝ) : (diagOf s₁ s₂).det = (s₁ : ℂ) * s₂ := by
  simp [diagOf, Matrix.det_fin_two, Matrix.diagonal]

private theorem mul_conjTranspose_of_eq (K₁ K₂ : Matrix (Fin 2) (Fin 2) ℂ) (s₁ s₂ : ℝ)
    (hk₂ : K₂ * K₂.conjTranspose = 1) :
    K₁ * diagOf s₁ s₂ * K₂ * (K₁ * diagOf s₁ s₂ * K₂).conjTranspose =
      K₁ * (diagOf s₁ s₂ * diagOf s₁ s₂) * K₁.conjTranspose := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, conjTranspose_diagOf]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc K₂ K₂.conjTranspose, hk₂, Matrix.one_mul]

private theorem mul_map_conj_of_eq (K₁ K₂ : Matrix (Fin 2) (Fin 2) ℂ) (s₁ s₂ : ℝ)
    (hk₁ : K₁ * K₁.conjTranspose = 1) :
    K₁ * diagOf s₁ s₂ * K₂ * (K₁ * diagOf s₁ s₂ * K₂).map (starRingEnd ℂ) =
      K₁ * (diagOf s₁ s₂ * (K₂ * K₁.map (starRingEnd ℂ)) * diagOf s₁ s₂ *
        (K₂ * K₁.map (starRingEnd ℂ)).map (starRingEnd ℂ)) * K₁.conjTranspose := by
  rw [Matrix.map_mul, Matrix.map_mul, map_conj_diagOf, Matrix.map_mul, map_conj_map_conj]
  calc K₁ * diagOf s₁ s₂ * K₂ * (K₁.map (starRingEnd ℂ) * diagOf s₁ s₂ * K₂.map (starRingEnd ℂ))
      = K₁ * diagOf s₁ s₂ * K₂ * (K₁.map (starRingEnd ℂ) * diagOf s₁ s₂ * K₂.map (starRingEnd ℂ)) *
          (K₁ * K₁.conjTranspose) := by rw [hk₁, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

private theorem map_conj_mul_conjTranspose_of (K : Matrix (Fin 2) (Fin 2) ℂ) (h : K * K.conjTranspose = 1) :
    K.map (starRingEnd ℂ) * (K.map (starRingEnd ℂ)).conjTranspose = 1 := by
  have h' : (K * K.conjTranspose).map (starRingEnd ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [h, Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _)]
  rw [Matrix.map_mul] at h'
  convert h' using 2
  rfl

private theorem det_mul_conj_det_of (K : Matrix (Fin 2) (Fin 2) ℂ) (h : K * K.conjTranspose = 1) :
    K.det * (starRingEnd ℂ) K.det = 1 := by
  have h' := congrArg Matrix.det h
  rwa [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, Complex.star_def] at h'

private theorem norm_det_of (K : Matrix (Fin 2) (Fin 2) ℂ) (h : K * K.conjTranspose = 1) : ‖K.det‖ = 1 := by
  have h1 := det_mul_conj_det_of K h
  rw [Complex.mul_conj] at h1
  have h2 : Complex.normSq K.det = 1 := by exact_mod_cast h1
  rw [Complex.normSq_eq_norm_sq] at h2
  nlinarith [norm_nonneg K.det]

private theorem det_map_conj (K : Matrix (Fin 2) (Fin 2) ℂ) : (K.map (starRingEnd ℂ)).det = (starRingEnd ℂ) K.det := by
  rw [RingHom.map_det]
  rfl

private theorem su2_shape (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W * W.conjTranspose = 1) (hdet : W.det = 1) :
    W 1 1 = (starRingEnd ℂ) (W 0 0) ∧ W 1 0 = -(starRingEnd ℂ) (W 0 1) ∧
      Complex.normSq (W 0 0) + Complex.normSq (W 0 1) = 1 := by
  have hinv : W.conjTranspose = W⁻¹ := (Matrix.inv_eq_right_inv hW).symm
  have hadj : W⁻¹ = W.adjugate := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  rw [hadj, Matrix.adjugate_fin_two] at hinv
  have h00 := congrFun (congrFun hinv 0) 0
  have h10 := congrFun (congrFun hinv 1) 0
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Complex.star_def] at h00 h10
  refine ⟨?_, ?_, ?_⟩
  · rw [← h00]
  · rw [h10, neg_neg]
  · have h := congrFun (congrFun hW 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply_eq, Complex.star_def,
      Complex.mul_conj] at h
    exact_mod_cast h

private theorem monomialInput_eq_re_pow_mul_im_pow_of_eq_mul_diagonal_mul
    (g k₁ k₂ : GL (Fin 2) ℂ) (s₁ s₂ : ℝ) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hk₁ : star (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (hk₂ : star (k₂ : Matrix (Fin 2) (Fin 2) ℂ) * (k₂ : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (hdet : Matrix.det (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.det (k₂ : Matrix (Fin 2) (Fin 2) ℂ))
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.diagonal ![(s₁ : ℂ), (s₂ : ℂ)] * (k₂ : Matrix (Fin 2) (Fin 2) ℂ))
    (hdistinct : 2 * invAbsDet g < invFrobSq g) (i l : ℕ) :
    monomialInput i l g =
      (((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re ^ (2 * i) *
        (((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im ^ (2 * l) := by
  have hK₁' : (k₁ : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hk₁
  have hK₂' : (k₂ : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose * (k₂ : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hk₂
  have hK₁ : (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose = 1 :=
    mul_eq_one_comm.mp hK₁'
  have hK₂ : (k₂ : Matrix (Fin 2) (Fin 2) ℂ) * (k₂ : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose = 1 :=
    mul_eq_one_comm.mp hK₂'
  have hg' : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * diagOf s₁ s₂ * (k₂ : Matrix (Fin 2) (Fin 2) ℂ) := hg
  rw [Units.val_mul, coe_conjEntries']
  set W : Matrix (Fin 2) (Fin 2) ℂ :=
    (k₂ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) with hW
  have hWu : W * W.conjTranspose = 1 := by
    rw [hW, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((k₁ : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ)),
      map_conj_mul_conjTranspose_of _ hK₁, Matrix.one_mul, hK₂]
  have hWdet : W.det = 1 := by
    rw [hW, Matrix.det_mul, det_map_conj, hdet, det_mul_conj_det_of _ hK₂]
  obtain ⟨h11, h10, hnorm⟩ := su2_shape W hWu hWdet
  have hGG : (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) =
      (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (diagOf s₁ s₂ * W * diagOf s₁ s₂ * W.map (starRingEnd ℂ)) *
        (k₁ : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose := by
    rw [hg', mul_map_conj_of_eq _ _ _ _ hK₁]
  have hGH : (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose =
      (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (diagOf s₁ s₂ * diagOf s₁ s₂) *
        (k₁ : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose := by
    rw [hg', mul_conjTranspose_of_eq _ _ _ _ hK₂]
  have hconjEntries : ((conjEntries g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) := rfl
  have hT : invFrobSq g = s₁ ^ 2 + s₂ ^ 2 := by
    unfold invFrobSq
    rw [hGH, Matrix.trace_mul_cycle, hK₁', Matrix.one_mul, trace_diagOf_mul_diagOf]
    simp [← Complex.ofReal_pow]
  have hd : invAbsDet g = s₁ * s₂ := by
    unfold invAbsDet
    rw [hg', Matrix.det_mul, Matrix.det_mul, det_diagOf, norm_mul, norm_mul, norm_det_of _ hK₁, norm_det_of _ hK₂,
      ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hs₁ hs₂)]
    ring
  have hx : (invTraceNorm g).re =
      (s₁ ^ 2 + s₂ ^ 2) * Complex.normSq (W 0 0) - 2 * (s₁ * s₂) * ((W 0 1).re ^ 2 - (W 0 1).im ^ 2) := by
    unfold invTraceNorm
    rw [Units.val_mul, hconjEntries, hGG, Matrix.trace_mul_cycle, hK₁', Matrix.one_mul, trace_diagOf_mul, h11, h10]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
      Complex.normSq_apply]
    ring
  have hy : invSecondRe g =
      (s₁ ^ 4 + s₂ ^ 4) * Complex.normSq (W 0 0) -
        s₁ * s₂ * (s₁ ^ 2 + s₂ ^ 2) * ((W 0 1).re ^ 2 - (W 0 1).im ^ 2) := by
    unfold invSecondRe
    rw [Units.val_mul, hconjEntries, hGG, hGH]
    have hassoc : (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (diagOf s₁ s₂ * W * diagOf s₁ s₂ * W.map (starRingEnd ℂ)) *
          (k₁ : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose *
          ((k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (diagOf s₁ s₂ * diagOf s₁ s₂) *
            (k₁ : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose) =
        (k₁ : Matrix (Fin 2) (Fin 2) ℂ) *
          (diagOf s₁ s₂ * W * diagOf s₁ s₂ * W.map (starRingEnd ℂ) * (diagOf s₁ s₂ * diagOf s₁ s₂)) *
          (k₁ : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (k₁ : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose (k₁ : Matrix (Fin 2) (Fin 2) ℂ), hK₁',
        Matrix.one_mul]
    rw [hassoc, Matrix.trace_mul_cycle, hK₁', Matrix.one_mul, trace_diagOf_mul_sq, h11, h10]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
      Complex.normSq_apply]
    ring
  have hn : Complex.normSq (W 0 0) = 1 - (W 0 1).re ^ 2 - (W 0 1).im ^ 2 := by
    rw [Complex.normSq_apply (W 0 1)] at hnorm
    nlinarith [hnorm]
  rw [hn] at hx hy
  have hd0 : s₁ * s₂ ≠ 0 := (mul_pos hs₁ hs₂).ne'
  have hplus : 2 * (s₁ ^ 2 + s₂ ^ 2 + 2 * (s₁ * s₂)) ≠ 0 := by positivity
  have hminus : 2 * (s₁ ^ 2 + s₂ ^ 2 - 2 * (s₁ * s₂)) ≠ 0 := by
    rw [hd, hT] at hdistinct
    have : 0 < s₁ ^ 2 + s₂ ^ 2 - 2 * (s₁ * s₂) := by linarith
    positivity
  have hE : invDifference g = 2 * (s₁ * s₂) * ((W 0 1).re ^ 2 + (W 0 1).im ^ 2) +
      (s₁ ^ 2 + s₂ ^ 2) * ((W 0 1).re ^ 2 - (W 0 1).im ^ 2) := by
    unfold invDifference
    rw [hy, hT, hx, hd, div_eq_iff hd0]
    ring
  unfold monomialInput
  rw [hT, hx, hE, hd]
  have hbp : (s₁ ^ 2 + s₂ ^ 2 - ((s₁ ^ 2 + s₂ ^ 2) * (1 - (W 0 1).re ^ 2 - (W 0 1).im ^ 2) -
        2 * (s₁ * s₂) * ((W 0 1).re ^ 2 - (W 0 1).im ^ 2)) +
      (2 * (s₁ * s₂) * ((W 0 1).re ^ 2 + (W 0 1).im ^ 2) + (s₁ ^ 2 + s₂ ^ 2) * ((W 0 1).re ^ 2 - (W 0 1).im ^ 2))) /
        (2 * (s₁ ^ 2 + s₂ ^ 2 + 2 * (s₁ * s₂))) = (W 0 1).re ^ 2 := by
    rw [div_eq_iff hplus]
    ring
  have hbm : (s₁ ^ 2 + s₂ ^ 2 - ((s₁ ^ 2 + s₂ ^ 2) * (1 - (W 0 1).re ^ 2 - (W 0 1).im ^ 2) -
        2 * (s₁ * s₂) * ((W 0 1).re ^ 2 - (W 0 1).im ^ 2)) -
      (2 * (s₁ * s₂) * ((W 0 1).re ^ 2 + (W 0 1).im ^ 2) + (s₁ ^ 2 + s₂ ^ 2) * ((W 0 1).re ^ 2 - (W 0 1).im ^ 2))) /
        (2 * (s₁ ^ 2 + s₂ ^ 2 - 2 * (s₁ * s₂))) = (W 0 1).im ^ 2 := by
    rw [div_eq_iff hminus]
    ring
  rw [hbp, hbm, ← pow_mul, ← pow_mul]

private theorem coeff_aeval_neg_X (F : MvPolynomial (Fin 2) ℂ) (m : Fin 2 →₀ ℕ) :
    (MvPolynomial.aeval (fun j : Fin 2 => -(MvPolynomial.X j : MvPolynomial (Fin 2) ℂ)) F).coeff m =
      (-1) ^ (m 0 + m 1) * F.coeff m := by
  induction F using MvPolynomial.induction_on generalizing m with
  | C c =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C]
    split_ifs with h
    · rw [← h]; simp
    · simp
  | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]; ring
  | mul_X p j hp =>
    rw [map_mul, MvPolynomial.aeval_X, mul_neg, MvPolynomial.coeff_neg, MvPolynomial.coeff_mul_X',
      MvPolynomial.coeff_mul_X']
    split_ifs with hj
    · rw [hp]
      have hj' : 1 ≤ m j := Finsupp.mem_support_iff.1 hj |> Nat.one_le_iff_ne_zero.2
      have hsum : m 0 + m 1 =
          (m - Finsupp.single j 1 : Fin 2 →₀ ℕ) 0 + (m - Finsupp.single j 1 : Fin 2 →₀ ℕ) 1 + 1 := by
        rw [Finsupp.tsub_apply, Finsupp.tsub_apply]
        fin_cases j <;> simp at hj' ⊢ <;> omega
      rw [hsum, pow_succ]; ring
    · simp

private theorem eval_add_eval_neg_eq_two_mul_sum_coeff_even (F : MvPolynomial (Fin 2) ℂ)
    (hF : MvPolynomial.aeval (fun j : Fin 2 => -(MvPolynomial.X j : MvPolynomial (Fin 2) ℂ)) F = F) (a b : ℝ) :
    MvPolynomial.eval ![(a : ℂ), (b : ℂ)] F + MvPolynomial.eval ![(a : ℂ), ((-b : ℝ) : ℂ)] F =
      2 * ∑ i ∈ Finset.range (F.totalDegree + 1), ∑ l ∈ Finset.range (F.totalDegree + 1 - i),
        F.coeff (Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l)) * ((a ^ (2 * i) * b ^ (2 * l) : ℝ) : ℂ) := by
  have hodd : ∀ m ∈ F.support, Even (m 0 + m 1) := by
    intro m hm
    have h1 := coeff_aeval_neg_X F m
    rw [hF] at h1
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    rw [hne.neg_one_pow, neg_one_mul] at h1
    exact MvPolynomial.mem_support_iff.1 hm (by linear_combination (1 / 2 : ℂ) * h1)
  have hdeg : ∀ m ∈ F.support, m 0 + m 1 ≤ F.totalDegree := by
    intro m hm
    have h := MvPolynomial.le_totalDegree hm
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at h
  have heven : ∀ m ∈ F.support,
      F.coeff m * ((a : ℂ) ^ m 0 * (b : ℂ) ^ m 1) + F.coeff m * ((a : ℂ) ^ m 0 * (((-b : ℝ) : ℂ)) ^ m 1) ≠ 0 →
        Even (m 0) ∧ Even (m 1) := by
    intro m hm hne
    have he : Even (m 1) := by
      by_contra h₁
      rw [Nat.not_even_iff_odd] at h₁
      apply hne
      rw [Complex.ofReal_neg, h₁.neg_pow]; ring
    exact ⟨(Nat.even_add.1 (hodd m hm)).2 he, he⟩
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', ← Finset.sum_add_distrib, Finset.sum_sigma', Finset.mul_sum]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine Finset.sum_bij_ne_zero (fun m _ _ => ⟨m 0 / 2, m 1 / 2⟩) ?_ ?_ ?_ ?_
  · intro m hm _
    have h := hdeg m hm
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · intro m₁ hm₁ hne₁ m₂ hm₂ hne₂ heq
    obtain ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩ := heven m₁ hm₁ hne₁
    obtain ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩ := heven m₂ hm₂ hne₂
    simp only [Sigma.mk.injEq, heq_eq_eq] at heq
    obtain ⟨h0, h1⟩ := heq
    ext j
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] <;> omega
  · rintro ⟨i, l⟩ _ hne
    have hc : F.coeff (Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l)) ≠ 0 := by
      intro h0
      apply hne
      show 2 * (F.coeff (Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l)) *
        ((a ^ (2 * i) * b ^ (2 * l) : ℝ) : ℂ)) = 0
      rw [h0, zero_mul, mul_zero]
    have hab : ((a : ℂ) ^ (2 * i) * (b : ℂ) ^ (2 * l)) ≠ 0 := by
      intro h0
      apply hne
      show 2 * (F.coeff (Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l)) *
        ((a ^ (2 * i) * b ^ (2 * l) : ℝ) : ℂ)) = 0
      push_cast
      rw [h0, mul_zero, mul_zero]
    refine ⟨Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l), MvPolynomial.mem_support_iff.2 hc, ?_, ?_⟩
    · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
        Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
        add_zero, zero_add, Complex.ofReal_neg, (even_two_mul l).neg_pow]
      intro h0
      exact mul_ne_zero hc hab (by linear_combination (1 / 2 : ℂ) * h0)
    · simp only [Sigma.mk.injEq, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
        Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
        add_zero, zero_add, heq_eq_eq]
      omega
  · intro m hm hne
    obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := heven m hm hne
    have hm' : Finsupp.single 0 (2 * (m 0 / 2)) + Finsupp.single 1 (2 * (m 1 / 2)) = m := by
      ext j
      fin_cases j <;> simp <;> omega
    have h0 : 2 * (m 0 / 2) = m 0 := by omega
    have h1 : 2 * (m 1 / 2) = m 1 := by omega
    dsimp only
    rw [hm', h0, h1, Complex.ofReal_neg, Even.neg_pow ⟨q, hq⟩]
    push_cast
    ring

private noncomputable def rot (w : Matrix (Fin 2) (Fin 2) ℂ) (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] * w *
    Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)]

private theorem exp_neg_mul_exp (φ : ℝ) : Complex.exp (-(φ * Complex.I)) * Complex.exp (φ * Complex.I) = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

private theorem rot_apply (w : Matrix (Fin 2) (Fin 2) ℂ) (φ : ℝ) :
    rot w φ 0 0 = Complex.exp (-(φ * Complex.I)) * w 0 0 * Complex.exp (-(φ * Complex.I)) ∧ rot w φ 0 1 = w 0 1 ∧
      rot w φ 1 0 = w 1 0 ∧ rot w φ 1 1 = Complex.exp (φ * Complex.I) * w 1 1 * Complex.exp (φ * Complex.I) := by
  have h := exp_neg_mul_exp φ
  simp only [rot, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨by trivial, ?_, ?_, by trivial⟩
  · linear_combination (w 0 1) * h
  · linear_combination (w 1 0) * h

private theorem prod_rot_pow (w : Matrix (Fin 2) (Fin 2) ℂ) (φ : ℝ) (n : Fin 2 × Fin 2 →₀ ℕ) :
    ∏ ij : Fin 2 × Fin 2, rot w φ ij.1 ij.2 ^ n ij =
      Complex.exp (-(φ * Complex.I)) ^ (2 * n (0, 0)) * Complex.exp (φ * Complex.I) ^ (2 * n (1, 1)) *
        (w 0 0 ^ n (0, 0) * w 0 1 ^ n (0, 1) * w 1 0 ^ n (1, 0) * w 1 1 ^ n (1, 1)) := by
  obtain ⟨h00, h01, h10, h11⟩ := rot_apply w φ
  rw [Fintype.prod_prod_type, Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two, h00, h01, h10, h11]
  ring

private theorem integral_exp_int_mul (k : ℤ) :
    ∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((k : ℂ) * Complex.I * (φ : ℂ)) =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const, sub_zero]
    change ((2 * Real.pi : ℝ) : ℂ) * 1 = _
    push_cast
    ring
  · have hc : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp ((k : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show (k : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h2]
    simp

private theorem integral_exp_pow_mul_exp_pow (p q : ℕ) :
    ∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(φ * Complex.I)) ^ p * Complex.exp (φ * Complex.I) ^ q =
      if p = q then (2 * Real.pi : ℂ) else 0 := by
  have h : ∀ φ : ℝ, Complex.exp (-(φ * Complex.I)) ^ p * Complex.exp (φ * Complex.I) ^ q =
      Complex.exp ((((q : ℤ) - (p : ℤ) : ℤ) : ℂ) * Complex.I * (φ : ℂ)) := by
    intro φ
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_exp_int_mul]
  by_cases hpq : p = q
  · simp [hpq]
  · have : ((q : ℤ) - (p : ℤ)) ≠ 0 := sub_ne_zero.2 (fun h' => hpq (by exact_mod_cast h'.symm))
    simp [hpq, this]

private noncomputable def phaseAveraged (Q : MvPolynomial (Fin 2 × Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  ∑ n ∈ Q.support,
    if 2 * n (0, 0) = 2 * n (1, 1) then
      MvPolynomial.C (Q.coeff n) *
        (1 - MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 ^ 2) ^ n (0, 0) *
        (MvPolynomial.X 0 + MvPolynomial.X 1 * MvPolynomial.C Complex.I) ^ n (0, 1) *
        (-(MvPolynomial.X 0 - MvPolynomial.X 1 * MvPolynomial.C Complex.I)) ^ n (1, 0)
    else 0

private theorem integral_sum_of_continuous {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i)) :
    ∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi), ∑ i ∈ s, f i φ = ∑ i ∈ s, ∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi), f i φ := by
  classical
  refine Finset.induction_on s (by simp) fun a s ha ih => ?_
  have hs : Continuous fun φ : ℝ => ∑ i ∈ s, f i φ := by fun_prop
  have h : (∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi), (f a φ + ∑ i ∈ s, f i φ)) =
      (∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi), f a φ) + ∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi), ∑ i ∈ s, f i φ :=
    intervalIntegral.integral_add ((hf a).intervalIntegrable _ _) (hs.intervalIntegrable _ _)
  simp only [Finset.sum_insert ha]
  rw [h, ih]

private theorem integral_term (c K : ℂ) (p q : ℕ) :
    ∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi),
        c * (Complex.exp (-(φ * Complex.I)) ^ p * Complex.exp (φ * Complex.I) ^ q * K) =
      c * ((if p = q then (2 * Real.pi : ℂ) else 0) * K) := by
  have h1 : (∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi),
        c * (Complex.exp (-(φ * Complex.I)) ^ p * Complex.exp (φ * Complex.I) ^ q * K)) =
      c * ∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(φ * Complex.I)) ^ p * Complex.exp (φ * Complex.I) ^ q * K :=
    intervalIntegral.integral_const_mul _ _
  have h2 : (∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(φ * Complex.I)) ^ p * Complex.exp (φ * Complex.I) ^ q * K) =
      (∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(φ * Complex.I)) ^ p * Complex.exp (φ * Complex.I) ^ q) * K :=
    intervalIntegral.integral_mul_const _ _
  rw [h1, h2, integral_exp_pow_mul_exp_pow]

private theorem sum_apply_four (n : Fin 2 × Fin 2 →₀ ℕ) :
    (n.sum fun _ e => e) = n (0, 0) + n (0, 1) + (n (1, 0) + n (1, 1)) := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two]

private theorem totalDegree_phaseAveraged_le (Q : MvPolynomial (Fin 2 × Fin 2) ℂ) :
    (phaseAveraged Q).totalDegree ≤ Q.totalDegree := by
  unfold phaseAveraged
  refine MvPolynomial.totalDegree_finsetSum_le fun n hn => ?_
  split_ifs with h
  · have hn' := MvPolynomial.le_totalDegree hn
    rw [sum_apply_four] at hn'
    have h1 : (1 - MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) ℂ).totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ((MvPolynomial.totalDegree_sub _ _).trans
        (max_le ?_ ?_)) ?_)
      · simp
      · exact (MvPolynomial.totalDegree_X_pow _ _).le
      · exact (MvPolynomial.totalDegree_X_pow _ _).le
    have h2 : (MvPolynomial.X 0 + MvPolynomial.X 1 * MvPolynomial.C Complex.I :
        MvPolynomial (Fin 2) ℂ).totalDegree ≤ 1 := by
      refine (MvPolynomial.totalDegree_add _ _).trans (max_le (MvPolynomial.totalDegree_X _).le ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
    have h3 : (-(MvPolynomial.X 0 - MvPolynomial.X 1 * MvPolynomial.C Complex.I) :
        MvPolynomial (Fin 2) ℂ).totalDegree ≤ 1 := by
      rw [MvPolynomial.totalDegree_neg]
      refine (MvPolynomial.totalDegree_sub _ _).trans (max_le (MvPolynomial.totalDegree_X _).le ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
    have hdeg : (MvPolynomial.C (Q.coeff n) * (1 - MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 ^ 2) ^ n (0, 0) *
        (MvPolynomial.X 0 + MvPolynomial.X 1 * MvPolynomial.C Complex.I) ^ n (0, 1) *
        (-(MvPolynomial.X 0 - MvPolynomial.X 1 * MvPolynomial.C Complex.I)) ^ n (1, 0) :
          MvPolynomial (Fin 2) ℂ).totalDegree ≤ 0 + n (0, 0) * 2 + n (0, 1) * 1 + n (1, 0) * 1 := by
      refine (MvPolynomial.totalDegree_mul _ _).trans (add_le_add ((MvPolynomial.totalDegree_mul _ _).trans
        (add_le_add ((MvPolynomial.totalDegree_mul _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
      · exact (MvPolynomial.totalDegree_C _).le
      · exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ h1)
      · exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ h2)
      · exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ h3)
    exact hdeg.trans (by omega)
  · simp

private theorem eval_phaseAveraged (Q : MvPolynomial (Fin 2 × Fin 2) ℂ) (a b : ℝ) :
    MvPolynomial.eval ![(a : ℂ), (b : ℂ)] (phaseAveraged Q) =
      ∑ n ∈ Q.support,
        if 2 * n (0, 0) = 2 * n (1, 1) then
          Q.coeff n * (1 - (a : ℂ) ^ 2 - (b : ℂ) ^ 2) ^ n (0, 0) * ((a : ℂ) + (b : ℂ) * Complex.I) ^ n (0, 1) *
            (-((a : ℂ) - (b : ℂ) * Complex.I)) ^ n (1, 0)
        else 0 := by
  unfold phaseAveraged
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs
  · simp
  · simp

private theorem exists_mvPolynomial_eval_re_im_eq_integral_eval_torus_conj (Q : MvPolynomial (Fin 2 × Fin 2) ℂ) :
    ∃ F : MvPolynomial (Fin 2) ℂ, F.totalDegree ≤ Q.totalDegree ∧
      ∀ w : Matrix (Fin 2) (Fin 2) ℂ, star w * w = 1 → Matrix.det w = 1 →
        (1 / (2 * Real.pi) : ℂ) *
            ∫ φ in (0 : ℝ)..(2 * Real.pi),
              MvPolynomial.eval
                (fun ij : Fin 2 × Fin 2 =>
                  (Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] * w *
                    Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)]) ij.1 ij.2) Q =
          MvPolynomial.eval ![((w 0 1).re : ℂ), ((w 0 1).im : ℂ)] F := by
  refine ⟨phaseAveraged Q, totalDegree_phaseAveraged_le Q, fun w hw hdet => ?_⟩
  have hWu : w * w.conjTranspose = 1 :=
    mul_eq_one_comm.mp (by simpa only [Matrix.star_eq_conjTranspose] using hw)
  obtain ⟨h11, h10, hnorm⟩ := su2_shape w hWu hdet
  have hrot : ∀ φ : ℝ,
      Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] * w *
        Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] = rot w φ := fun _ => rfl
  simp_rw [hrot]
  have hev : ∀ φ : ℝ, MvPolynomial.eval (fun ij : Fin 2 × Fin 2 => rot w φ ij.1 ij.2) Q =
      ∑ n ∈ Q.support, Q.coeff n *
        (Complex.exp (-(φ * Complex.I)) ^ (2 * n (0, 0)) * Complex.exp (φ * Complex.I) ^ (2 * n (1, 1)) *
          (w 0 0 ^ n (0, 0) * w 0 1 ^ n (0, 1) * w 1 0 ^ n (1, 0) * w 1 1 ^ n (1, 1))) := by
    intro φ
    rw [MvPolynomial.eval_eq']
    exact Finset.sum_congr rfl fun n _ => by rw [prod_rot_pow]
  simp_rw [hev]
  rw [integral_sum_of_continuous _ _ fun n => by fun_prop]
  simp_rw [integral_term]
  rw [eval_phaseAveraged, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs with h
  · have hn : n (1, 1) = n (0, 0) := by omega
    have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
    have hconj : ((w 0 1).re : ℂ) - ((w 0 1).im : ℂ) * Complex.I = (starRingEnd ℂ) (w 0 1) := by
      apply Complex.ext <;> simp
    have hn' : Complex.normSq (w 0 0) = 1 - (w 0 1).re ^ 2 - (w 0 1).im ^ 2 := by
      rw [Complex.normSq_apply (w 0 1)] at hnorm
      nlinarith [hnorm]
    have hα : (1 - ((w 0 1).re : ℂ) ^ 2 - ((w 0 1).im : ℂ) ^ 2) = w 0 0 * (starRingEnd ℂ) (w 0 0) := by
      rw [Complex.mul_conj, hn']
      push_cast
      ring
    rw [Complex.re_add_im, hconj, hα, h11, h10, hn]
    field_simp
    ring
  · simp

end TorusAverage

namespace ChartInvariance

p2m_open "AutomorphicForm.GL2Twisted P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted"
open scoped Matrix

private theorem conjEntries_apply (g : GL (Fin 2) ℂ) (i j : Fin 2) :
    ((conjEntries g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j =
      (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
  rfl

private theorem conjEntries_coe (g : GL (Fin 2) ℂ) :
    ((conjEntries g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) :=
  rfl

private theorem conjEntries_mul (x y : GL (Fin 2) ℂ) : conjEntries (x * y) = conjEntries x * conjEntries y :=
  map_mul (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) x y

private theorem conjEntries_inv (x : GL (Fin 2) ℂ) : conjEntries x⁻¹ = (conjEntries x)⁻¹ :=
  map_inv (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) x

private theorem _root_.ChartInvariance.conjEntries_conjEntries (x : GL (Fin 2) ℂ) : conjEntries (conjEntries x) = x := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [conjEntries_apply, conjEntries_apply, Complex.conj_conj]

p2m_export "ChartInvariance" "conjEntries_conjEntries"
private theorem conj_mul_conjEntries (k M : GL (Fin 2) ℂ) :
    k⁻¹ * M * conjEntries k * conjEntries (k⁻¹ * M * conjEntries k) = k⁻¹ * (M * conjEntries M) * k := by
  rw [conjEntries_mul, conjEntries_mul, conjEntries_inv, conjEntries_conjEntries]
  simp only [mul_assoc, mul_inv_cancel_left]

private theorem invTraceNorm_conj (k M : GL (Fin 2) ℂ) : invTraceNorm (k⁻¹ * M * conjEntries k) = invTraceNorm M := by
  unfold invTraceNorm
  rw [conj_mul_conjEntries]
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

private theorem invAbsDet_conj (k M : GL (Fin 2) ℂ) : invAbsDet (k⁻¹ * M * conjEntries k) = invAbsDet M := by
  unfold invAbsDet
  have h1 : Matrix.det ((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (starRingEnd ℂ) (Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [conjEntries_coe, RingHom.map_det, RingHom.mapMatrix_apply]
  have h2 : ‖Matrix.det ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)‖ *
      ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, norm_one]
  simp only [Units.val_mul, Matrix.det_mul, norm_mul]
  rw [h1, RCLike.norm_conj]
  calc ‖Matrix.det ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)‖ * ‖Matrix.det (M : Matrix (Fin 2) (Fin 2) ℂ)‖ *
        ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖
      = ‖Matrix.det (M : Matrix (Fin 2) (Fin 2) ℂ)‖ *
          (‖Matrix.det ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)‖ *
            ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖) := by ring
    _ = ‖Matrix.det (M : Matrix (Fin 2) (Fin 2) ℂ)‖ := by rw [h2, mul_one]

private theorem inv_coe_of_unitary {k : GL (Fin 2) ℂ}
    (hk : star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
  rw [Matrix.star_eq_conjTranspose] at hk
  calc ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = (k : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (k : Matrix (Fin 2) (Fin 2) ℂ) *
          ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by rw [hk, Matrix.one_mul]
    _ = (k : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

private theorem mul_conjTranspose_of_unitary {k : GL (Fin 2) ℂ}
    (hk : star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
  rw [← inv_coe_of_unitary hk, Units.mul_inv]

private theorem conjEntries_mul_conjTranspose_of_unitary {k : GL (Fin 2) ℂ}
    (hk : star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    ((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
  rw [conjEntries_coe, ← Matrix.conjTranspose_map (starRingEnd ℂ) fun z => rfl, ← Matrix.map_mul,
    mul_conjTranspose_of_unitary hk]
  exact Matrix.map_one _ (map_zero _) (map_one _)

private theorem conj_mul_conjTranspose {k : GL (Fin 2) ℂ}
    (hk : star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1) (M : GL (Fin 2) ℂ) :
    ((k⁻¹ * M * conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((k⁻¹ * M * conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
      (k : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
        ((M : Matrix (Fin 2) (Fin 2) ℂ) * (M : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) * (k : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hc : ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
      ((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, conjEntries_mul_conjTranspose_of_unitary hk, Matrix.one_mul]
  simp only [Units.val_mul, Matrix.conjTranspose_mul, inv_coe_of_unitary hk, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, hc]

private theorem invFrobSq_conj {k : GL (Fin 2) ℂ}
    (hk : star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1) (M : GL (Fin 2) ℂ) :
    invFrobSq (k⁻¹ * M * conjEntries k) = invFrobSq M := by
  unfold invFrobSq
  rw [conj_mul_conjTranspose hk, Matrix.trace_mul_cycle, mul_conjTranspose_of_unitary hk, Matrix.one_mul]

private theorem invSecondRe_conj {k : GL (Fin 2) ℂ}
    (hk : star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1) (M : GL (Fin 2) ℂ) :
    invSecondRe (k⁻¹ * M * conjEntries k) = invSecondRe M := by
  have hu : ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
      (k : Matrix (Fin 2) (Fin 2) ℂ) * ((k : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, mul_conjTranspose_of_unitary hk, Matrix.one_mul]
  unfold invSecondRe
  rw [conj_mul_conjEntries, conj_mul_conjTranspose hk]
  congr 1
  simp only [Units.val_mul, inv_coe_of_unitary hk, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hu, mul_conjTranspose_of_unitary hk, Matrix.mul_one]

private theorem monomialInput_conj (i l : ℕ) {k : GL (Fin 2) ℂ}
    (hk : star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1) (M : GL (Fin 2) ℂ) :
    monomialInput i l (k⁻¹ * M * conjEntries k) = monomialInput i l M := by
  simp only [monomialInput, invDifference, invFrobSq_conj hk, invTraceNorm_conj, invAbsDet_conj, invSecondRe_conj hk]

private theorem unitaryElt_unitary (ψ η ξ₁ ξ₂ : ℝ) :
    star ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  have hU : ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
      Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
      Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
      Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))] := rfl
  have hψ : (starRingEnd ℂ) (Complex.exp (ψ * Complex.I)) * Complex.exp (ψ * Complex.I) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  have h₁ : (starRingEnd ℂ) (Complex.exp (ξ₁ * Complex.I)) = Complex.exp (-(ξ₁ * Complex.I)) := by
    rw [← Complex.exp_conj]
    simp
  have h₁' : (starRingEnd ℂ) (Complex.exp (-(ξ₁ * Complex.I))) = Complex.exp (ξ₁ * Complex.I) := by
    rw [← Complex.exp_conj]
    simp
  have h₂ : (starRingEnd ℂ) (Complex.exp (ξ₂ * Complex.I)) = Complex.exp (-(ξ₂ * Complex.I)) := by
    rw [← Complex.exp_conj]
    simp
  have h₂' : (starRingEnd ℂ) (Complex.exp (-(ξ₂ * Complex.I))) = Complex.exp (ξ₂ * Complex.I) := by
    rw [← Complex.exp_conj]
    simp
  have e₁ : Complex.exp (-(ξ₁ * Complex.I)) * Complex.exp (ξ₁ * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have e₂ : Complex.exp (-(ξ₂ * Complex.I)) * Complex.exp (ξ₂ * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hcs : ((Real.cos η : ℂ)) ^ 2 + ((Real.sin η : ℂ)) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq η
  rw [hU]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.one_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue, Complex.star_def, map_mul, map_neg,
      Complex.conj_ofReal, h₁, h₁', h₂, h₂', if_true, if_false, one_ne_zero, zero_ne_one]
  · linear_combination ((Real.cos η : ℂ) ^ 2 * (Complex.exp (-(ξ₁ * Complex.I)) * Complex.exp (ξ₁ * Complex.I)) +
        (Real.sin η : ℂ) ^ 2 * (Complex.exp (-(ξ₂ * Complex.I)) * Complex.exp (ξ₂ * Complex.I))) * hψ +
      (Real.cos η : ℂ) ^ 2 * e₁ + (Real.sin η : ℂ) ^ 2 * e₂ + hcs
  · ring
  · ring
  · linear_combination ((Real.cos η : ℂ) ^ 2 * (Complex.exp (-(ξ₁ * Complex.I)) * Complex.exp (ξ₁ * Complex.I)) +
        (Real.sin η : ℂ) ^ 2 * (Complex.exp (-(ξ₂ * Complex.I)) * Complex.exp (ξ₂ * Complex.I))) * hψ +
      (Real.cos η : ℂ) ^ 2 * e₁ + (Real.sin η : ℂ) ^ 2 * e₂ + hcs

private theorem unitaryAverage_one : unitaryAverage (fun _ => (1 : ℂ)) = 1 := by
  have h2 : ∀ η : ℝ, (∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * (1 : ℂ)) = ((2 * Real.pi) ^ 2 * (Real.sin η * Real.cos η) : ℝ) := by
    intro η
    simp only [mul_one, ← Complex.ofReal_mul]
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    congr 1
    ring
  have h3 : (∫ η in (0 : ℝ)..(Real.pi / 2), (((2 * Real.pi) ^ 2 * (Real.sin η * Real.cos η) : ℝ) : ℂ)) =
      (((2 * Real.pi) ^ 2 * (1 / 2) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul, integral_sin_mul_cos₁,
      Real.sin_pi_div_two, Real.sin_zero]
    norm_num
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold unitaryAverage
  simp_rw [h2]
  rw [h3, intervalIntegral.integral_ofReal, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  push_cast
  field_simp
  ring

private theorem unitaryAverage_const_mul (z : ℂ) (F : GL (Fin 2) ℂ → ℂ) :
    unitaryAverage (fun k => z * F k) = z * unitaryAverage F := by
  have e4 : ∀ ψ η ξ₁ : ℝ,
      (∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * (z * F (unitaryElt ψ η ξ₁ ξ₂)))
        = z * ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ η ξ₁
    have hre : (fun ξ₂ => (Real.sin η * Real.cos η : ℂ) * (z * F (unitaryElt ψ η ξ₁ ξ₂)))
        = fun ξ₂ => z * ((Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)) := by
      funext ξ₂
      ring
    rw [hre]
    exact intervalIntegral.integral_const_mul z _
  have e3 : ∀ ψ η : ℝ,
      (∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), z * ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂))
        = z * ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
            (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂) :=
    fun ψ η => intervalIntegral.integral_const_mul z _
  have e2 : ∀ ψ : ℝ,
      (∫ η in (0 : ℝ)..(Real.pi / 2), z * ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂))
        = z * ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
            (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂) :=
    fun ψ => intervalIntegral.integral_const_mul z _
  have e1 :
      (∫ ψ in (0 : ℝ)..(2 * Real.pi), z * ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
          ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂))
        = z * ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
            ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂) :=
    intervalIntegral.integral_const_mul z _
  simp only [unitaryAverage]
  simp_rw [e4, e3, e2]
  rw [e1]
  ring

private theorem unitaryAverage_const (z : ℂ) : unitaryAverage (fun _ => z) = z := by
  have h : (fun _ : GL (Fin 2) ℂ => z) = fun k => z * (fun _ : GL (Fin 2) ℂ => (1 : ℂ)) k := by
    funext k
    simp
  rw [h, unitaryAverage_const_mul, unitaryAverage_one, mul_one]

private theorem input_chart (i l : ℕ) (c : ℝ → ℂ) (M : GL (Fin 2) ℂ) (ψ η ξ₁ ξ₂ : ℝ) :
    c (invFrobSq ((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * M * conjEntries (unitaryElt ψ η ξ₁ ξ₂))) *
        ((monomialInput i l ((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * M * conjEntries (unitaryElt ψ η ξ₁ ξ₂)) : ℝ) : ℂ) =
      c (invFrobSq M) * ((monomialInput i l M : ℝ) : ℂ) := by
  rw [invFrobSq_conj (unitaryElt_unitary ψ η ξ₁ ξ₂), monomialInput_conj i l (unitaryElt_unitary ψ η ξ₁ ξ₂)]

private theorem average_conj_invariant (i l : ℕ) (c : ℝ → ℂ) (M : GL (Fin 2) ℂ) :
    unitaryAverage (fun k => c (invFrobSq (k⁻¹ * M * conjEntries k)) *
        ((monomialInput i l (k⁻¹ * M * conjEntries k) : ℝ) : ℂ)) =
      c (invFrobSq M) * ((monomialInput i l M : ℝ) : ℂ) := by
  have h : unitaryAverage (fun k => c (invFrobSq (k⁻¹ * M * conjEntries k)) *
      ((monomialInput i l (k⁻¹ * M * conjEntries k) : ℝ) : ℂ)) =
        unitaryAverage (fun _ => c (invFrobSq M) * ((monomialInput i l M : ℝ) : ℂ)) := by
    simp only [unitaryAverage, input_chart]
  rw [h, unitaryAverage_const]

end ChartInvariance

section
p2m_open "Polynomial P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.Polynomial Finset AutomorphicForm.GL2Twisted P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted"

namespace Polynomial
p2m_export "Polynomial" "C natDegree_mul_le X eval_mul support coeff_add aeval_def C_mul leadingCoeff coeff algebraMap_eq Chebyshev.natDegree_T natDegree_add_le sum_add eval₂ coeff_monomial aeval eval₂_add eval_monomial monomial eval_finsetSum natDegree_sum_le_of_forall_le Chebyshev.T_real_cos C_add Chebyshev.U aeval_C IsRoot.def lcoeff_apply coeff_sub C_pow map evalRingHom eval₂_X comp eval₂_mul coeff_C eval_pow Chebyshev.U_ne_zero sum Chebyshev.U_sub_one coe_smul coeff_zero natDegree eval_X eval_C finite_setOf_isRoot as_sum_range' coeff_sum natDegree_pow_le C_1 natDegree_sub_le eval_sub pow eq_C_of_natDegree_le_zero natDegree_X_le smul_eval mem_support_iff Chebyshev.natDegree_U_natCast support_smul C_mul_X_pow_eq_monomial coe_add eval_one lcoeff sum_smul_index' notMem_support_iff natDegree_le_iff_coeff_eq_zero aeval_X coeff_smul div Chebyshev.T_ne_zero coeff_C_mul natDegree_C eval_add map_ne_zero coeff_C_mul_X coeff_eq_zero_of_natDegree_lt support_add C_ofNat ext Chebyshev.U_real_cos coeff_C_mul_X_pow Chebyshev.T IsRoot funext eval_eq_sum_range' ring coeff_neg leadingCoeff_ne_zero eval natDegree_C_mul_le"
p2m_open "Polynomial"

private theorem exists_sum_C_mul_of_natDegree_eq (F : ℕ → ℝ[X]) (hdeg : ∀ n, (F n).natDegree = n)
    (hne : ∀ n, F n ≠ 0) :
    ∀ (m : ℕ) (p : ℝ[X]), p.natDegree ≤ m → ∃ c : ℕ → ℝ, p = ∑ j ∈ range (m + 1), C (c j) * F j := by
  intro m
  induction m with
  | zero =>
    intro p hp
    have hp0 : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero hp
    obtain ⟨x, hx⟩ : ∃ x : ℝ, F 0 = C x := ⟨_, eq_C_of_natDegree_le_zero (hdeg 0).le⟩
    have hx0 : x ≠ 0 := by
      intro h
      apply hne 0
      rw [hx, h, map_zero]
    refine ⟨fun _ => p.coeff 0 / x, ?_⟩
    rw [sum_range_one, hx, ← C_mul, div_mul_cancel₀ _ hx0]
    exact hp0
  | succ m ih =>
    intro p hp
    set a : ℝ := p.coeff (m + 1) / (F (m + 1)).leadingCoeff with ha
    have hlead : (F (m + 1)).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (hne (m + 1))
    have hcoeffF : (F (m + 1)).coeff (m + 1) = (F (m + 1)).leadingCoeff := by
      rw [Polynomial.leadingCoeff, hdeg]
    set q : ℝ[X] := p - C a * F (m + 1) with hq
    have hqdeg : q.natDegree ≤ m := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hq, coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge (m + 1) N with hlt | hge
      · have h1 : p.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hlt)
        have h2 : (F (m + 1)).coeff N = 0 := coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hlt)
        rw [h1, h2, mul_zero, sub_zero]
      · have hNeq : N = m + 1 := le_antisymm hge hN
        subst hNeq
        rw [hcoeffF, ha, div_mul_cancel₀ _ hlead, sub_self]
    obtain ⟨c, hc⟩ := ih q hqdeg
    refine ⟨fun j => if j = m + 1 then a else c j, ?_⟩
    rw [sum_range_succ]
    have hsum : (∑ j ∈ range (m + 1), C (if j = m + 1 then a else c j) * F j)
        = ∑ j ∈ range (m + 1), C (c j) * F j := by
      refine sum_congr rfl fun j hj => ?_
      rw [mem_range] at hj
      rw [if_neg (by omega)]
    show p = (∑ j ∈ range (m + 1), C (if j = m + 1 then a else c j) * F j) +
      C (if m + 1 = m + 1 then a else c (m + 1)) * F (m + 1)
    rw [hsum, if_pos rfl, ← hc, hq]
    ring

private theorem exists_sum_C_mul_chebyshevT_of_natDegree_le (m : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ m) :
    ∃ c : ℕ → ℝ, p = ∑ j ∈ range (m + 1), C (c j) * Chebyshev.T ℝ (j : ℤ) :=
  exists_sum_C_mul_of_natDegree_eq (fun n => Chebyshev.T ℝ (n : ℤ))
    (fun n => by rw [Chebyshev.natDegree_T]; simp) (fun n => Chebyshev.T_ne_zero ℝ (n : ℤ)) m p hp

private theorem exists_sum_C_mul_chebyshevU_of_natDegree_le (m : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ m) :
    ∃ c : ℕ → ℝ, p = ∑ j ∈ range (m + 1), C (c j) * Chebyshev.U ℝ (j : ℤ) :=
  exists_sum_C_mul_of_natDegree_eq (fun n => Chebyshev.U ℝ (n : ℤ))
    (fun n => Chebyshev.natDegree_U_natCast ℝ n) (fun n => Chebyshev.U_ne_zero ℝ (n : ℤ) (by omega)) m p hp

end Polynomial

namespace ArcIntegral

private noncomputable def arcIntegral (i l : ℕ) (Ψ : ℝ) : ℝ :=
  ∫ ψ in -(Ψ / 2)..Ψ / 2, Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l)

private noncomputable def doubledAnglePoly (i l : ℕ) : ℝ[X] :=
  (C (1 / 2 : ℝ) * (1 + X)) ^ i * (C (1 / 2 : ℝ) * (1 - X)) ^ l

private theorem cos_pow_mul_sin_pow_eq_eval (i l : ℕ) (ψ : ℝ) :
    Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l) = (doubledAnglePoly i l).eval (Real.cos (2 * ψ)) := by
  have h1 : Real.cos ψ ^ (2 * i) = (1 / 2 * (1 + Real.cos (2 * ψ))) ^ i := by
    rw [pow_mul, Real.cos_sq ψ]
    ring
  have h2 : Real.sin ψ ^ (2 * l) = (1 / 2 * (1 - Real.cos (2 * ψ))) ^ l := by
    rw [pow_mul, Real.sin_sq ψ, Real.cos_sq ψ]
    ring
  rw [h1, h2, doubledAnglePoly]
  simp only [eval_mul, eval_pow, eval_C, eval_add, eval_sub, eval_one, eval_X]

private theorem natDegree_doubledAnglePoly_le (i l : ℕ) : (doubledAnglePoly i l).natDegree ≤ i + l := by
  have hA : (C (1 / 2 : ℝ) * (1 + X)).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  have hB : (C (1 / 2 : ℝ) * (1 - X)).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (by simp))
  refine natDegree_mul_le.trans (add_le_add ?_ ?_)
  · exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left i hA)
  · exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left l hB)

private theorem integral_cos_doubled (a : ℝ) (ha : a ≠ 0) (Ψ : ℝ) :
    (∫ ψ in -(Ψ / 2)..Ψ / 2, Real.cos (a * (2 * ψ))) = Real.sin (a * Ψ) / a := by
  have h2a : (2 * a) ≠ 0 := mul_ne_zero two_ne_zero ha
  have hfun : (fun ψ : ℝ => Real.cos (a * (2 * ψ))) = fun ψ => Real.cos ((2 * a) * ψ) := by
    funext ψ
    congr 1
    ring
  rw [hfun, intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) h2a, integral_cos]
  have e1 : 2 * a * (Ψ / 2) = a * Ψ := by ring
  have e2 : 2 * a * (-(Ψ / 2)) = -(a * Ψ) := by ring
  rw [e1, e2, Real.sin_neg, smul_eq_mul]
  field_simp
  ring

private theorem exists_arcIntegral_eq (i l : ℕ) :
    ∃ (A : ℝ) (Q : ℝ[X]), Q.natDegree ≤ i + l - 1 ∧
      ∀ Ψ : ℝ, arcIntegral i l Ψ = A * Ψ + Real.sin Ψ * Q.eval (Real.cos Ψ) := by
  obtain ⟨c, hc⟩ :=
    exists_sum_C_mul_chebyshevT_of_natDegree_le (i + l) _ (natDegree_doubledAnglePoly_le i l)
  have hint : ∀ ψ : ℝ, Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l)
      = ∑ m ∈ range (i + l + 1), c m * Real.cos ((m : ℝ) * (2 * ψ)) := by
    intro ψ
    rw [cos_pow_mul_sin_pow_eq_eval, hc, eval_finsetSum]
    refine sum_congr rfl fun m _ => ?_
    rw [eval_mul, eval_C, Chebyshev.T_real_cos]
    simp
  refine ⟨c 0, ∑ m ∈ range (i + l), C (c (m + 1) / ((m : ℝ) + 1)) * Chebyshev.U ℝ (m : ℤ), ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    rw [mem_range] at hm
    exact (natDegree_C_mul_le _ _).trans (by rw [Chebyshev.natDegree_U_natCast]; omega)
  · intro Ψ
    unfold arcIntegral
    simp_rw [hint]
    rw [intervalIntegral.integral_finsetSum fun m _ => (by fun_prop : Continuous fun ψ : ℝ =>
      c m * Real.cos ((m : ℝ) * (2 * ψ))).intervalIntegrable _ _]
    rw [sum_range_succ']
    have h0 : (∫ ψ in -(Ψ / 2)..Ψ / 2, c 0 * Real.cos (((0 : ℕ) : ℝ) * (2 * ψ))) = c 0 * Ψ := by
      simp [mul_comm]
    have hm : ∀ m ∈ range (i + l),
        (∫ ψ in -(Ψ / 2)..Ψ / 2, c (m + 1) * Real.cos (((m + 1 : ℕ) : ℝ) * (2 * ψ)))
          = Real.sin Ψ * (c (m + 1) / ((m : ℝ) + 1) * (Chebyshev.U ℝ (m : ℤ)).eval (Real.cos Ψ)) := by
      intro m _
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      rw [intervalIntegral.integral_const_mul, Nat.cast_succ, integral_cos_doubled _ hm1]
      have hU := Chebyshev.U_real_cos Ψ (m : ℤ)
      push_cast at hU
      rw [← hU]
      field_simp
    rw [sum_congr rfl hm, h0, eval_finsetSum, mul_sum, add_comm]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [eval_mul, eval_C]

end ArcIntegral

namespace SineOrthogonality

private theorem integral_cos_intCast_mul (a : ℤ) (ha : a ≠ 0) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.cos ((a : ℝ) * θ)) = 0 := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) ha', integral_cos, mul_zero,
    Real.sin_zero, sub_zero, Real.sin_int_mul_pi, smul_zero]

private theorem integral_sin_natCast_mul_mul_sin_natCast_mul (n m : ℕ) (h : n ≠ m) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin ((n : ℝ) * θ) * Real.sin ((m : ℝ) * θ)) = 0 := by
  have hfun : ∀ θ : ℝ, Real.sin ((n : ℝ) * θ) * Real.sin ((m : ℝ) * θ)
      = (1 / 2 : ℝ) * (Real.cos ((((n : ℤ) - m : ℤ) : ℝ) * θ)
          - Real.cos ((((n : ℤ) + m : ℤ) : ℝ) * θ)) := by
    intro θ
    have h2 := Real.two_mul_sin_mul_sin ((n : ℝ) * θ) ((m : ℝ) * θ)
    push_cast
    rw [sub_mul, add_mul]
    linear_combination (1 / 2 : ℝ) * h2
  have hc1 : Continuous fun θ : ℝ => Real.cos ((((n : ℤ) - m : ℤ) : ℝ) * θ) := by fun_prop
  have hc2 : Continuous fun θ : ℝ => Real.cos ((((n : ℤ) + m : ℤ) : ℝ) * θ) := by fun_prop
  simp_rw [hfun]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _), integral_cos_intCast_mul _ (by omega), integral_cos_intCast_mul _ (by omega),
    sub_zero, mul_zero]

end SineOrthogonality

namespace SplitKernel

private noncomputable def kernel (j : ℤ) (t : ℝ) : ℝ := Real.exp (-(((j : ℝ) + 1) * |t|))

private theorem two_mul_cosh_mul_kernel (j : ℤ) (t : ℝ) :
    2 * Real.cosh t * kernel j t = kernel (j - 1) t + kernel (j + 1) t := by
  unfold kernel
  have e1 : Real.exp |t| * Real.exp (-(((j : ℝ) + 1) * |t|)) = Real.exp (-((((j - 1 : ℤ) : ℝ) + 1) * |t|)) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have e2 : Real.exp (-|t|) * Real.exp (-(((j : ℝ) + 1) * |t|)) = Real.exp (-((((j + 1 : ℤ) : ℝ) + 1) * |t|)) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [← Real.cosh_abs t, Real.cosh_eq]
  linear_combination e1 + e2

private noncomputable def poly (c : ℤ →₀ ℝ) : ℝ[X] := c.sum fun j r => C r * Chebyshev.U ℝ j

private noncomputable def fn (c : ℤ →₀ ℝ) (t : ℝ) : ℝ := c.sum fun j r => r * kernel j t

private noncomputable def shift (c : ℤ →₀ ℝ) : ℤ →₀ ℝ :=
  Finsupp.mapDomain (fun j => j - 1) c + Finsupp.mapDomain (fun j => j + 1) c

private theorem poly_mapDomain (f : ℤ → ℤ) (c : ℤ →₀ ℝ) :
    poly (Finsupp.mapDomain f c) = c.sum fun j r => C r * Chebyshev.U ℝ (f j) := by
  unfold poly
  refine Finsupp.sum_mapDomain_index (fun b => ?_) (fun b r₁ r₂ => ?_)
  · simp
  · rw [C_add, add_mul]

private theorem fn_mapDomain (f : ℤ → ℤ) (c : ℤ →₀ ℝ) (t : ℝ) :
    fn (Finsupp.mapDomain f c) t = c.sum fun j r => r * kernel (f j) t := by
  unfold fn
  refine Finsupp.sum_mapDomain_index (fun b => ?_) (fun b r₁ r₂ => ?_)
  · simp
  · rw [add_mul]

private theorem poly_shift (c : ℤ →₀ ℝ) : poly (shift c) = 2 * X * poly c := by
  unfold shift
  rw [poly, Finsupp.sum_add_index' (fun b => by simp) (fun b r₁ r₂ => by rw [C_add, add_mul]), ← poly, ← poly,
    poly_mapDomain, poly_mapDomain, poly, Finsupp.mul_sum, ← Finsupp.sum_add]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [Chebyshev.U_sub_one]
  ring

private theorem fn_shift (c : ℤ →₀ ℝ) (t : ℝ) : fn (shift c) t = 2 * Real.cosh t * fn c t := by
  unfold shift
  rw [fn, Finsupp.sum_add_index' (fun b => by simp) (fun b r₁ r₂ => by rw [add_mul]), ← fn, ← fn, fn_mapDomain,
    fn_mapDomain, fn, Finsupp.mul_sum, ← Finsupp.sum_add]
  refine Finsupp.sum_congr fun j _ => ?_
  linear_combination (-(c j)) * two_mul_cosh_mul_kernel j t

private theorem support_shift_subset (c : ℤ →₀ ℝ) (lo hi : ℤ) (h : ∀ j ∈ c.support, lo ≤ j ∧ j ≤ hi) :
    ∀ j ∈ (shift c).support, lo - 1 ≤ j ∧ j ≤ hi + 1 := by
  intro j hj
  unfold shift at hj
  rcases Finset.mem_union.mp (Finsupp.support_add hj) with hj | hj
  · obtain ⟨j₀, hj₀, hj₀e⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hj)
    have := h j₀ hj₀
    omega
  · obtain ⟨j₀, hj₀, hj₀e⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hj)
    have := h j₀ hj₀
    omega

private theorem exists_paired_expansion (a : ℕ) (w : ℤ) :
    ∃ c : ℤ →₀ ℝ, (∀ j ∈ c.support, w - a ≤ j ∧ j ≤ w + a) ∧
      (2 * X) ^ a * Chebyshev.U ℝ w = poly c ∧
      ∀ t : ℝ, (2 * Real.cosh t) ^ a * kernel w t = fn c t := by
  induction a with
  | zero =>
    refine ⟨Finsupp.single w 1, fun j hj => ?_, ?_, fun t => ?_⟩
    · have := Finset.mem_singleton.mp (Finsupp.support_single_subset hj)
      omega
    · rw [poly, Finsupp.sum_single_index (by simp)]
      simp
    · rw [fn, Finsupp.sum_single_index (by simp)]
      simp
  | succ a ih =>
    obtain ⟨c, hsupp, hpoly, hfn⟩ := ih
    refine ⟨shift c, ?_, ?_, fun t => ?_⟩
    · intro j hj
      have := support_shift_subset c _ _ hsupp j hj
      push_cast
      omega
    · rw [poly_shift, ← hpoly]
      ring
    · rw [fn_shift, ← hfn t]
      ring

end SplitKernel

namespace FibreAlgebra

noncomputable section

private def levelPoly (i l : ℕ) (T d : ℝ) : ℝ[X] :=
  C (((T + 2 * d) ^ i * (T - 2 * d) ^ l)⁻¹) * (C T - C (2 * d) * X) ^ (i + l)

private theorem natDegree_levelPoly_le (i l : ℕ) (T d : ℝ) : (levelPoly i l T d).natDegree ≤ i + l := by
  unfold levelPoly
  refine (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans ?_)
  have h1 : (C T - C (2 * d) * X : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ((natDegree_C_mul_le _ _).trans natDegree_X_le))
    rw [natDegree_C]
    exact Nat.zero_le _
  exact (Nat.mul_le_mul le_rfl h1).trans_eq (Nat.mul_one _)

private theorem fibreMonomialFactor_two_mul_eq_eval (i l : ℕ) (T d y : ℝ) :
    fibreMonomialFactor i l T d (2 * d * y) = (levelPoly i l T d).eval y := by
  simp only [fibreMonomialFactor, levelPoly, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  rw [div_eq_inv_mul]

private theorem ellipticFibreTerm_eq (i l : ℕ) (T r θ : ℝ) :
    ellipticFibreTerm i l T r θ = ((4 * Real.pi * Real.sin θ / r : ℝ) : ℂ) *
      (((levelPoly i l T r).eval (Real.cos θ) * fibreArcIntegral i l (ellipticArcLength T r θ) : ℝ) : ℂ) := by
  rw [ellipticFibreTerm, fibreMonomialFactor_two_mul_eq_eval]

private theorem mul_exp_mul_mul_exp_neg (r t : ℝ) : r * Real.exp t * (r * Real.exp (-t)) = r ^ 2 := by
  have h : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  linear_combination r ^ 2 * h

private theorem mul_exp_add_mul_exp_neg (r t : ℝ) : r * Real.exp t + r * Real.exp (-t) = 2 * r * Real.cosh t := by
  rw [Real.cosh_eq]
  ring

private theorem splitFibreTerm_exp_eq (i l : ℕ) (T r t : ℝ) (hr : 0 ≤ r) :
    splitFibreTerm i l T (r * Real.exp t) (r * Real.exp (-t)) =
      ((1 / 2 * (levelPoly i l T r).eval (Real.cosh t) * fibreArcIntegral i l (2 * Real.pi) : ℝ) : ℂ) := by
  rw [splitFibreTerm, mul_exp_mul_mul_exp_neg, Real.sqrt_sq hr, mul_exp_add_mul_exp_neg,
    fibreMonomialFactor_two_mul_eq_eval]

private theorem fibreMonomialFactor_zero_zero (T d x : ℝ) : fibreMonomialFactor 0 0 T d x = 1 := by
  simp only [fibreMonomialFactor, add_zero, pow_zero, mul_one, div_one]

private theorem fibreArcIntegral_zero_zero (Ψ : ℝ) : fibreArcIntegral 0 0 Ψ = Ψ := by
  simp only [fibreArcIntegral, mul_zero, pow_zero, mul_one, intervalIntegral.integral_const, smul_eq_mul]
  ring

private theorem ellipticFibreTerm_zero_zero (T r θ : ℝ) :
    ellipticFibreTerm 0 0 T r θ = ((4 * Real.pi * Real.sin θ / r : ℝ) : ℂ) * ((ellipticArcLength T r θ : ℝ) : ℂ) := by
  rw [ellipticFibreTerm, fibreMonomialFactor_zero_zero, fibreArcIntegral_zero_zero, one_mul]

private theorem splitFibreTerm_zero_zero (T a₁ a₂ : ℝ) : splitFibreTerm 0 0 T a₁ a₂ = (Real.pi : ℂ) := by
  rw [splitFibreTerm, fibreMonomialFactor_zero_zero, fibreArcIntegral_zero_zero]
  push_cast
  ring

private theorem ellipticFibreTerm_two_mul_self (i l : ℕ) (r θ : ℝ) (hr : 0 < r) :
    ellipticFibreTerm i l (2 * r) r θ = 0 := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    by_cases hc : Real.cos θ = 1
    · have hs : Real.sin θ = 0 := by
        have h2 := Real.sin_sq_add_cos_sq θ
        rw [hc] at h2
        have h3 : Real.sin θ ^ 2 = 0 := by linarith
        exact pow_eq_zero_iff two_ne_zero |>.mp h3
      rw [ellipticFibreTerm, hs]
      simp
    · have hD : 2 * r - 2 * r * Real.cos θ ≠ 0 := by
        intro h0
        apply hc
        have : 2 * r * (1 - Real.cos θ) = 0 := by linear_combination h0
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (by positivity)
        · linarith
      have hκ : ellipticArcLength (2 * r) r θ = 0 := by
        rw [ellipticArcLength, div_self hD, Real.arccos_one]
      rw [ellipticFibreTerm, hκ]
      simp [fibreArcIntegral]
  · have hF : ∀ x, fibreMonomialFactor i l (2 * r) r x = 0 := by
      intro x
      rw [fibreMonomialFactor, sub_self, zero_pow hl.ne', mul_zero, div_zero]
    rw [ellipticFibreTerm, hF]
    simp

end

end FibreAlgebra

namespace SplitKernel

private theorem poly_add (c c' : ℤ →₀ ℝ) : poly (c + c') = poly c + poly c' := by
  unfold poly
  exact Finsupp.sum_add_index' (fun b => by simp) (fun b r₁ r₂ => by rw [C_add, add_mul])

private theorem fn_add (c c' : ℤ →₀ ℝ) (t : ℝ) : fn (c + c') t = fn c t + fn c' t := by
  unfold fn
  exact Finsupp.sum_add_index' (fun b => by simp) (fun b r₁ r₂ => by rw [add_mul])

private theorem poly_smul (s : ℝ) (c : ℤ →₀ ℝ) : poly (s • c) = C s * poly c := by
  unfold poly
  rw [Finsupp.sum_smul_index' (fun b => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [smul_eq_mul, C_mul, mul_assoc]

private theorem fn_smul (s : ℝ) (c : ℤ →₀ ℝ) (t : ℝ) : fn (s • c) t = s * fn c t := by
  unfold fn
  rw [Finsupp.sum_smul_index' (fun b => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [smul_eq_mul, mul_assoc]

private theorem poly_sum {ι : Type*} (s : Finset ι) (g : ι → ℤ →₀ ℝ) : poly (∑ a ∈ s, g a) = ∑ a ∈ s, poly (g a) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [poly]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, poly_add, ih]

private theorem fn_sum {ι : Type*} (s : Finset ι) (g : ι → ℤ →₀ ℝ) (t : ℝ) :
    fn (∑ a ∈ s, g a) t = ∑ a ∈ s, fn (g a) t := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [fn]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fn_add, ih]

private theorem two_poly_eq_C : (2 : ℝ[X]) = C 2 := (C_ofNat 2).symm

private theorem exists_paired_expansion_X_pow (a : ℕ) (w : ℤ) :
    ∃ c : ℤ →₀ ℝ, (∀ j ∈ c.support, w - a ≤ j ∧ j ≤ w + a) ∧
      X ^ a * Chebyshev.U ℝ w = poly c ∧
      ∀ t : ℝ, Real.cosh t ^ a * kernel w t = fn c t := by
  obtain ⟨c, hsupp, hpoly, hfn⟩ := exists_paired_expansion a w
  have h2a : ((2 : ℝ) ^ a)⁻¹ * 2 ^ a = 1 := inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)
  refine ⟨((2 : ℝ) ^ a)⁻¹ • c, fun j hj => hsupp j (Finsupp.support_smul hj), ?_, fun t => ?_⟩
  · rw [poly_smul, ← hpoly, mul_pow, two_poly_eq_C, ← C_pow, ← mul_assoc, ← mul_assoc, ← C_mul, h2a, C_1, one_mul]
  · rw [fn_smul, ← hfn t, mul_pow, ← mul_assoc, ← mul_assoc, h2a, one_mul]

private theorem exists_paired_expansion_poly (N : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ N) (w : ℤ) :
    ∃ c : ℤ →₀ ℝ, (∀ j ∈ c.support, w - N ≤ j ∧ j ≤ w + N) ∧
      p * Chebyshev.U ℝ w = poly c ∧
      ∀ t : ℝ, p.eval (Real.cosh t) * kernel w t = fn c t := by
  classical
  choose cc hsupp hpoly hfn using exists_paired_expansion_X_pow
  refine ⟨∑ a ∈ range (N + 1), p.coeff a • cc a w, fun j hj => ?_, ?_, fun t => ?_⟩
  · obtain ⟨a, ha, hj⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hj)
    have h1 := hsupp a w j (Finsupp.support_smul hj)
    have h2 : a ≤ N := by simpa [Nat.lt_succ_iff] using ha
    omega
  · rw [poly_sum]
    conv_lhs => rw [p.as_sum_range' (N + 1) (Nat.lt_succ_of_le hp)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [poly_smul, ← hpoly a w, ← C_mul_X_pow_eq_monomial, mul_assoc]
  · rw [fn_sum, p.eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [fn_smul, ← hfn a w t, mul_assoc]

end SplitKernel

namespace FibreAlgebra

private theorem natDegree_C_sub_C_mul_X_le (a b : ℝ) : (C a - C b * X : ℝ[X]).natDegree ≤ 1 := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  rw [natDegree_C]
  exact Nat.zero_le _

private theorem natDegree_C_sub_C_mul_X_pow_le (a b : ℝ) (n : ℕ) : ((C a - C b * X : ℝ[X]) ^ n).natDegree ≤ n :=
  natDegree_pow_le.trans ((Nat.mul_le_mul le_rfl (natDegree_C_sub_C_mul_X_le a b)).trans_eq (Nat.mul_one n))

private theorem sub_two_mul_mul_cos_pos (T r θ : ℝ) (hr : 0 < r) (hT : 2 * r < T) : 0 < T - 2 * r * Real.cos θ := by
  nlinarith [Real.cos_le_one θ]

private theorem one_sub_arcCos_eq (T r θ : ℝ) (hr : 0 < r) (hT : 2 * r < T) :
    1 - (2 * r - T * Real.cos θ) / (T - 2 * r * Real.cos θ)
      = (T - 2 * r) * (1 + Real.cos θ) / (T - 2 * r * Real.cos θ) := by
  have hD := (sub_two_mul_mul_cos_pos T r θ hr hT).ne'
  field_simp
  ring

private theorem one_add_arcCos_eq (T r θ : ℝ) (hr : 0 < r) (hT : 2 * r < T) :
    1 + (2 * r - T * Real.cos θ) / (T - 2 * r * Real.cos θ)
      = (T + 2 * r) * (1 - Real.cos θ) / (T - 2 * r * Real.cos θ) := by
  have hD := (sub_two_mul_mul_cos_pos T r θ hr hT).ne'
  field_simp
  ring

private theorem arcCos_mem (T r θ : ℝ) (hr : 0 < r) (hT : 2 * r < T) :
    -1 ≤ (2 * r - T * Real.cos θ) / (T - 2 * r * Real.cos θ) ∧
      (2 * r - T * Real.cos θ) / (T - 2 * r * Real.cos θ) ≤ 1 := by
  have hD := sub_two_mul_mul_cos_pos T r θ hr hT
  have h1 : 0 ≤ 1 - (2 * r - T * Real.cos θ) / (T - 2 * r * Real.cos θ) := by
    rw [one_sub_arcCos_eq T r θ hr hT]
    exact div_nonneg (mul_nonneg (by linarith) (by linarith [Real.neg_one_le_cos θ])) hD.le
  have h2 : 0 ≤ 1 + (2 * r - T * Real.cos θ) / (T - 2 * r * Real.cos θ) := by
    rw [one_add_arcCos_eq T r θ hr hT]
    exact div_nonneg (mul_nonneg (by linarith) (by linarith [Real.cos_le_one θ])) hD.le
  constructor <;> linarith

private theorem cos_ellipticArcLength (T r θ : ℝ) (hr : 0 < r) (hT : 2 * r < T) :
    Real.cos (ellipticArcLength T r θ) = (2 * r - T * Real.cos θ) / (T - 2 * r * Real.cos θ) := by
  obtain ⟨h1, h2⟩ := arcCos_mem T r θ hr hT
  rw [ellipticArcLength, Real.cos_arccos h1 h2]

private theorem sin_ellipticArcLength (T r θ : ℝ) (hr : 0 < r) (hT : 2 * r < T) (hs : 0 ≤ Real.sin θ) :
    Real.sin (ellipticArcLength T r θ)
      = Real.sqrt (T ^ 2 - 4 * r ^ 2) * Real.sin θ / (T - 2 * r * Real.cos θ) := by
  have hD := sub_two_mul_mul_cos_pos T r θ hr hT
  have hD' := hD.ne'
  have hT2 : 0 ≤ T ^ 2 - 4 * r ^ 2 := by nlinarith
  have hsq : 1 - ((2 * r - T * Real.cos θ) / (T - 2 * r * Real.cos θ)) ^ 2
      = (Real.sqrt (T ^ 2 - 4 * r ^ 2) * Real.sin θ / (T - 2 * r * Real.cos θ)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, Real.sq_sqrt hT2, Real.sin_sq]
    field_simp
    ring
  rw [ellipticArcLength, Real.sin_arccos, hsq,
    Real.sqrt_sq (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hs) hD.le)]

private noncomputable def remainderPoly (i l : ℕ) (T r : ℝ) (Q : ℝ[X]) : ℝ[X] :=
  C (((T + 2 * r) ^ i * (T - 2 * r) ^ l)⁻¹) *
    ∑ n ∈ range (i + l), C (Q.coeff n) * (C (2 * r) - C T * X) ^ n * (C T - C (2 * r) * X) ^ (i + l - 1 - n)

private theorem natDegree_remainderPoly_le (i l : ℕ) (T r : ℝ) (Q : ℝ[X]) :
    (remainderPoly i l T r Q).natDegree ≤ i + l - 1 := by
  unfold remainderPoly
  refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun n hn => ?_)
  rw [mem_range] at hn
  refine natDegree_mul_le.trans ?_
  have h1 : (C (Q.coeff n) * (C (2 * r) - C T * X) ^ n).natDegree ≤ n :=
    (natDegree_C_mul_le _ _).trans (natDegree_C_sub_C_mul_X_pow_le _ _ n)
  have h2 := natDegree_C_sub_C_mul_X_pow_le T (2 * r) (i + l - 1 - n)
  omega

private theorem levelPoly_eval_mul_eval_eq (i l : ℕ) (hil : 1 ≤ i + l) (T r y : ℝ) (hD : T - 2 * r * y ≠ 0) (Q : ℝ[X])
    (hQ : Q.natDegree ≤ i + l - 1) :
    (levelPoly i l T r).eval y * Q.eval ((2 * r - T * y) / (T - 2 * r * y))
      = (T - 2 * r * y) * (remainderPoly i l T r Q).eval y := by
  have hQ' : Q.natDegree < i + l := by omega
  rw [Q.eval_eq_sum_range' hQ']
  simp only [levelPoly, remainderPoly, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_finsetSum]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  obtain ⟨m, hm⟩ : ∃ m, i + l - 1 - n = m := ⟨_, rfl⟩
  have hil' : i + l = m + n + 1 := by omega
  rw [hm, hil', pow_add, pow_add, pow_one, div_pow]
  have hc := mul_inv_cancel₀ (pow_ne_zero n hD)
  linear_combination
    (((T + 2 * r) ^ i * (T - 2 * r) ^ l)⁻¹ * (T - 2 * r * y) ^ m * (T - 2 * r * y) * Q.coeff n * (2 * r - T * y) ^ n)
      * hc

private theorem ellipticFibreTerm_decomp (i l : ℕ) (hil : 1 ≤ i + l) (A : ℝ) (Q : ℝ[X]) (hQ : Q.natDegree ≤ i + l - 1)
    (hArc : ∀ Ψ : ℝ, fibreArcIntegral i l Ψ = A * Ψ + Real.sin Ψ * Q.eval (Real.cos Ψ))
    (T r θ : ℝ) (hr : 0 < r) (hT : 2 * r < T) (hs : 0 ≤ Real.sin θ) :
    ellipticFibreTerm i l T r θ
      = ((A * (levelPoly i l T r).eval (Real.cos θ) : ℝ) : ℂ) * ellipticFibreTerm 0 0 T r θ +
        ((4 * Real.pi / r * Real.sqrt (T ^ 2 - 4 * r ^ 2) : ℝ) : ℂ) *
          ((Real.sin θ * (Real.sin θ * (remainderPoly i l T r Q).eval (Real.cos θ)) : ℝ) : ℂ) := by
  have hD' := (sub_two_mul_mul_cos_pos T r θ hr hT).ne'
  have hr' := hr.ne'
  have hq : (remainderPoly i l T r Q).eval (Real.cos θ)
      = (levelPoly i l T r).eval (Real.cos θ) * Q.eval ((2 * r - T * Real.cos θ) / (T - 2 * r * Real.cos θ)) /
        (T - 2 * r * Real.cos θ) := by
    rw [eq_div_iff hD', levelPoly_eval_mul_eval_eq i l hil T r (Real.cos θ) hD' Q hQ]
    ring
  rw [ellipticFibreTerm_eq, ellipticFibreTerm_zero_zero, hArc, sin_ellipticArcLength T r θ hr hT hs,
    cos_ellipticArcLength T r θ hr hT, hq]
  push_cast
  have hDc : ((T : ℂ) - 2 * (r : ℂ) * ((Real.cos θ : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hD'
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr'
  field_simp

end FibreAlgebra

namespace FibreAlgebra

open SplitKernel SineOrthogonality

private theorem eval_poly (c : ℤ →₀ ℝ) (y : ℝ) :
    (SplitKernel.poly c).eval y = ∑ j ∈ c.support, c j * (Chebyshev.U ℝ j).eval y := by
  simp only [SplitKernel.poly, Finsupp.sum, eval_finsetSum, eval_mul, eval_C]

private theorem fn_eq_sum (c : ℤ →₀ ℝ) (t : ℝ) : SplitKernel.fn c t = ∑ j ∈ c.support, c j * kernel j t := rfl

private theorem continuous_kernel (j : ℤ) : Continuous (kernel j) := by
  unfold kernel
  fun_prop

private theorem continuous_ellipticFibreTerm_zero_zero (T r : ℝ) (hr : 0 < r) (hT : 2 * r < T) :
    Continuous fun θ : ℝ => ellipticFibreTerm 0 0 T r θ := by
  simp only [ellipticFibreTerm_zero_zero, ellipticArcLength]
  have hκ : Continuous fun θ : ℝ => (2 * r - T * Real.cos θ) / (T - 2 * r * Real.cos θ) :=
    Continuous.div (by fun_prop) (by fun_prop) fun θ => (sub_two_mul_mul_cos_pos T r θ hr hT).ne'
  exact (Complex.continuous_ofReal.comp (by fun_prop)).mul
    (Complex.continuous_ofReal.comp (Real.continuous_arccos.comp hκ))

private theorem natCast_index_eq (n : ℕ) (θ : ℝ) : (((n : ℤ) : ℝ) + 1) * θ = ((n + 1 : ℕ) : ℝ) * θ := by
  push_cast
  ring

private theorem weight_index_eq (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) :
    ((((k : ℤ) - 2 : ℤ) : ℝ) + 1) * θ = ((k - 1 : ℕ) : ℝ) * θ := by
  push_cast [Nat.cast_sub hk]
  ring

private theorem integral_remainder_eq_zero (i l k : ℕ) (hil : 1 ≤ i + l) (hk : i + l + 2 ≤ k) (q : ℝ[X])
    (hq : q.natDegree ≤ i + l - 1) :
    (∫ θ in (0 : ℝ)..Real.pi,
        Real.sin θ * (Real.sin θ * q.eval (Real.cos θ)) * (Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ)) = 0 := by
  obtain ⟨e, he⟩ := exists_sum_C_mul_chebyshevU_of_natDegree_le (i + l - 1) q hq
  have hrange : i + l - 1 + 1 = i + l := Nat.sub_add_cancel hil
  rw [hrange] at he
  have hpt : ∀ θ : ℝ, Real.sin θ * (Real.sin θ * q.eval (Real.cos θ)) * (Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ)
      = ∑ n ∈ range (i + l), e n * (Real.sin (((n + 1 : ℕ) : ℝ) * θ) * Real.sin (((k - 1 : ℕ) : ℝ) * θ)) := by
    intro θ
    rw [he, eval_finsetSum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [eval_mul, eval_C, ← natCast_index_eq, ← weight_index_eq k (by omega), ← Chebyshev.U_real_cos,
      ← Chebyshev.U_real_cos]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun n _ => (by fun_prop : Continuous fun θ : ℝ =>
    e n * (Real.sin (((n + 1 : ℕ) : ℝ) * θ) * Real.sin (((k - 1 : ℕ) : ℝ) * θ))).intervalIntegrable _ _]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [mem_range] at hn
  rw [intervalIntegral.integral_const_mul, integral_sin_natCast_mul_mul_sin_natCast_mul _ _ (by omega), mul_zero]

private theorem constant_identity_int
    (hconstTerm : ∀ k : ℕ, 2 ≤ k → ∀ r T : ℝ, 0 < r → 2 * r ≤ T →
      (∫ θ in (0 : ℝ)..Real.pi,
          ellipticFibreTerm 0 0 T r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
        (2 * Real.pi / r : ℂ) *
          ∫ t in (-Real.arcosh (T / (2 * r)))..Real.arcosh (T / (2 * r)),
            (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t)))
    (j : ℤ) (hj : 0 ≤ j) (r T : ℝ) (hr : 0 < r) (hT : 2 * r ≤ T) :
    (∫ θ in (0 : ℝ)..Real.pi, ellipticFibreTerm 0 0 T r θ * (((Chebyshev.U ℝ j).eval (Real.cos θ) : ℝ) : ℂ)) =
      (2 * Real.pi / r : ℂ) *
        ∫ t in (-Real.arcosh (T / (2 * r)))..Real.arcosh (T / (2 * r)),
          ((kernel j t : ℝ) : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t)) := by
  have h := hconstTerm (j.toNat + 2) (by omega) r T hr hT
  have hj' : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj
  have hjr : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast hj'
  have h1 : ((j.toNat + 2 : ℕ) : ℤ) - 2 = j := by
    push_cast
    rw [hj']
    ring
  have h2 : ∀ t : ℝ, Real.exp (-((((j.toNat + 2 : ℕ) : ℝ) - 1) * |t|)) = kernel j t := by
    intro t
    unfold kernel
    congr 2
    push_cast
    rw [hjr]
    ring
  rw [h1] at h
  simp_rw [h2] at h
  exact h

private theorem summation_identity
    (hconstTerm : ∀ k : ℕ, 2 ≤ k → ∀ r T : ℝ, 0 < r → 2 * r ≤ T →
      (∫ θ in (0 : ℝ)..Real.pi,
          ellipticFibreTerm 0 0 T r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
        (2 * Real.pi / r : ℂ) *
          ∫ t in (-Real.arcosh (T / (2 * r)))..Real.arcosh (T / (2 * r)),
            (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t)))
    (i l k : ℕ) (hk : i + l + 2 ≤ k) (r T : ℝ) (hr : 0 < r) (hT : 2 * r ≤ T) :
    (∫ θ in (0 : ℝ)..Real.pi,
        ellipticFibreTerm i l T r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
      (2 * Real.pi / r : ℂ) *
        ∫ t in (-Real.arcosh (T / (2 * r)))..Real.arcosh (T / (2 * r)),
          (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreTerm i l T (r * Real.exp t) (r * Real.exp (-t)) := by
  rcases Nat.eq_zero_or_pos (i + l) with hil | hil
  · obtain ⟨hi, hl⟩ : i = 0 ∧ l = 0 := by omega
    subst hi hl
    exact hconstTerm k (by omega) r T hr hT
  rcases hT.eq_or_lt with hTw | hTlt
  · subst hTw
    have h0 : ∀ θ : ℝ, ellipticFibreTerm i l (2 * r) r θ = 0 := fun θ => ellipticFibreTerm_two_mul_self i l r θ hr
    simp only [h0, zero_mul, intervalIntegral.integral_zero]
    rw [div_self (by positivity : (2 * r : ℝ) ≠ 0)]
    simp [Real.arcosh]
  obtain ⟨A, Q, hQ, hArc⟩ := ArcIntegral.exists_arcIntegral_eq i l
  have hArc' : ∀ Ψ : ℝ, fibreArcIntegral i l Ψ = A * Ψ + Real.sin Ψ * Q.eval (Real.cos Ψ) := hArc
  have hArc2π : fibreArcIntegral i l (2 * Real.pi) = A * (2 * Real.pi) := by
    rw [hArc', Real.sin_two_pi, zero_mul, add_zero]
  obtain ⟨cc, hsupp, hpoly, hfn⟩ :=
    exists_paired_expansion_poly (i + l) (levelPoly i l T r) (natDegree_levelPoly_le i l T r) ((k : ℤ) - 2)
  have hE := continuous_ellipticFibreTerm_zero_zero T r hr hTlt
  have hker : ∀ t : ℝ, Real.exp (-(((k : ℝ) - 1) * |t|)) = kernel ((k : ℤ) - 2) t := by
    intro t
    unfold kernel
    congr 2
    push_cast
    ring
  have hpoint : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi,
      ellipticFibreTerm i l T r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)
        = (∑ j ∈ cc.support, ((A * cc j : ℝ) : ℂ) *
              (ellipticFibreTerm 0 0 T r θ * (((Chebyshev.U ℝ j).eval (Real.cos θ) : ℝ) : ℂ))) +
          ((4 * Real.pi / r * Real.sqrt (T ^ 2 - 4 * r ^ 2) : ℝ) : ℂ) *
            ((Real.sin θ * (Real.sin θ * (remainderPoly i l T r Q).eval (Real.cos θ)) *
              (Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) := by
    intro θ hθ
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have hexp : (levelPoly i l T r).eval (Real.cos θ) * (Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ)
        = ∑ j ∈ cc.support, cc j * (Chebyshev.U ℝ j).eval (Real.cos θ) := by
      rw [← eval_mul, hpoly, eval_poly]
    have hexpC : (((levelPoly i l T r).eval (Real.cos θ) : ℝ) : ℂ) *
          (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)
        = ∑ j ∈ cc.support, (cc j : ℂ) * (((Chebyshev.U ℝ j).eval (Real.cos θ) : ℝ) : ℂ) := by
      exact_mod_cast hexp
    rw [ellipticFibreTerm_decomp i l hil A Q hQ hArc' T r θ hr hTlt hs, add_mul]
    congr 1
    · have hterm : ∀ j ∈ cc.support, ((A * cc j : ℝ) : ℂ) *
          (ellipticFibreTerm 0 0 T r θ * (((Chebyshev.U ℝ j).eval (Real.cos θ) : ℝ) : ℂ))
            = ((A : ℂ) * ellipticFibreTerm 0 0 T r θ) *
                ((cc j : ℂ) * (((Chebyshev.U ℝ j).eval (Real.cos θ) : ℝ) : ℂ)) := by
        intro j _
        push_cast
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hexpC]
      push_cast
      ring
    · push_cast
      ring
  have hsplit : ∀ t : ℝ,
      (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreTerm i l T (r * Real.exp t) (r * Real.exp (-t))
        = ∑ j ∈ cc.support, ((A * cc j : ℝ) : ℂ) *
            (((kernel j t : ℝ) : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t))) := by
    intro t
    have hfn' := hfn t
    rw [fn_eq_sum] at hfn'
    have hfnC : (((levelPoly i l T r).eval (Real.cosh t) : ℝ) : ℂ) * (kernel ((k : ℤ) - 2) t : ℂ)
        = ∑ j ∈ cc.support, (cc j : ℂ) * (kernel j t : ℂ) := by
      exact_mod_cast hfn'
    have hterm : ∀ j ∈ cc.support, ((A * cc j : ℝ) : ℂ) *
        (((kernel j t : ℝ) : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t)))
          = ((A : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t))) *
              ((cc j : ℂ) * (kernel j t : ℂ)) := by
      intro j _
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hfnC, hker, splitFibreTerm_exp_eq i l T r t hr.le, hArc2π,
      splitFibreTerm_zero_zero]
    push_cast
    ring
  have hUc : ∀ j : ℤ, Continuous fun θ : ℝ => (((Chebyshev.U ℝ j).eval (Real.cos θ) : ℝ) : ℂ) := fun j =>
    Complex.continuous_ofReal.comp ((Chebyshev.U ℝ j).continuous.comp Real.continuous_cos)
  have hc1 : ∀ j : ℤ, Continuous fun θ : ℝ => ((A * cc j : ℝ) : ℂ) *
      (ellipticFibreTerm 0 0 T r θ * (((Chebyshev.U ℝ j).eval (Real.cos θ) : ℝ) : ℂ)) :=
    fun j => continuous_const.mul (hE.mul (hUc j))
  have hrem : Continuous fun θ : ℝ => ((4 * Real.pi / r * Real.sqrt (T ^ 2 - 4 * r ^ 2) : ℝ) : ℂ) *
      ((Real.sin θ * (Real.sin θ * (remainderPoly i l T r Q).eval (Real.cos θ)) *
        (Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) :=
    continuous_const.mul (Complex.continuous_ofReal.comp
      ((Real.continuous_sin.mul (Real.continuous_sin.mul
          ((remainderPoly i l T r Q).continuous.comp Real.continuous_cos))).mul
        ((Chebyshev.U ℝ ((k : ℤ) - 2)).continuous.comp Real.continuous_cos)))
  have hc2 : ∀ j : ℤ, Continuous fun t : ℝ => ((A * cc j : ℝ) : ℂ) *
      (((kernel j t : ℝ) : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t))) := by
    intro j
    simp only [splitFibreTerm_zero_zero]
    exact continuous_const.mul ((Complex.continuous_ofReal.comp (continuous_kernel j)).mul continuous_const)
  have hrem0 : (∫ θ in (0 : ℝ)..Real.pi, ((4 * Real.pi / r * Real.sqrt (T ^ 2 - 4 * r ^ 2) : ℝ) : ℂ) *
      ((Real.sin θ * (Real.sin θ * (remainderPoly i l T r Q).eval (Real.cos θ)) *
        (Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) = 0 := by
    have hcm : (∫ θ in (0 : ℝ)..Real.pi, ((4 * Real.pi / r * Real.sqrt (T ^ 2 - 4 * r ^ 2) : ℝ) : ℂ) *
          ((Real.sin θ * (Real.sin θ * (remainderPoly i l T r Q).eval (Real.cos θ)) *
            (Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))
        = ((4 * Real.pi / r * Real.sqrt (T ^ 2 - 4 * r ^ 2) : ℝ) : ℂ) *
          ∫ θ in (0 : ℝ)..Real.pi, ((Real.sin θ * (Real.sin θ * (remainderPoly i l T r Q).eval (Real.cos θ)) *
            (Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) :=
      intervalIntegral.integral_const_mul _ _
    have hre : (∫ θ in (0 : ℝ)..Real.pi, ((Real.sin θ * (Real.sin θ * (remainderPoly i l T r Q).eval (Real.cos θ)) *
            (Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))
        = ((∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * (Real.sin θ * (remainderPoly i l T r Q).eval (Real.cos θ)) *
            (Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) :=
      intervalIntegral.integral_ofReal
    have hz := integral_remainder_eq_zero i l k hil hk _ (natDegree_remainderPoly_le i l T r Q)
    rw [hcm, hre, hz, Complex.ofReal_zero, mul_zero]
  have hterm : ∀ j ∈ cc.support, (∫ θ in (0 : ℝ)..Real.pi, ((A * cc j : ℝ) : ℂ) *
      (ellipticFibreTerm 0 0 T r θ * (((Chebyshev.U ℝ j).eval (Real.cos θ) : ℝ) : ℂ)))
        = ((A * cc j : ℝ) : ℂ) * ((2 * Real.pi / r : ℂ) *
            ∫ t in (-Real.arcosh (T / (2 * r)))..Real.arcosh (T / (2 * r)),
              ((kernel j t : ℝ) : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t))) := by
    intro j hj
    have hj0 : 0 ≤ j := by
      have := (hsupp j hj).1
      push_cast at this
      omega
    have hcm : (∫ θ in (0 : ℝ)..Real.pi, ((A * cc j : ℝ) : ℂ) *
          (ellipticFibreTerm 0 0 T r θ * (((Chebyshev.U ℝ j).eval (Real.cos θ) : ℝ) : ℂ)))
        = ((A * cc j : ℝ) : ℂ) *
          ∫ θ in (0 : ℝ)..Real.pi, ellipticFibreTerm 0 0 T r θ * (((Chebyshev.U ℝ j).eval (Real.cos θ) : ℝ) : ℂ) :=
      intervalIntegral.integral_const_mul _ _
    rw [hcm, constant_identity_int hconstTerm j hj0 r T hr hT]
  rw [intervalIntegral.integral_congr hpoint,
    intervalIntegral.integral_add
      ((continuous_finsetSum cc.support fun j _ => hc1 j).intervalIntegrable _ _) (hrem.intervalIntegrable _ _),
    hrem0, add_zero, intervalIntegral.integral_finsetSum fun j _ => (hc1 j).intervalIntegrable _ _,
    Finset.sum_congr rfl hterm]
  simp_rw [hsplit]
  rw [intervalIntegral.integral_finsetSum fun j _ => (hc2 j).intervalIntegrable _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcm : (∫ t in (-Real.arcosh (T / (2 * r)))..Real.arcosh (T / (2 * r)), ((A * cc j : ℝ) : ℂ) *
          (((kernel j t : ℝ) : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t))))
        = ((A * cc j : ℝ) : ℂ) * ∫ t in (-Real.arcosh (T / (2 * r)))..Real.arcosh (T / (2 * r)),
            ((kernel j t : ℝ) : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t)) :=
      intervalIntegral.integral_const_mul _ _
  rw [hcm]
  ring

end FibreAlgebra

end
noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff WindowedSiegel.IsRowIsometry GL2Twisted.conjEntries"
namespace GL2Twisted
p2m_export "AutomorphicForm.GL2Twisted" "unitaryElt unitaryAverage conjEntries twistedSplitElt twistedSplitTransform twistedEllipticElt twistedEllipticTransform invFrobSq invTraceNorm invSecondRe invAbsDet invDifference monomialInput fibreMonomialFactor fibreArcIntegral ellipticArcLength ellipticFibreTerm splitFibreTerm ellipticFibreSide splitFibreSide twistedTransforms_monomialInput_eq_fibreSides ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing unitaryAverage_translate"
namespace OddInputs
p2m_open "AutomorphicForm.GL2Twisted AutomorphicForm"

private theorem conjEntries_mul (a b : GL (Fin 2) ℂ) : conjEntries (a * b) = conjEntries a * conjEntries b := by
  unfold conjEntries; exact map_mul _ a b

private theorem conjEntries_inv (a : GL (Fin 2) ℂ) : conjEntries a⁻¹ = (conjEntries a)⁻¹ := by
  unfold conjEntries; exact map_inv _ a

private theorem conjEntries_conjEntries (a : GL (Fin 2) ℂ) : conjEntries (conjEntries a) = a := by
  unfold conjEntries
  ext i j
  simp [Matrix.GeneralLinearGroup.map]

private theorem conjEntries_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    conjEntries (twistedSplitElt a₁ a₂ v h) = twistedSplitElt a₁ a₂ ((starRingEnd ℂ) v) h := by
  unfold conjEntries twistedSplitElt
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, Complex.conj_ofReal]

private theorem conjEntries_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    conjEntries (unitaryElt ψ η ξ₁ ξ₂) = unitaryElt (-ψ) η (-ξ₁) (-ξ₂) := by
  unfold conjEntries unitaryElt
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I,
      -Complex.ofReal_cos, -Complex.ofReal_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]

private theorem conjEntries_twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    conjEntries (twistedEllipticElt r θ ρ u hr hρ) = twistedEllipticElt r (-θ) ρ ((starRingEnd ℂ) u) hr hρ := by
  unfold conjEntries twistedEllipticElt
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
      Complex.normSq_conj, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    (try ring_nf)

private theorem unitaryElt_add_two_pi_fst
    (ψ η ξ₁ ξ₂ : ℝ) : unitaryElt (ψ + 2 * Real.pi) η ξ₁ ξ₂ = unitaryElt ψ η ξ₁ ξ₂ := by
  unfold unitaryElt
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I]

private theorem unitaryElt_add_two_pi_snd
    (ψ η ξ₁ ξ₂ : ℝ) : unitaryElt ψ η (ξ₁ + 2 * Real.pi) ξ₂ = unitaryElt ψ η ξ₁ ξ₂ := by
  unfold unitaryElt
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, Complex.exp_neg]

private theorem unitaryElt_add_two_pi_trd
    (ψ η ξ₁ ξ₂ : ℝ) : unitaryElt ψ η ξ₁ (ξ₂ + 2 * Real.pi) = unitaryElt ψ η ξ₁ ξ₂ := by
  unfold unitaryElt
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, Complex.exp_neg]

private theorem intervalIntegral_comp_neg_of_periodic {f : ℝ → ℂ} (hf : Function.Periodic f (2 * Real.pi)) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), f (-x) = ∫ x in (0 : ℝ)..(2 * Real.pi), f x := by
  rw [intervalIntegral.integral_comp_neg]
  have h := hf.intervalIntegral_add_eq (-(2 * Real.pi)) 0
  simpa using h

private theorem unitaryAverage_comp_conjEntries (G : GL (Fin 2) ℂ → ℂ) :
    unitaryAverage (fun k => G (conjEntries k)) = unitaryAverage G := by
  unfold unitaryAverage
  congr 1
  simp_rw [conjEntries_unitaryElt]
  have hψ : Function.Periodic (fun ψ : ℝ => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * G (unitaryElt ψ η (-ξ₁) (-ξ₂)))
      (2 * Real.pi) := fun ψ => by simp only [unitaryElt_add_two_pi_fst]
  rw [intervalIntegral_comp_neg_of_periodic hψ]
  refine intervalIntegral.integral_congr fun ψ _ => ?_
  refine intervalIntegral.integral_congr fun η _ => ?_
  have hξ₁ : Function.Periodic (fun ξ₁ : ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * G (unitaryElt ψ η ξ₁ (-ξ₂))) (2 * Real.pi) :=
    fun ξ₁ => by simp only [unitaryElt_add_two_pi_snd]
  rw [intervalIntegral_comp_neg_of_periodic hξ₁]
  refine intervalIntegral.integral_congr fun ξ₁ _ => ?_
  have hξ₂ : Function.Periodic (fun ξ₂ : ℝ => (Real.sin η * Real.cos η : ℂ) * G (unitaryElt ψ η ξ₁ ξ₂))
      (2 * Real.pi) := fun ξ₂ => by simp only [unitaryElt_add_two_pi_trd]
  exact intervalIntegral_comp_neg_of_periodic hξ₂

private theorem unitaryAverage_neg (F : GL (Fin 2) ℂ → ℂ) : unitaryAverage (fun k => -F k) = -unitaryAverage F := by
  rw [unitaryAverage, unitaryAverage, ← mul_neg]
  congr 1
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun ψ _ => ?_
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun η _ => ?_
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun ξ₁ _ => ?_
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun ξ₂ _ => ?_
  simp only [mul_neg]

private theorem integral_comp_conj (A : ℂ → ℂ) : ∫ v : ℂ, A ((starRingEnd ℂ) v) = ∫ v : ℂ, A v := by
  have h := Complex.conjLIE.measurePreserving.integral_comp Complex.conjLIE.toHomeomorph.measurableEmbedding A
  simpa [Complex.conjLIE_apply] using h

private theorem eq_zero_of_eq_neg_self {z : ℂ} (h : z = -z) : z = 0 := by
  have h2 : (2 : ℂ) * z = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

private theorem unitaryAverage_odd_at (O : GL (Fin 2) ℂ → ℂ) (hO : ∀ g, O (conjEntries g) = -O g) (m : GL (Fin 2) ℂ) :
    (unitaryAverage fun k => O (k⁻¹ * m * conjEntries k)) =
      -(unitaryAverage fun k => O (k⁻¹ * conjEntries m * conjEntries k)) := by
  have h1 : (fun k => O (k⁻¹ * m * conjEntries k)) =
      fun k => -(fun k' => O (k'⁻¹ * conjEntries m * conjEntries k')) (conjEntries k) := by
    funext k
    have h := hO (k⁻¹ * m * conjEntries k)
    rw [conjEntries_mul, conjEntries_mul, conjEntries_inv, conjEntries_conjEntries] at h
    simp only
    rw [conjEntries_conjEntries, h, neg_neg]
  rw [h1, unitaryAverage_neg,
    unitaryAverage_comp_conjEntries (fun k' => O (k'⁻¹ * conjEntries m * conjEntries k'))]

private theorem integral_twistedSplitElt_eq_zero_of_odd (F : GL (Fin 2) ℂ → ℂ) (hF : ∀ g, F (conjEntries g) = -F g)
    (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) : ∫ v : ℂ, F (twistedSplitElt a₁ a₂ v h) = 0 := by
  apply eq_zero_of_eq_neg_self
  calc (∫ v : ℂ, F (twistedSplitElt a₁ a₂ v h))
      = ∫ v : ℂ, -F (twistedSplitElt a₁ a₂ ((starRingEnd ℂ) v) h) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only
        rw [← conjEntries_twistedSplitElt, hF, neg_neg]
    _ = -∫ v : ℂ, F (twistedSplitElt a₁ a₂ ((starRingEnd ℂ) v) h) := integral_neg _
    _ = -∫ v : ℂ, F (twistedSplitElt a₁ a₂ v h) := by
        rw [integral_comp_conj (fun v => F (twistedSplitElt a₁ a₂ v h))]

private theorem integral_twistedEllipticElt_two_sheets_eq_zero_of_odd (F : GL (Fin 2) ℂ → ℂ)
    (hF : ∀ g, F (conjEntries g) = -F g) (r θ ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (c : ℂ) :
    ∫ u : ℂ, c * (F (twistedEllipticElt r θ ρ u hr hρ) + F (twistedEllipticElt r (-θ) ρ u hr hρ)) = 0 := by
  apply eq_zero_of_eq_neg_self
  set B : ℂ → ℂ := fun u =>
    c * (F (twistedEllipticElt r θ ρ u hr hρ) + F (twistedEllipticElt r (-θ) ρ u hr hρ)) with hB
  have hpt : ∀ u, B u = -B ((starRingEnd ℂ) u) := by
    intro u
    simp only [hB]
    have h₁ := hF (twistedEllipticElt r θ ρ u hr hρ)
    have h₂ := hF (twistedEllipticElt r (-θ) ρ u hr hρ)
    rw [conjEntries_twistedEllipticElt] at h₁ h₂
    rw [neg_neg] at h₂
    linear_combination c * h₁ + c * h₂
  calc (∫ u : ℂ, B u) = ∫ u : ℂ, -B ((starRingEnd ℂ) u) := integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = -∫ u : ℂ, B ((starRingEnd ℂ) u) := integral_neg _
    _ = -∫ u : ℂ, B u := by rw [integral_comp_conj B]

private theorem odd_unitaryAverage_twistedConj
    (O : GL (Fin 2) ℂ → ℂ) (hO : ∀ g, O (conjEntries g) = -O g) (m : GL (Fin 2) ℂ) :
    (unitaryAverage fun k => O (k⁻¹ * conjEntries m * conjEntries k)) =
      -(unitaryAverage fun k => O (k⁻¹ * m * conjEntries k)) := by
  rw [unitaryAverage_odd_at O hO m, neg_neg]

private theorem twistedSplitTransform_eq_zero_of_odd (O : GL (Fin 2) ℂ → ℂ) (hO : ∀ g, O (conjEntries g) = -O g)
    (a₁ a₂ : ℝ) : twistedSplitTransform O a₁ a₂ = 0 := by
  unfold twistedSplitTransform
  split_ifs with h
  · exact integral_twistedSplitElt_eq_zero_of_odd (fun m => unitaryAverage fun k => O (k⁻¹ * m * conjEntries k))
      (odd_unitaryAverage_twistedConj O hO) a₁ a₂ h
  · rfl

private theorem integral_twistedEllipticElt_bracket_eq_zero_of_odd (F : GL (Fin 2) ℂ → ℂ)
    (hF : ∀ g, F (conjEntries g) = -F g) (r θ : ℝ) (hr : 0 < r) :
    (∫ ρ in Set.Ioi (0 : ℝ), ∫ u : ℂ,
        if hρ : 0 < ρ then
          (ρ : ℂ)⁻¹ * (F (twistedEllipticElt r θ ρ u hr hρ) + F (twistedEllipticElt r (-θ) ρ u hr hρ))
        else 0) = 0 := by
  have hinner : ∀ ρ : ℝ, (∫ u : ℂ, if hρ : 0 < ρ then
      (ρ : ℂ)⁻¹ * (F (twistedEllipticElt r θ ρ u hr hρ) + F (twistedEllipticElt r (-θ) ρ u hr hρ)) else 0) = 0 := by
    intro ρ
    by_cases hρ : 0 < ρ
    · simp only [dif_pos hρ]
      exact integral_twistedEllipticElt_two_sheets_eq_zero_of_odd F hF r θ ρ hr hρ _
    · simp only [hρ, dite_false, integral_zero]
  simp only [hinner, integral_zero]

private theorem twistedEllipticTransform_eq_zero_of_odd (O : GL (Fin 2) ℂ → ℂ) (hO : ∀ g, O (conjEntries g) = -O g)
    (r θ : ℝ) : twistedEllipticTransform O r θ = 0 := by
  unfold twistedEllipticTransform
  split_ifs with hr
  · rw [integral_twistedEllipticElt_bracket_eq_zero_of_odd
      (fun m => unitaryAverage fun k => O (k⁻¹ * m * conjEntries k)) (odd_unitaryAverage_twistedConj O hO) r θ hr,
      mul_zero]
  · rfl

end AutomorphicForm.GL2Twisted.OddInputs

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff WindowedSiegel.IsRowIsometry GL2Twisted.conjEntries"
namespace GL2Twisted
p2m_export "AutomorphicForm.GL2Twisted" "unitaryElt unitaryAverage conjEntries twistedSplitElt twistedSplitTransform twistedEllipticElt twistedEllipticTransform invFrobSq invTraceNorm invSecondRe invAbsDet invDifference monomialInput fibreMonomialFactor fibreArcIntegral ellipticArcLength ellipticFibreTerm splitFibreTerm ellipticFibreSide splitFibreSide twistedTransforms_monomialInput_eq_fibreSides ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing unitaryAverage_translate"
namespace MonomialBounds
p2m_open "AutomorphicForm.GL2Twisted AutomorphicForm"

section invariantsAlongRepresentatives

private theorem conjTranspose_fin_two_of (a b c d : ℂ) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose =
      !![(starRingEnd ℂ) a, (starRingEnd ℂ) c; (starRingEnd ℂ) b, (starRingEnd ℂ) d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem map_conj_fin_two_of (a b c d : ℂ) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) =
      !![(starRingEnd ℂ) a, (starRingEnd ℂ) b; (starRingEnd ℂ) c, (starRingEnd ℂ) d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem coe_conjEntries (g : GL (Fin 2) ℂ) :
    ((conjEntries g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) := rfl

private theorem coe_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    ((twistedSplitElt a₁ a₂ v h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.sqrt a₁ : ℂ), v; 0, (Real.sqrt a₂ : ℂ)] := rfl

private theorem coe_twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    ((twistedEllipticElt r θ ρ u hr hρ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.sqrt r : ℂ) * (-(u * ρ * Complex.exp (-(θ / 2 * Complex.I)))),
          (Real.sqrt r : ℂ) * ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) -
            (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I)));
        (Real.sqrt r : ℂ) * (ρ * Complex.exp (-(θ / 2 * Complex.I))),
          (Real.sqrt r : ℂ) * ((starRingEnd ℂ) u * ρ * Complex.exp (-(θ / 2 * Complex.I)))] := rfl

private theorem norm_monomialInput_le_one_of (i l : ℕ) (g : GL (Fin 2) ℂ)
    (h₁ : 0 ≤ invFrobSq g - (invTraceNorm g).re + invDifference g)
    (h₂ : invFrobSq g - (invTraceNorm g).re + invDifference g ≤ 2 * (invFrobSq g + 2 * invAbsDet g))
    (h₃ : 0 ≤ invFrobSq g - (invTraceNorm g).re - invDifference g)
    (h₄ : invFrobSq g - (invTraceNorm g).re - invDifference g ≤ 2 * (invFrobSq g - 2 * invAbsDet g)) :
    ‖monomialInput i l g‖ ≤ 1 := by
  have hb₁ : 0 ≤ (invFrobSq g - (invTraceNorm g).re + invDifference g) /
      (2 * (invFrobSq g + 2 * invAbsDet g)) := div_nonneg h₁ (by linarith)
  have hb₂ : 0 ≤ (invFrobSq g - (invTraceNorm g).re - invDifference g) /
      (2 * (invFrobSq g - 2 * invAbsDet g)) := div_nonneg h₃ (by linarith)
  have hc₁ : (invFrobSq g - (invTraceNorm g).re + invDifference g) /
      (2 * (invFrobSq g + 2 * invAbsDet g)) ≤ 1 := div_le_one_of_le₀ h₂ (by linarith)
  have hc₂ : (invFrobSq g - (invTraceNorm g).re - invDifference g) /
      (2 * (invFrobSq g - 2 * invAbsDet g)) ≤ 1 := div_le_one_of_le₀ h₄ (by linarith)
  unfold monomialInput
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hb₁ i) (pow_nonneg hb₂ l))]
  exact mul_le_one₀ (pow_le_one₀ hb₁ hc₁) (pow_nonneg hb₂ l) (pow_le_one₀ hb₂ hc₂)

private theorem invFrobSq_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    invFrobSq (twistedSplitElt a₁ a₂ v h) = Real.sqrt a₁ ^ 2 + Real.sqrt a₂ ^ 2 + Complex.normSq v := by
  have hc : Matrix.trace ((twistedSplitElt a₁ a₂ v h : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.conjTranspose (twistedSplitElt a₁ a₂ v h : Matrix (Fin 2) (Fin 2) ℂ)) =
      ((Real.sqrt a₁ ^ 2 + Real.sqrt a₂ ^ 2 + Complex.normSq v : ℝ) : ℂ) := by
    rw [coe_twistedSplitElt, conjTranspose_fin_two_of, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
    push_cast
    rw [← Complex.mul_conj]
    simp only [Complex.conj_ofReal]
    ring
  unfold invFrobSq
  rw [hc, Complex.ofReal_re]

private theorem invTraceNorm_re_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    (invTraceNorm (twistedSplitElt a₁ a₂ v h)).re = Real.sqrt a₁ ^ 2 + Real.sqrt a₂ ^ 2 := by
  have hc : Matrix.trace ((twistedSplitElt a₁ a₂ v h * conjEntries (twistedSplitElt a₁ a₂ v h) : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = ((Real.sqrt a₁ ^ 2 + Real.sqrt a₂ ^ 2 : ℝ) : ℂ) := by
    rw [Units.val_mul, coe_conjEntries, coe_twistedSplitElt, map_conj_fin_two_of, Matrix.mul_fin_two,
      Matrix.trace_fin_two_of]
    push_cast
    simp only [Complex.conj_ofReal, map_zero]
    ring
  unfold invTraceNorm
  rw [hc, Complex.ofReal_re]

private theorem invSecondRe_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    invSecondRe (twistedSplitElt a₁ a₂ v h) =
      Complex.normSq v * (Real.sqrt a₁ ^ 2 + Real.sqrt a₂ ^ 2) + Real.sqrt a₁ ^ 4 + Real.sqrt a₂ ^ 4 +
        Real.sqrt a₁ * Real.sqrt a₂ * (v.re ^ 2 - v.im ^ 2) := by
  have hc : Matrix.trace (((twistedSplitElt a₁ a₂ v h * conjEntries (twistedSplitElt a₁ a₂ v h) : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) * ((twistedSplitElt a₁ a₂ v h : Matrix (Fin 2) (Fin 2) ℂ) *
        Matrix.conjTranspose (twistedSplitElt a₁ a₂ v h : Matrix (Fin 2) (Fin 2) ℂ))) =
      ((Complex.normSq v * (Real.sqrt a₁ ^ 2 + Real.sqrt a₂ ^ 2) + Real.sqrt a₁ ^ 4 + Real.sqrt a₂ ^ 4 : ℝ) : ℂ) +
        ((Real.sqrt a₁ * Real.sqrt a₂ : ℝ) : ℂ) * ((starRingEnd ℂ) v) ^ 2 := by
    rw [Units.val_mul, coe_conjEntries, coe_twistedSplitElt, map_conj_fin_two_of, conjTranspose_fin_two_of,
      Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
    push_cast
    rw [← Complex.mul_conj]
    simp only [Complex.conj_ofReal, map_zero]
    ring
  have hre : (((starRingEnd ℂ) v) ^ 2).re = v.re ^ 2 - v.im ^ 2 := by
    simp [sq, Complex.mul_re]
  unfold invSecondRe
  rw [hc, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre]

private theorem invAbsDet_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    invAbsDet (twistedSplitElt a₁ a₂ v h) = Real.sqrt a₁ * Real.sqrt a₂ := by
  unfold invAbsDet
  rw [coe_twistedSplitElt, Matrix.det_fin_two_of]
  simp only [mul_zero, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg a₁), abs_of_nonneg (Real.sqrt_nonneg a₂)]

private theorem invDifference_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    invDifference (twistedSplitElt a₁ a₂ v h) = v.re ^ 2 - v.im ^ 2 := by
  have h₁ : Real.sqrt a₁ ≠ 0 := (Real.sqrt_pos.mpr h.1).ne'
  have h₂ : Real.sqrt a₂ ≠ 0 := (Real.sqrt_pos.mpr h.2).ne'
  unfold invDifference
  rw [invSecondRe_twistedSplitElt, invFrobSq_twistedSplitElt, invTraceNorm_re_twistedSplitElt,
    invAbsDet_twistedSplitElt]
  field_simp
  ring

private theorem norm_monomialInput_twistedSplitElt_le_one (i l : ℕ) (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    ‖monomialInput i l (twistedSplitElt a₁ a₂ v h)‖ ≤ 1 := by
  apply norm_monomialInput_le_one_of <;>
    simp only [invFrobSq_twistedSplitElt, invTraceNorm_re_twistedSplitElt, invDifference_twistedSplitElt,
      invAbsDet_twistedSplitElt, Complex.normSq_apply] <;>
    nlinarith [sq_nonneg v.re, sq_nonneg v.im, sq_nonneg (Real.sqrt a₁ + Real.sqrt a₂),
      sq_nonneg (Real.sqrt a₁ - Real.sqrt a₂)]

private theorem measurable_monomialInput_twistedSplitElt (i l : ℕ) (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) :
    Measurable fun v : ℂ => monomialInput i l (twistedSplitElt a₁ a₂ v h) := by
  simp only [monomialInput, invFrobSq_twistedSplitElt, invTraceNorm_re_twistedSplitElt,
    invDifference_twistedSplitElt, invAbsDet_twistedSplitElt]
  have hn : Measurable fun v : ℂ => Complex.normSq v := Complex.continuous_normSq.measurable
  fun_prop

private theorem conj_exp_neg_half (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(θ / 2 * Complex.I))) = Complex.exp (θ / 2 * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I, map_ofNat]

private theorem conj_exp_half (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (θ / 2 * Complex.I)) = Complex.exp (-(θ / 2 * Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I, map_ofNat]

private theorem exp_neg_half_eq_inv (θ : ℝ) :
    Complex.exp (-(θ / 2 * Complex.I)) = (Complex.exp (θ / 2 * Complex.I))⁻¹ :=
  Complex.exp_neg _

private theorem cos_eq_half_exp_sq_add (θ : ℝ) :
    Complex.cos θ =
      (Complex.exp (-(θ / 2 * Complex.I)) ^ 2 + Complex.exp (θ / 2 * Complex.I) ^ 2) / 2 := by
  have h₁ : Complex.exp (-(θ / 2 * Complex.I)) ^ 2 = Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [sq, ← Complex.exp_add]; congr 1; ring
  have h₂ : Complex.exp (θ / 2 * Complex.I) ^ 2 = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [sq, ← Complex.exp_add]; congr 1; ring
  rw [h₁, h₂, Complex.cos, add_comm]

private theorem re_exp_sq_sub_exp_sq (θ : ℝ) :
    ((Complex.exp (-(θ / 2 * Complex.I)) ^ 2 - Complex.exp (θ / 2 * Complex.I) ^ 2) / 2).re = 0 := by
  have h₁ : Complex.exp (-(θ / 2 * Complex.I)) ^ 2 = Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [sq, ← Complex.exp_add]; congr 1; ring
  have h₂ : Complex.exp (θ / 2 * Complex.I) ^ 2 = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [sq, ← Complex.exp_add]; congr 1; ring
  rw [h₁, h₂]
  simp [Complex.exp_re]

private theorem invTraceNorm_re_twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    (invTraceNorm (twistedEllipticElt r θ ρ u hr hρ)).re = Real.sqrt r ^ 2 * (2 * Real.cos θ) := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hE : Complex.exp (θ / 2 * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hc : Matrix.trace ((twistedEllipticElt r θ ρ u hr hρ * conjEntries (twistedEllipticElt r θ ρ u hr hρ) :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = ((Real.sqrt r ^ 2 * (2 * Real.cos θ) : ℝ) : ℂ) := by
    rw [Units.val_mul, coe_conjEntries, coe_twistedEllipticElt, map_conj_fin_two_of, Matrix.mul_fin_two,
      Matrix.trace_fin_two_of]
    simp only [map_mul, map_neg, map_sub, map_inv₀, Complex.conj_ofReal, Complex.conj_conj, conj_exp_neg_half,
      conj_exp_half]
    push_cast
    rw [cos_eq_half_exp_sq_add, exp_neg_half_eq_inv, ← Complex.mul_conj]
    field_simp
    ring
  unfold invTraceNorm
  rw [hc, Complex.ofReal_re]

private theorem invFrobSq_twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    invFrobSq (twistedEllipticElt r θ ρ u hr hρ) =
      Real.sqrt r ^ 2 * (ρ ^ 2 * (Complex.normSq u + 1) ^ 2 - 2 * Complex.normSq u * Real.cos θ + ρ⁻¹ ^ 2) := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hE : Complex.exp (θ / 2 * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hc : Matrix.trace ((twistedEllipticElt r θ ρ u hr hρ : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.conjTranspose (twistedEllipticElt r θ ρ u hr hρ : Matrix (Fin 2) (Fin 2) ℂ)) =
      ((Real.sqrt r ^ 2 * (ρ ^ 2 * (Complex.normSq u + 1) ^ 2 - 2 * Complex.normSq u * Real.cos θ + ρ⁻¹ ^ 2) : ℝ) :
        ℂ) := by
    rw [coe_twistedEllipticElt, conjTranspose_fin_two_of, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
    simp only [map_mul, map_neg, map_sub, map_inv₀, Complex.conj_ofReal, Complex.conj_conj, conj_exp_neg_half,
      conj_exp_half]
    push_cast
    rw [cos_eq_half_exp_sq_add, exp_neg_half_eq_inv, ← Complex.mul_conj]
    field_simp
    ring
  unfold invFrobSq
  rw [hc, Complex.ofReal_re]

private theorem invSecondRe_twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    invSecondRe (twistedEllipticElt r θ ρ u hr hρ) =
      Real.sqrt r ^ 4 * (Real.cos θ * (ρ ^ 2 * (Complex.normSq u + 1) ^ 2 + ρ⁻¹ ^ 2) -
        4 * Complex.normSq u * Real.cos θ ^ 2 + 2 * Complex.normSq u) := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hE : Complex.exp (θ / 2 * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hc : Matrix.trace (((twistedEllipticElt r θ ρ u hr hρ * conjEntries (twistedEllipticElt r θ ρ u hr hρ) :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((twistedEllipticElt r θ ρ u hr hρ : Matrix (Fin 2) (Fin 2) ℂ) *
        Matrix.conjTranspose (twistedEllipticElt r θ ρ u hr hρ : Matrix (Fin 2) (Fin 2) ℂ))) =
      ((Real.sqrt r ^ 4 * (Real.cos θ * (ρ ^ 2 * (Complex.normSq u + 1) ^ 2 + ρ⁻¹ ^ 2) -
        4 * Complex.normSq u * Real.cos θ ^ 2 + 2 * Complex.normSq u) : ℝ) : ℂ) +
      ((Real.sqrt r ^ 4 * (ρ ^ 2 * (Complex.normSq u + 1) ^ 2 - ρ⁻¹ ^ 2) : ℝ) : ℂ) *
        ((Complex.exp (-(θ / 2 * Complex.I)) ^ 2 - Complex.exp (θ / 2 * Complex.I) ^ 2) / 2) := by
    rw [Units.val_mul, coe_conjEntries, coe_twistedEllipticElt, map_conj_fin_two_of, conjTranspose_fin_two_of,
      Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
    simp only [map_mul, map_neg, map_sub, map_inv₀, Complex.conj_ofReal, Complex.conj_conj, conj_exp_neg_half,
      conj_exp_half]
    push_cast
    rw [cos_eq_half_exp_sq_add, exp_neg_half_eq_inv, ← Complex.mul_conj]
    field_simp
    ring
  unfold invSecondRe
  rw [hc, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, re_exp_sq_sub_exp_sq, mul_zero, add_zero]

private theorem invAbsDet_twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    invAbsDet (twistedEllipticElt r θ ρ u hr hρ) = Real.sqrt r ^ 2 := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hE : Complex.exp (θ / 2 * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hdet : Matrix.det (twistedEllipticElt r θ ρ u hr hρ : Matrix (Fin 2) (Fin 2) ℂ) =
      -((Real.sqrt r : ℂ) ^ 2) := by
    rw [coe_twistedEllipticElt, Matrix.det_fin_two_of, exp_neg_half_eq_inv]
    rw [← Complex.mul_conj]
    field_simp
    ring
  unfold invAbsDet
  rw [hdet, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg r)]

private theorem norm_monomialInput_twistedEllipticElt_le_one (i l : ℕ) (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    ‖monomialInput i l (twistedEllipticElt r θ ρ u hr hρ)‖ ≤ 1 := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hs' : Real.sqrt r ≠ 0 := hs.ne'
  have hρ' : ρ ≠ 0 := hρ.ne'
  have hm : 0 ≤ Complex.normSq u := Complex.normSq_nonneg u
  have hc₁ : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  have hc₂ : 0 ≤ 1 + Real.cos θ := by linarith [Real.neg_one_le_cos θ]
  have hs2 : 0 ≤ Real.sqrt r ^ 2 := sq_nonneg _
  have k₁ : invFrobSq (twistedEllipticElt r θ ρ u hr hρ) - (invTraceNorm (twistedEllipticElt r θ ρ u hr hρ)).re +
      invDifference (twistedEllipticElt r θ ρ u hr hρ) =
      Real.sqrt r ^ 2 * (1 - Real.cos θ) * (ρ * (Complex.normSq u + 1) + ρ⁻¹) ^ 2 := by
    unfold invDifference
    rw [invFrobSq_twistedEllipticElt, invTraceNorm_re_twistedEllipticElt, invSecondRe_twistedEllipticElt,
      invAbsDet_twistedEllipticElt]
    field_simp
    ring
  have k₂ : 2 * (invFrobSq (twistedEllipticElt r θ ρ u hr hρ) + 2 * invAbsDet (twistedEllipticElt r θ ρ u hr hρ)) -
      (invFrobSq (twistedEllipticElt r θ ρ u hr hρ) - (invTraceNorm (twistedEllipticElt r θ ρ u hr hρ)).re +
        invDifference (twistedEllipticElt r θ ρ u hr hρ)) =
      Real.sqrt r ^ 2 * (1 + Real.cos θ) * ((ρ * (Complex.normSq u + 1) - ρ⁻¹) ^ 2 + 4) := by
    unfold invDifference
    rw [invFrobSq_twistedEllipticElt, invTraceNorm_re_twistedEllipticElt, invSecondRe_twistedEllipticElt,
      invAbsDet_twistedEllipticElt]
    field_simp
    ring
  have k₃ : invFrobSq (twistedEllipticElt r θ ρ u hr hρ) - (invTraceNorm (twistedEllipticElt r θ ρ u hr hρ)).re -
      invDifference (twistedEllipticElt r θ ρ u hr hρ) =
      Real.sqrt r ^ 2 * (1 + Real.cos θ) * (ρ * (Complex.normSq u + 1) - ρ⁻¹) ^ 2 := by
    unfold invDifference
    rw [invFrobSq_twistedEllipticElt, invTraceNorm_re_twistedEllipticElt, invSecondRe_twistedEllipticElt,
      invAbsDet_twistedEllipticElt]
    field_simp
    ring
  have k₄ : 2 * (invFrobSq (twistedEllipticElt r θ ρ u hr hρ) - 2 * invAbsDet (twistedEllipticElt r θ ρ u hr hρ)) -
      (invFrobSq (twistedEllipticElt r θ ρ u hr hρ) - (invTraceNorm (twistedEllipticElt r θ ρ u hr hρ)).re -
        invDifference (twistedEllipticElt r θ ρ u hr hρ)) =
      Real.sqrt r ^ 2 * (1 - Real.cos θ) * ((ρ * (Complex.normSq u + 1) - ρ⁻¹) ^ 2 + 4 * Complex.normSq u) := by
    unfold invDifference
    rw [invFrobSq_twistedEllipticElt, invTraceNorm_re_twistedEllipticElt, invSecondRe_twistedEllipticElt,
      invAbsDet_twistedEllipticElt]
    field_simp
    ring
  have n₁ : 0 ≤ Real.sqrt r ^ 2 * (1 - Real.cos θ) * (ρ * (Complex.normSq u + 1) + ρ⁻¹) ^ 2 :=
    mul_nonneg (mul_nonneg hs2 hc₁) (sq_nonneg _)
  have n₂ : 0 ≤ Real.sqrt r ^ 2 * (1 + Real.cos θ) * ((ρ * (Complex.normSq u + 1) - ρ⁻¹) ^ 2 + 4) :=
    mul_nonneg (mul_nonneg hs2 hc₂) (by positivity)
  have n₃ : 0 ≤ Real.sqrt r ^ 2 * (1 + Real.cos θ) * (ρ * (Complex.normSq u + 1) - ρ⁻¹) ^ 2 :=
    mul_nonneg (mul_nonneg hs2 hc₂) (sq_nonneg _)
  have n₄ : 0 ≤ Real.sqrt r ^ 2 * (1 - Real.cos θ) *
      ((ρ * (Complex.normSq u + 1) - ρ⁻¹) ^ 2 + 4 * Complex.normSq u) :=
    mul_nonneg (mul_nonneg hs2 hc₁) (by positivity)
  exact norm_monomialInput_le_one_of i l _ (by linarith) (by linarith) (by linarith) (by linarith)

private theorem measurable_monomialInput_twistedEllipticElt (i l : ℕ) (r θ : ℝ) (hr : 0 < r) :
    Measurable fun p : ℝ × ℂ =>
      if hρ : 0 < p.1 then monomialInput i l (twistedEllipticElt r θ p.1 p.2 hr hρ) else 0 := by
  simp only [monomialInput, invDifference, invFrobSq_twistedEllipticElt, invTraceNorm_re_twistedEllipticElt,
    invSecondRe_twistedEllipticElt, invAbsDet_twistedEllipticElt, dite_eq_ite]
  have hn : Measurable fun p : ℝ × ℂ => Complex.normSq p.2 :=
    Complex.continuous_normSq.measurable.comp measurable_snd
  have hfst : Measurable fun p : ℝ × ℂ => p.1 := measurable_fst
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  fun_prop

end invariantsAlongRepresentatives

end AutomorphicForm.GL2Twisted.MonomialBounds

end

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff WindowedSiegel.IsRowIsometry GL2Twisted.conjEntries"
namespace GL2Twisted
p2m_export "AutomorphicForm.GL2Twisted" "unitaryElt unitaryAverage conjEntries twistedSplitElt twistedSplitTransform twistedEllipticElt twistedEllipticTransform invFrobSq invTraceNorm invSecondRe invAbsDet invDifference monomialInput fibreMonomialFactor fibreArcIntegral ellipticArcLength ellipticFibreTerm splitFibreTerm ellipticFibreSide splitFibreSide twistedTransforms_monomialInput_eq_fibreSides ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing unitaryAverage_translate"
p2m_open "AutomorphicForm.GL2Twisted AutomorphicForm"
open AutomorphicForm.GL2Real

private def parameterSlice {P : Type} (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (p : P) : GL (Fin 2) ℂ → ℂ :=
  fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)

private def normDetCone : Set (ℝ × ℝ) := {q | 2 * q.2 ≤ q.1 ∧ 0 < q.2}

private def distinctSingularValues : Set (GL (Fin 2) ℂ) := {g | 2 * invAbsDet g < invFrobSq g}

private noncomputable def upperSingularValue (T d : ℝ) : ℝ :=
  Real.sqrt ((T + Real.sqrt (T ^ 2 - 4 * d ^ 2)) / 2)

private noncomputable def lowerSingularValue (T d : ℝ) : ℝ :=
  Real.sqrt ((T - Real.sqrt (T ^ 2 - 4 * d ^ 2)) / 2)

private noncomputable def singularDiagonal (T d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![((upperSingularValue T d : ℝ) : ℂ), ((lowerSingularValue T d : ℝ) : ℂ)]

private theorem singularValues_spec (T d : ℝ) (hd : 0 ≤ d) (hT : 2 * d ≤ T) :
    0 ≤ lowerSingularValue T d ∧ lowerSingularValue T d ≤ upperSingularValue T d ∧
      upperSingularValue T d ^ 2 + lowerSingularValue T d ^ 2 = T ∧
      upperSingularValue T d * lowerSingularValue T d = d := by
  have hT0 : 0 ≤ T := by linarith
  have hdisc : 0 ≤ T ^ 2 - 4 * d ^ 2 := by nlinarith
  set E := Real.sqrt (T ^ 2 - 4 * d ^ 2) with hE
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  have hE2 : E ^ 2 = T ^ 2 - 4 * d ^ 2 := Real.sq_sqrt hdisc
  have hET : E ≤ T := by
    have h := Real.sqrt_le_sqrt (show T ^ 2 - 4 * d ^ 2 ≤ T ^ 2 by nlinarith)
    rwa [Real.sqrt_sq hT0] at h
  have hlo : 0 ≤ (T - E) / 2 := by linarith
  have hup : 0 ≤ (T + E) / 2 := by linarith
  unfold upperSingularValue lowerSingularValue
  rw [← hE]
  refine ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt (by linarith), ?_, ?_⟩
  · rw [Real.sq_sqrt hup, Real.sq_sqrt hlo]
    ring
  · have hprod : (T + E) / 2 * ((T - E) / 2) = d ^ 2 := by
      rw [show (T + E) / 2 * ((T - E) / 2) = (T ^ 2 - E ^ 2) / 4 by ring, hE2]
      ring
    rw [← Real.sqrt_mul hup, hprod, Real.sqrt_sq hd]

private theorem lowerSingularValue_pos (T d : ℝ) (hd : 0 < d) (hT : 2 * d ≤ T) : 0 < lowerSingularValue T d := by
  have hT0 : 0 < T := by linarith
  have hdisc : 0 ≤ T ^ 2 - 4 * d ^ 2 := by nlinarith
  have hlt : Real.sqrt (T ^ 2 - 4 * d ^ 2) < T := by
    have h := Real.sqrt_lt_sqrt hdisc (show T ^ 2 - 4 * d ^ 2 < T ^ 2 by nlinarith)
    rwa [Real.sqrt_sq hT0.le] at h
  unfold lowerSingularValue
  exact Real.sqrt_pos.mpr (by linarith)

private theorem lowerSingularValue_lt_upperSingularValue (T d : ℝ) (hd : 0 ≤ d) (hT : 2 * d < T) :
    lowerSingularValue T d < upperSingularValue T d := by
  have hT0 : 0 < T := by linarith
  have hpos : 0 < Real.sqrt (T ^ 2 - 4 * d ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hET : Real.sqrt (T ^ 2 - 4 * d ^ 2) ≤ T := by
    have h := Real.sqrt_le_sqrt (show T ^ 2 - 4 * d ^ 2 ≤ T ^ 2 by nlinarith)
    rwa [Real.sqrt_sq hT0.le] at h
  unfold lowerSingularValue upperSingularValue
  exact Real.sqrt_lt_sqrt (by linarith) (by linarith)

private theorem continuous_upperSingularValue : Continuous fun q : ℝ × ℝ => upperSingularValue q.1 q.2 := by
  unfold upperSingularValue
  exact ((continuous_fst.add ((continuous_fst.pow 2).sub
    (continuous_const.mul (continuous_snd.pow 2))).sqrt).div_const 2).sqrt

private theorem continuous_lowerSingularValue : Continuous fun q : ℝ × ℝ => lowerSingularValue q.1 q.2 := by
  unfold lowerSingularValue
  exact ((continuous_fst.sub ((continuous_fst.pow 2).sub
    (continuous_const.mul (continuous_snd.pow 2))).sqrt).div_const 2).sqrt

private theorem invAbsDet_pos (g : GL (Fin 2) ℂ) : 0 < invAbsDet g := by
  unfold invAbsDet
  exact norm_pos_iff.mpr (Matrix.isUnits_det_units g).ne_zero

private theorem two_mul_invAbsDet_le_invFrobSq (g : GL (Fin 2) ℂ) : 2 * invAbsDet g ≤ invFrobSq g := by
  unfold invAbsDet invFrobSq
  set A : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ)
  have hre : ∀ z : ℂ, (z * star z).re = ‖z‖ ^ 2 := by
    intro z
    rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have htr : (Matrix.trace (A * Matrix.conjTranspose A)).re =
      ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) := by
    simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.add_re, hre]
  have hdet : ‖A.det‖ ≤ ‖A 0 0‖ * ‖A 1 1‖ + ‖A 0 1‖ * ‖A 1 0‖ := by
    rw [Matrix.det_fin_two]
    exact (norm_sub_le _ _).trans (by rw [norm_mul, norm_mul])
  rw [htr]
  nlinarith [hdet, sq_nonneg (‖A 0 0‖ - ‖A 1 1‖), sq_nonneg (‖A 0 1‖ - ‖A 1 0‖), norm_nonneg A.det,
    norm_nonneg (A 0 0), norm_nonneg (A 1 1), norm_nonneg (A 0 1), norm_nonneg (A 1 0)]

private theorem det_singularDiagonal (T d : ℝ) (hd : 0 ≤ d) (hT : 2 * d ≤ T) :
    Matrix.det (singularDiagonal T d) = (d : ℂ) := by
  obtain ⟨-, -, -, hprod⟩ := singularValues_spec T d hd hT
  simp only [singularDiagonal, Matrix.det_diagonal, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [← Complex.ofReal_mul, hprod]

private theorem exists_decomposition_of_ordered_eigenvalues (g : GL (Fin 2) ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (μ : Fin 2 → ℝ)
    (hUU : star U * U = 1) (hUU' : U * star U = 1) (h10 : μ 1 ≤ μ 0) (h1 : 0 ≤ μ 1)
    (hspec : Matrix.conjTranspose (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) =
      U * Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ)) * star U)
    (hsum : μ 0 + μ 1 = invFrobSq g) (hprod : μ 0 * μ 1 = invAbsDet g ^ 2) :
    ∃ k₁ k₂ : GL (Fin 2) ℂ,
      star (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
      star (k₂ : Matrix (Fin 2) (Fin 2) ℂ) * (k₂ : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
      Matrix.det (k₂ : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) ℂ) =
        (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal (invFrobSq g) (invAbsDet g) *
          (k₂ : Matrix (Fin 2) (Fin 2) ℂ) := by
  classical
  set A : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) with hA
  set T : ℝ := invFrobSq g with hT
  set d : ℝ := invAbsDet g with hd
  set D : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ)) with hD
  have hd0 : 0 < d := invAbsDet_pos g
  set E : ℝ := μ 0 - μ 1 with hE
  have hE0 : 0 ≤ E := by linarith
  have hdisc : T ^ 2 - 4 * d ^ 2 = E ^ 2 := by
    rw [← hsum, ← hprod, hE]
    ring
  have hsq : Real.sqrt (T ^ 2 - 4 * d ^ 2) = E := by rw [hdisc, Real.sqrt_sq hE0]
  have hup : upperSingularValue T d = Real.sqrt (μ 0) := by
    unfold upperSingularValue
    rw [hsq, ← hsum, hE]
    congr 1
    ring
  have hlo : lowerSingularValue T d = Real.sqrt (μ 1) := by
    unfold lowerSingularValue
    rw [hsq, ← hsum, hE]
    congr 1
    ring
  have hμ1 : 0 < μ 1 := by
    rcases h1.lt_or_eq with h | h
    · exact h
    · exfalso
      have : d ^ 2 = 0 := by rw [← hprod, ← h, mul_zero]
      nlinarith
  have hμ0 : 0 < μ 0 := lt_of_lt_of_le hμ1 h10
  set a : ℝ := Real.sqrt (μ 0) with ha
  set b : ℝ := Real.sqrt (μ 1) with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr hμ0
  have hb0 : 0 < b := Real.sqrt_pos.mpr hμ1
  have ha2 : a ^ 2 = μ 0 := Real.sq_sqrt hμ0.le
  have hb2 : b ^ 2 = μ 1 := Real.sq_sqrt hμ1.le
  have haC : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb0.ne'
  have hS : singularDiagonal T d = Matrix.diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)] := by
    unfold singularDiagonal
    rw [hup, hlo]
  set Sinv : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![((a : ℝ) : ℂ)⁻¹, ((b : ℝ) : ℂ)⁻¹] with hSinv
  have hSinvS : Sinv * Matrix.diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)] = 1 := by
    rw [hSinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [haC, hbC]
  have hSinv_star : star Sinv = Sinv := by
    rw [hSinv, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    fin_cases i <;> simp
  have hmid : Sinv * D * Sinv = 1 := by
    rw [hSinv, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [← ha2, Complex.ofReal_pow]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← hb2, Complex.ofReal_pow]
      field_simp
  have hinner : star U * (U * D * star U) * U = D := by
    calc star U * (U * D * star U) * U = (star U * U) * D * (star U * U) := by
          simp only [Matrix.mul_assoc]
      _ = D := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
  have hK1 : star (A * U * Sinv) * (A * U * Sinv) = 1 := by
    rw [StarMul.star_mul, StarMul.star_mul, hSinv_star, Matrix.star_eq_conjTranspose A]
    calc Sinv * (star U * Matrix.conjTranspose A) * (A * U * Sinv)
          = Sinv * (star U * (Matrix.conjTranspose A * A) * U) * Sinv := by
          simp only [Matrix.mul_assoc]
      _ = Sinv * D * Sinv := by rw [hspec, hinner]
      _ = 1 := hmid
  have hK1eq : A * U * Sinv * Matrix.diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)] * star U = A := by
    calc A * U * Sinv * Matrix.diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)] * star U
          = A * U * (Sinv * Matrix.diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)]) * star U := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [hSinvS, Matrix.mul_one, Matrix.mul_assoc, hUU', Matrix.mul_one]
  have hdetU : Matrix.det (star U) * Matrix.det U = 1 := by rw [← Matrix.det_mul, hUU, Matrix.det_one]
  have hδ : Matrix.det (star U) ≠ 0 := left_ne_zero_of_mul_eq_one hdetU
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq (Matrix.det (star U))⁻¹ (show 0 < 2 by norm_num)
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hlam
    exact inv_ne_zero hδ hlam.symm
  have hstarU : Matrix.det (star U) = (starRingEnd ℂ) (Matrix.det U) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
    rfl
  have hnormU : Complex.normSq (Matrix.det U) = 1 := by
    have h' : ((Complex.normSq (Matrix.det U) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self, ← hstarU]
      exact hdetU
    exact_mod_cast h'
  have hnormlam : Complex.normSq lam = 1 := by
    have h2 : Complex.normSq lam ^ 2 = 1 := by
      rw [← map_pow, hlam, map_inv₀, hstarU, Complex.normSq_conj, hnormU, inv_one]
    nlinarith [Complex.normSq_nonneg lam]
  have hstarlam : star lam * lam = 1 := by
    rw [show star lam = (starRingEnd ℂ) lam from rfl, ← Complex.normSq_eq_conj_mul_self, hnormlam,
      Complex.ofReal_one]
  set K₂ : Matrix (Fin 2) (Fin 2) ℂ := lam • star U with hK2
  set K₁ : Matrix (Fin 2) (Fin 2) ℂ := lam⁻¹ • (A * U * Sinv) with hK1d
  have hK2det : Matrix.det K₂ = 1 := by
    rw [hK2, Matrix.det_smul, Fintype.card_fin, hlam, inv_mul_cancel₀ hδ]
  have hK2u : star K₂ * K₂ = 1 := by
    rw [hK2, star_smul, star_star, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hUU', hstarlam, one_smul]
  have hK1u : star K₁ * K₁ = 1 := by
    rw [hK1d, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hK1]
    have h3 : star lam⁻¹ * lam⁻¹ = 1 := by rw [star_inv₀, ← mul_inv, hstarlam, inv_one]
    rw [h3, one_smul]
  have hK1det : Matrix.det K₁ ≠ 0 := by
    have h4 := congrArg Matrix.det hK1u
    rw [Matrix.det_mul, Matrix.det_one] at h4
    exact right_ne_zero_of_mul_eq_one h4
  have hK2det0 : Matrix.det K₂ ≠ 0 := by
    rw [hK2det]
    exact one_ne_zero
  have heq : K₁ * singularDiagonal T d * K₂ = A := by
    rw [hS, hK1d, hK2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hlam0,
      one_smul, hK1eq]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero K₁ hK1det, Matrix.GeneralLinearGroup.mkOfDetNeZero K₂ hK2det0,
    hK1u, hK2u, hK2det, ?_⟩
  exact heq.symm

open scoped ComplexOrder in
private theorem exists_unitary_mul_singularDiagonal_mul_unitary (g : GL (Fin 2) ℂ) :
    ∃ k₁ k₂ : GL (Fin 2) ℂ,
      star (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
      star (k₂ : Matrix (Fin 2) (Fin 2) ℂ) * (k₂ : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
      Matrix.det (k₂ : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) ℂ) =
        (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal (invFrobSq g) (invAbsDet g) *
          (k₂ : Matrix (Fin 2) (Fin 2) ℂ) := by
  classical
  have hP : (Matrix.conjTranspose (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self _
  have hUU :
      star (hP.1.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) *
        (hP.1.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem hP.1.eigenvectorUnitary.2
  have hUU' :
      (hP.1.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) *
        star (hP.1.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Unitary.mul_star_self_of_mem hP.1.eigenvectorUnitary.2
  have hspec : Matrix.conjTranspose (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (hP.1.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) *
          Matrix.diagonal (fun i => ((hP.1.eigenvalues i : ℝ) : ℂ)) *
        star (hP.1.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) := by
    have h := hP.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_eq_complex_ofReal] at h
    exact h
  have hnn : ∀ i, 0 ≤ hP.1.eigenvalues i := hP.eigenvalues_nonneg
  have hsum : hP.1.eigenvalues 0 + hP.1.eigenvalues 1 = invFrobSq g := by
    have h1 := hP.1.trace_eq_sum_eigenvalues
    rw [Fin.sum_univ_two] at h1
    have h2 : invFrobSq g =
        (Matrix.trace (Matrix.conjTranspose (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ))).re := by
      unfold invFrobSq
      rw [Matrix.trace_mul_comm]
    rw [h2, h1]
    show hP.1.eigenvalues 0 + hP.1.eigenvalues 1 =
      (((hP.1.eigenvalues 0 : ℝ) : ℂ) + ((hP.1.eigenvalues 1 : ℝ) : ℂ)).re
    rw [Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]
  have hprod : hP.1.eigenvalues 0 * hP.1.eigenvalues 1 = invAbsDet g ^ 2 := by
    have h3 := hP.1.det_eq_prod_eigenvalues
    rw [Fin.prod_univ_two, Matrix.det_mul, Matrix.det_conjTranspose] at h3
    have h4 : ((invAbsDet g ^ 2 : ℝ) : ℂ) = ((hP.1.eigenvalues 0 * hP.1.eigenvalues 1 : ℝ) : ℂ) := by
      unfold invAbsDet
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, Complex.ofReal_mul]
      exact h3
    exact_mod_cast h4.symm
  rcases le_total (hP.1.eigenvalues 1) (hP.1.eigenvalues 0) with h10 | h01
  · exact exists_decomposition_of_ordered_eigenvalues g _ _ hUU hUU' h10 (hnn 1) hspec hsum hprod
  ·
    set U : Matrix (Fin 2) (Fin 2) ℂ := (hP.1.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) with hU
    set μ : Fin 2 → ℝ := hP.1.eigenvalues with hμ
    set P : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0] with hPdef
    have hPP : P * P = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hPdef, Matrix.mul_apply, Fin.sum_univ_two]
    have hPstar : star P = P := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hPdef, Matrix.star_apply]
    have hP00 : P 0 0 = 0 := by simp [hPdef]
    have hP01 : P 0 1 = 1 := by simp [hPdef]
    have hP10 : P 1 0 = 1 := by simp [hPdef]
    have hP11 : P 1 1 = 0 := by simp [hPdef]
    have hswap : P * Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ)) * P =
        Matrix.diagonal (fun i => ((μ (Equiv.swap (0 : Fin 2) 1 i) : ℝ) : ℂ)) := by
      ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;>
        simp [hP00, hP01, hP10, hP11, Matrix.diagonal_apply_ne, Equiv.swap_apply_left, Equiv.swap_apply_right]
    refine exists_decomposition_of_ordered_eigenvalues g (U * P) (fun i => μ (Equiv.swap (0 : Fin 2) 1 i))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [StarMul.star_mul, hPstar]
      calc P * star U * (U * P) = P * (star U * U) * P := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hUU, Matrix.mul_one, hPP]
    · rw [StarMul.star_mul, hPstar]
      calc U * P * (P * star U) = U * (P * P) * star U := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hPP, Matrix.mul_one, hUU']
    · simpa using h01
    · simpa using hnn 0
    · rw [hspec, StarMul.star_mul, hPstar, ← hswap]
      symm
      calc U * P * (P * Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ)) * P) * (P * star U)
            = U * (P * P) * Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ)) * (P * P) * star U := by
            simp only [Matrix.mul_assoc]
        _ = U * Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ)) * star U := by
            rw [hPP, Matrix.mul_one, Matrix.mul_one]
    · simpa [add_comm] using hsum
    · simpa [mul_comm] using hprod

private theorem coe_inv_mul_mul_inv_eq_singularDiagonal (g k₁ k₂ : GL (Fin 2) ℂ)
    (h : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal (invFrobSq g) (invAbsDet g) *
        (k₂ : Matrix (Fin 2) (Fin 2) ℂ)) :
    ((k₁⁻¹ * g * k₂⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      singularDiagonal (invFrobSq g) (invAbsDet g) := by
  have h1 : ((k₁⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (k₂ : Matrix (Fin 2) (Fin 2) ℂ) * ((k₂⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul, h]
  calc ((k₁⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((k₁ : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal (invFrobSq g) (invAbsDet g) *
          (k₂ : Matrix (Fin 2) (Fin 2) ℂ)) *
        ((k₂⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        = ((k₁⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) *
            singularDiagonal (invFrobSq g) (invAbsDet g) *
            ((k₂ : Matrix (Fin 2) (Fin 2) ℂ) * ((k₂⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = singularDiagonal (invFrobSq g) (invAbsDet g) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

private theorem exp_mul_mul_exp_neg (θ : ℝ) (z : ℂ) :
    Complex.exp (θ * Complex.I) * z * Complex.exp (-(θ * Complex.I)) = z := by
  rw [mul_right_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

private theorem decomposition_mul_diagonal (g k₁ k₂ : GL (Fin 2) ℂ) (α β : ℝ)
    (h : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal (invFrobSq g) (invAbsDet g) *
        (k₂ : Matrix (Fin 2) (Fin 2) ℂ)) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (k₁ : Matrix (Fin 2) (Fin 2) ℂ) *
            Matrix.diagonal ![Complex.exp (α * Complex.I), Complex.exp (β * Complex.I)] *
          singularDiagonal (invFrobSq g) (invAbsDet g) *
        (Matrix.diagonal ![Complex.exp (-(α * Complex.I)), Complex.exp (-(β * Complex.I))] *
          (k₂ : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have ht : Matrix.diagonal ![Complex.exp (α * Complex.I), Complex.exp (β * Complex.I)] *
        singularDiagonal (invFrobSq g) (invAbsDet g) *
      Matrix.diagonal ![Complex.exp (-(α * Complex.I)), Complex.exp (-(β * Complex.I))] =
      singularDiagonal (invFrobSq g) (invAbsDet g) := by
    unfold singularDiagonal
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact exp_mul_mul_exp_neg α _
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact exp_mul_mul_exp_neg β _
  calc (g : Matrix (Fin 2) (Fin 2) ℂ)
        = (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal (invFrobSq g) (invAbsDet g) *
            (k₂ : Matrix (Fin 2) (Fin 2) ℂ) := h
    _ = (k₁ : Matrix (Fin 2) (Fin 2) ℂ) *
          (Matrix.diagonal ![Complex.exp (α * Complex.I), Complex.exp (β * Complex.I)] *
              singularDiagonal (invFrobSq g) (invAbsDet g) *
            Matrix.diagonal ![Complex.exp (-(α * Complex.I)), Complex.exp (-(β * Complex.I))]) *
          (k₂ : Matrix (Fin 2) (Fin 2) ℂ) := by rw [ht]
    _ = _ := by simp only [Matrix.mul_assoc]

private theorem star_exp_ofReal_mul_I (θ : ℝ) :
    star (Complex.exp (θ * Complex.I)) = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
  rw [show star (Complex.exp (θ * Complex.I)) = (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) from rfl,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

private theorem exists_diagonal_of_decomposition_eq (g : GL (Fin 2) ℂ) (hg : g ∈ distinctSingularValues)
    (k₁ k₂ k₁' k₂' : GL (Fin 2) ℂ)
    (hk₁ : star (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (hk₂ : star (k₂ : Matrix (Fin 2) (Fin 2) ℂ) * (k₂ : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (hk₁' : star (k₁' : Matrix (Fin 2) (Fin 2) ℂ) * (k₁' : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (hk₂' : star (k₂' : Matrix (Fin 2) (Fin 2) ℂ) * (k₂' : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (h : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal (invFrobSq g) (invAbsDet g) *
        (k₂ : Matrix (Fin 2) (Fin 2) ℂ))
    (h' : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (k₁' : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal (invFrobSq g) (invAbsDet g) *
        (k₂' : Matrix (Fin 2) (Fin 2) ℂ)) :
    ∃ α β : ℝ,
      (k₁' : Matrix (Fin 2) (Fin 2) ℂ) =
        (k₁ : Matrix (Fin 2) (Fin 2) ℂ) *
          Matrix.diagonal ![Complex.exp (α * Complex.I), Complex.exp (β * Complex.I)] ∧
      (k₂' : Matrix (Fin 2) (Fin 2) ℂ) =
        Matrix.diagonal ![Complex.exp (-(α * Complex.I)), Complex.exp (-(β * Complex.I))] *
          (k₂ : Matrix (Fin 2) (Fin 2) ℂ) := by
  classical
  set T : ℝ := invFrobSq g with hT
  set d : ℝ := invAbsDet g with hd
  have hd0 : 0 < d := invAbsDet_pos g
  have hTd : 2 * d < T := hg
  set a : ℝ := upperSingularValue T d with ha
  set b : ℝ := lowerSingularValue T d with hb
  have hb0 : 0 < b := lowerSingularValue_pos T d hd0 hTd.le
  have hab : b < a := lowerSingularValue_lt_upperSingularValue T d hd0.le hTd
  have ha0 : 0 < a := hb0.trans hab
  have haC : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb0.ne'
  have hab2 : ((a : ℝ) : ℂ) ^ 2 ≠ ((b : ℝ) : ℂ) ^ 2 := by
    intro e
    have e' : a ^ 2 = b ^ 2 := by exact_mod_cast e
    nlinarith
  set S : Matrix (Fin 2) (Fin 2) ℂ := singularDiagonal T d with hSdef
  have hS : S = Matrix.diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)] := rfl
  set K₁ : Matrix (Fin 2) (Fin 2) ℂ := (k₁ : Matrix (Fin 2) (Fin 2) ℂ)
  set K₂ : Matrix (Fin 2) (Fin 2) ℂ := (k₂ : Matrix (Fin 2) (Fin 2) ℂ)
  set K₁' : Matrix (Fin 2) (Fin 2) ℂ := (k₁' : Matrix (Fin 2) (Fin 2) ℂ)
  set K₂' : Matrix (Fin 2) (Fin 2) ℂ := (k₂' : Matrix (Fin 2) (Fin 2) ℂ)
  have hK1' : K₁' * star K₁' = 1 := mul_eq_one_comm.mp hk₁'
  have hK2 : K₂ * star K₂ = 1 := mul_eq_one_comm.mp hk₂
  set u : Matrix (Fin 2) (Fin 2) ℂ := star K₁' * K₁ with hu
  set v : Matrix (Fin 2) (Fin 2) ℂ := K₂' * star K₂ with hv
  have e0 : K₁ * S * K₂ = K₁' * S * K₂' := h.symm.trans h'
  have e1 : u * S = star K₁' * (K₁ * S * K₂) * star K₂ := by
    simp only [hu, Matrix.mul_assoc, hK2, Matrix.mul_one]
  have e2 : S * v = star K₁' * (K₁' * S * K₂') * star K₂ := by
    simp only [hv, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star K₁') K₁', hk₁', Matrix.one_mul]
  have huv : u * S = S * v := by rw [e1, e0, ← e2]
  have hu1 : star u * u = 1 := by
    simp only [hu, StarMul.star_mul, star_star]
    calc star K₁ * K₁' * (star K₁' * K₁)
          = star K₁ * (K₁' * star K₁') * K₁ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hK1', Matrix.mul_one, hk₁]
  have hu2 : u * star u = 1 := mul_eq_one_comm.mp hu1
  have hv1 : star v * v = 1 := by
    simp only [hv, StarMul.star_mul, star_star]
    calc K₂ * star K₂' * (K₂' * star K₂)
          = K₂ * (star K₂' * K₂') * star K₂ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hk₂', Matrix.mul_one, hK2]
  have hv2 : v * star v = 1 := mul_eq_one_comm.mp hv1
  have hSstar : star S = S := by
    rw [hS, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    fin_cases i <;> simp
  have hSS : S * S = Matrix.diagonal ![((a : ℝ) : ℂ) ^ 2, ((b : ℝ) : ℂ) ^ 2] := by
    rw [hS, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [sq]
  have hcu : u * (S * S) = S * S * u := by
    have e3 : u * S * star (u * S) = S * S := by
      rw [huv, StarMul.star_mul, hSstar]
      calc S * v * (star v * S) = S * (v * star v) * S := by simp only [Matrix.mul_assoc]
        _ = S * S := by rw [hv2, Matrix.mul_one]
    rw [StarMul.star_mul, hSstar] at e3
    calc u * (S * S) = u * S * (S * star u) * u := by simp only [Matrix.mul_assoc, hu1, Matrix.mul_one]
      _ = S * S * u := by rw [e3]
  have hcv : S * S * v = v * (S * S) := by
    have e4 : star (S * v) * (S * v) = S * S := by
      rw [← huv, StarMul.star_mul, hSstar]
      calc S * star u * (u * S) = S * (star u * u) * S := by simp only [Matrix.mul_assoc]
        _ = S * S := by rw [hu1, Matrix.mul_one]
    rw [StarMul.star_mul, hSstar] at e4
    calc S * S * v = v * (star v * S * (S * v)) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc v (star v), hv2, Matrix.one_mul]
      _ = v * (S * S) := by rw [e4]
  have hu01 : u 0 1 = 0 := by
    have e := congrFun (congrFun hcu 0) 1
    rw [hSS, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at e
    have e' : (((b : ℝ) : ℂ) ^ 2 - ((a : ℝ) : ℂ) ^ 2) * u 0 1 = 0 := by linear_combination e
    exact (mul_eq_zero.mp e').resolve_left (sub_ne_zero.mpr (Ne.symm hab2))
  have hu10 : u 1 0 = 0 := by
    have e := congrFun (congrFun hcu 1) 0
    rw [hSS, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at e
    have e' : (((a : ℝ) : ℂ) ^ 2 - ((b : ℝ) : ℂ) ^ 2) * u 1 0 = 0 := by linear_combination e
    exact (mul_eq_zero.mp e').resolve_left (sub_ne_zero.mpr hab2)
  have hv01 : v 0 1 = 0 := by
    have e := congrFun (congrFun hcv 0) 1
    rw [hSS, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at e
    have e' : (((a : ℝ) : ℂ) ^ 2 - ((b : ℝ) : ℂ) ^ 2) * v 0 1 = 0 := by linear_combination e
    exact (mul_eq_zero.mp e').resolve_left (sub_ne_zero.mpr hab2)
  have hv10 : v 1 0 = 0 := by
    have e := congrFun (congrFun hcv 1) 0
    rw [hSS, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at e
    have e' : (((b : ℝ) : ℂ) ^ 2 - ((a : ℝ) : ℂ) ^ 2) * v 1 0 = 0 := by linear_combination e
    exact (mul_eq_zero.mp e').resolve_left (sub_ne_zero.mpr (Ne.symm hab2))
  have h00 : u 0 0 = v 0 0 := by
    have e := congrFun (congrFun huv 0) 0
    rw [hS, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    simp only [Fin.isValue, Matrix.cons_val_zero] at e
    exact mul_right_cancel₀ haC (e.trans (mul_comm _ _))
  have h11 : u 1 1 = v 1 1 := by
    have e := congrFun (congrFun huv 1) 1
    rw [hS, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at e
    exact mul_right_cancel₀ hbC (e.trans (mul_comm _ _))
  have hn0 : ‖u 0 0‖ = 1 := by
    have e := congrFun (congrFun hu1 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e
    simp only [Matrix.star_apply, hu10, star_zero, mul_zero, add_zero] at e
    have e' : ((Complex.normSq (u 0 0) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact e
    have e'' : Complex.normSq (u 0 0) = 1 := by exact_mod_cast e'
    rw [Complex.normSq_eq_norm_sq] at e''
    nlinarith [norm_nonneg (u 0 0)]
  have hn1 : ‖u 1 1‖ = 1 := by
    have e := congrFun (congrFun hu1 1) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e
    simp only [Matrix.star_apply, hu01, star_zero, mul_zero, zero_add] at e
    have e' : ((Complex.normSq (u 1 1) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact e
    have e'' : Complex.normSq (u 1 1) = 1 := by exact_mod_cast e'
    rw [Complex.normSq_eq_norm_sq] at e''
    nlinarith [norm_nonneg (u 1 1)]
  obtain ⟨α', hα'⟩ := (Complex.norm_eq_one_iff _).mp hn0
  obtain ⟨β', hβ'⟩ := (Complex.norm_eq_one_iff _).mp hn1
  have hudiag : u = Matrix.diagonal ![u 0 0, u 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hu01, hu10]
  have hvdiag : v = Matrix.diagonal ![u 0 0, u 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hv01, hv10, h00, h11]
  refine ⟨-α', -β', ?_, ?_⟩
  · have e5 : K₁' * u = K₁ := by rw [hu, ← Matrix.mul_assoc, hK1', Matrix.one_mul]
    have e6 : K₁' = K₁ * star u := by rw [← e5, Matrix.mul_assoc, hu2, Matrix.mul_one]
    rw [e6, hudiag, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, ← hα', ← hβ']
    congr 2
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.star_apply, Matrix.cons_val_zero]
      exact star_exp_ofReal_mul_I α'
    · simp only [Fin.mk_one, Fin.isValue, Pi.star_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact star_exp_ofReal_mul_I β'
  · have e7 : v * K₂ = K₂' := by rw [hv, Matrix.mul_assoc, hk₂, Matrix.mul_one]
    rw [← e7, hvdiag, ← hα', ← hβ']
    congr 2
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      congr 1
      push_cast
      ring
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      congr 1
      push_cast
      ring

private theorem twistedConj_eq_twistedConj_inv_mul (g k₁ k₂ k : GL (Fin 2) ℂ) :
    k⁻¹ * g * conjEntries k =
      (k₁⁻¹ * k)⁻¹ * ((k₁⁻¹ * g * k₂⁻¹) * (k₂ * conjEntries k₁)) *
        conjEntries (k₁⁻¹ * k) := by
  simp only [conjEntries, map_mul, map_inv]
  group

private theorem star_mul_self_conjEntries (k : GL (Fin 2) ℂ)
    (hk : star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    star ((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  have hc : ((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (k : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) := rfl
  rw [hc, Matrix.star_eq_conjTranspose, ← Matrix.conjTranspose_map (starRingEnd ℂ) (fun _ => rfl),
    ← Matrix.map_mul, ← Matrix.star_eq_conjTranspose, hk, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem det_conjEntries (k : GL (Fin 2) ℂ) :
    Matrix.det ((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (starRingEnd ℂ) (Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hc : ((conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (starRingEnd ℂ).mapMatrix (k : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  rw [hc, ← RingHom.map_det]

private theorem mem_rowIsometrySubgroup₀_of_star_mul_self (k : GL (Fin 2) ℂ)
    (hk : star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (hdet : Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    k ∈ rowIsometrySubgroup₀ ℂ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨hdet, ?_⟩
  unfold WindowedSiegel.IsRowIsometry
  refine ⟨by rw [hdet, norm_one], fun x y => ?_⟩
  set K : Matrix (Fin 2) (Fin 2) ℂ := (k : Matrix (Fin 2) (Fin 2) ℂ) with hK
  have hk' : K * star K = 1 := mul_eq_one_comm.mp hk
  have hc : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun _ => rfl
  have e00 := congrFun (congrFun hk' 0) 0
  have e11 := congrFun (congrFun hk' 1) 1
  have e01 := congrFun (congrFun hk' 0) 1
  have e10 := congrFun (congrFun hk' 1) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00 e11
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at e01
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e10
  simp only [Matrix.star_apply, hc] at e00 e11 e01 e10
  have hnn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, Complex.ofReal_add, hnn, hnn, hnn, hnn, map_add, map_add, map_mul, map_mul, map_mul,
    map_mul]
  linear_combination (x * (starRingEnd ℂ) x) * e00 + (y * (starRingEnd ℂ) y) * e11 +
    (x * (starRingEnd ℂ) y) * e01 + (y * (starRingEnd ℂ) x) * e10

private theorem coe_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    ((twistedSplitElt a₁ a₂ v h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.sqrt a₁ : ℂ), v; 0, (Real.sqrt a₂ : ℂ)] := rfl

private theorem invFrobSq_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    invFrobSq (twistedSplitElt a₁ a₂ v h) = a₁ + a₂ + Complex.normSq v := by
  unfold invFrobSq
  rw [coe_twistedSplitElt]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Complex.star_def, Complex.mul_conj]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.normSq_ofReal, Complex.normSq_zero,
    Real.mul_self_sqrt h.1.le, Real.mul_self_sqrt h.2.le]
  ring

private theorem invAbsDet_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    invAbsDet (twistedSplitElt a₁ a₂ v h) = Real.sqrt a₁ * Real.sqrt a₂ := by
  unfold invAbsDet
  rw [coe_twistedSplitElt, Matrix.det_fin_two_of]
  simp only [mul_zero, sub_zero]
  rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

private theorem twistedSplitElt_mem_distinctSingularValues (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) (hv : v ≠ 0) :
    twistedSplitElt a₁ a₂ v h ∈ distinctSingularValues := by
  show 2 * invAbsDet (twistedSplitElt a₁ a₂ v h) < invFrobSq (twistedSplitElt a₁ a₂ v h)
  rw [invFrobSq_twistedSplitElt, invAbsDet_twistedSplitElt]
  have hv' : 0 < Complex.normSq v := Complex.normSq_pos.mpr hv
  have h1 := Real.mul_self_sqrt h.1.le
  have h2 := Real.mul_self_sqrt h.2.le
  nlinarith [sq_nonneg (Real.sqrt a₁ - Real.sqrt a₂)]

private theorem coe_twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    ((twistedEllipticElt r θ ρ u hr hρ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.sqrt r : ℂ) * (-(u * ρ * Complex.exp (-(θ / 2 * Complex.I)))),
          (Real.sqrt r : ℂ) * ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) -
            (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I)));
        (Real.sqrt r : ℂ) * (ρ * Complex.exp (-(θ / 2 * Complex.I))),
          (Real.sqrt r : ℂ) * ((starRingEnd ℂ) u * ρ * Complex.exp (-(θ / 2 * Complex.I)))] := rfl

private theorem invAbsDet_twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    invAbsDet (twistedEllipticElt r θ ρ u hr hρ) = r := by
  unfold invAbsDet
  rw [coe_twistedEllipticElt, Matrix.det_fin_two_of]
  have hE : Complex.exp (θ / 2 * Complex.I) * Complex.exp (-(θ / 2 * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hρi : (ρ : ℂ)⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ'
  have hu : (starRingEnd ℂ) u * u = (Complex.normSq u : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj u
  have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by exact_mod_cast Real.sq_sqrt hr.le
  have key : (Real.sqrt r : ℂ) * (-(u * ρ * Complex.exp (-(θ / 2 * Complex.I)))) *
        ((Real.sqrt r : ℂ) * ((starRingEnd ℂ) u * ρ * Complex.exp (-(θ / 2 * Complex.I)))) -
      (Real.sqrt r : ℂ) * ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) -
        (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I))) *
        ((Real.sqrt r : ℂ) * (ρ * Complex.exp (-(θ / 2 * Complex.I)))) = -(r : ℂ) := by
    linear_combination
      (-(ρ : ℂ) ^ 2 * Complex.exp (-(θ / 2 * Complex.I)) ^ 2 * (Real.sqrt r : ℂ) ^ 2) * hu -
        (Real.sqrt r : ℂ) ^ 2 * hρi - (Real.sqrt r : ℂ) ^ 2 * ((ρ : ℂ)⁻¹ * ρ) * hE - hs
  rw [key, norm_neg, Complex.norm_real, Real.norm_of_nonneg hr.le]

private theorem normSq_exp_half (θ : ℝ) : Complex.normSq (Complex.exp (θ / 2 * Complex.I)) = 1 := by
  have : (θ / 2 : ℂ) * Complex.I = ((θ / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]

private theorem normSq_exp_neg_half (θ : ℝ) : Complex.normSq (Complex.exp (-(θ / 2 * Complex.I))) = 1 := by
  have : -((θ / 2 : ℂ) * Complex.I) = ((-(θ / 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]

private theorem re_cross_term (θ ρ : ℝ) (q : ℝ) (hρ : 0 < ρ) :
    ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) *
        (starRingEnd ℂ) ((q : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I)))).re = q * Real.cos θ := by
  have hconj : (starRingEnd ℂ) (Complex.exp (-(θ / 2 * Complex.I))) = Complex.exp (θ / 2 * Complex.I) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, map_ofNat]
  have hEE : Complex.exp (θ / 2 * Complex.I) * Complex.exp (θ / 2 * Complex.I) = Complex.exp (θ * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  rw [map_mul, map_mul, hconj, Complex.conj_ofReal, Complex.conj_ofReal]
  have : (ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) * ((q : ℂ) * ρ * Complex.exp (θ / 2 * Complex.I)) =
      (q : ℂ) * Complex.exp (θ * Complex.I) := by
    rw [← hEE]; field_simp
  simp only [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

private theorem invFrobSq_twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    invFrobSq (twistedEllipticElt r θ ρ u hr hρ) =
      r * (ρ ^ 2 + ρ⁻¹ ^ 2 + Complex.normSq u ^ 2 * ρ ^ 2 + 2 * Complex.normSq u * ρ ^ 2
        - 2 * Complex.normSq u * Real.cos θ) := by
  unfold invFrobSq
  rw [coe_twistedEllipticElt]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Complex.star_def, Complex.mul_conj]
  simp only [Complex.add_re, Complex.ofReal_re]
  have hcross : Complex.normSq ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) -
      (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I))) =
        ρ⁻¹ ^ 2 + Complex.normSq u ^ 2 * ρ ^ 2 - 2 * (Complex.normSq u * Real.cos θ) := by
    rw [Complex.normSq_sub, re_cross_term θ ρ (Complex.normSq u) hρ, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_mul, Complex.normSq_inv, normSq_exp_half, normSq_exp_neg_half, Complex.normSq_ofReal,
      Complex.normSq_ofReal]
    ring
  simp only [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_conj, Complex.normSq_ofReal, normSq_exp_neg_half,
    hcross, Real.mul_self_sqrt hr.le]
  ring

private theorem twistedEllipticElt_mem_distinctSingularValues (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ)
    (hg : 0 < ρ ^ 2 * Complex.normSq u ^ 2 + (2 * ρ ^ 2 - 2 * Real.cos θ) * Complex.normSq u
      + (ρ ^ 2 + ρ⁻¹ ^ 2 - 2)) :
    twistedEllipticElt r θ ρ u hr hρ ∈ distinctSingularValues := by
  show 2 * invAbsDet (twistedEllipticElt r θ ρ u hr hρ) < invFrobSq (twistedEllipticElt r θ ρ u hr hρ)
  rw [invAbsDet_twistedEllipticElt, invFrobSq_twistedEllipticElt]
  nlinarith [mul_pos hr hg]

private theorem ae_gap_ne_zero (θ ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᵐ u : ℂ, ρ ^ 2 * Complex.normSq u ^ 2 + (2 * ρ ^ 2 - 2 * Real.cos θ) * Complex.normSq u
      + (ρ ^ 2 + ρ⁻¹ ^ 2 - 2) ≠ 0 := by
  set p : Polynomial ℝ := Polynomial.C (ρ ^ 2) * Polynomial.X ^ 2 +
    Polynomial.C (2 * ρ ^ 2 - 2 * Real.cos θ) * Polynomial.X + Polynomial.C (ρ ^ 2 + ρ⁻¹ ^ 2 - 2) with hp
  have hp0 : p ≠ 0 := by
    intro h0
    have h2 := congrArg (fun q : Polynomial ℝ => q.coeff 2) h0
    simp only [hp, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
      Polynomial.coeff_zero] at h2
    norm_num at h2
    exact absurd h2 (by positivity)
  have hroots : {x : ℝ | p.IsRoot x}.Finite := Polynomial.finite_setOf_isRoot hp0
  have hnull : (volume : MeasureTheory.Measure ℂ)
      (⋃ x ∈ {x : ℝ | p.IsRoot x}, {u : ℂ | Complex.normSq u = x}) = 0 := by
    rw [MeasureTheory.measure_biUnion_null_iff hroots.countable]
    intro x _
    apply MeasureTheory.measure_mono_null (t := Metric.sphere (0 : ℂ) (Real.sqrt x))
    · intro u hu
      simp only [Set.mem_setOf_eq] at hu
      rw [Metric.mem_sphere, dist_zero_right, ← hu, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg u)]
    · exact MeasureTheory.Measure.addHaar_sphere volume (0 : ℂ) (Real.sqrt x)
  rw [MeasureTheory.ae_iff]
  apply MeasureTheory.measure_mono_null _ hnull
  intro u hu
  simp only [Set.mem_setOf_eq, not_not] at hu
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  refine ⟨Complex.normSq u, ?_, rfl⟩
  simp only [Polynomial.IsRoot.def, hp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  exact hu

private theorem two_sheets_congr_aux
    (F G : GL (Fin 2) ℂ → ℂ) (hFG : Set.EqOn F G distinctSingularValues) (r θ ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ)
    (c : ℂ) :
    ∫ u : ℂ, c * (F (twistedEllipticElt r θ ρ u hr hρ) + F (twistedEllipticElt r (-θ) ρ u hr hρ)) =
      ∫ u : ℂ, c * (G (twistedEllipticElt r θ ρ u hr hρ) + G (twistedEllipticElt r (-θ) ρ u hr hρ)) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_gap_ne_zero θ ρ hρ] with u hu
  have hinv : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ.ne'
  have hq := Complex.normSq_nonneg u
  have hc := Real.cos_le_one θ
  have h0 : 0 ≤ ρ ^ 2 * Complex.normSq u ^ 2 + (2 * ρ ^ 2 - 2 * Real.cos θ) * Complex.normSq u
      + (ρ ^ 2 + ρ⁻¹ ^ 2 - 2) := by
    nlinarith [sq_nonneg (ρ * (Complex.normSq u + 1) - ρ⁻¹), mul_nonneg hq (sub_nonneg.mpr hc)]
  have hg := lt_of_le_of_ne h0 (Ne.symm hu)
  have hneg : 0 < ρ ^ 2 * Complex.normSq u ^ 2 + (2 * ρ ^ 2 - 2 * Real.cos (-θ)) * Complex.normSq u
      + (ρ ^ 2 + ρ⁻¹ ^ 2 - 2) := by rwa [Real.cos_neg]
  rw [hFG (twistedEllipticElt_mem_distinctSingularValues r θ ρ u hr hρ hg),
    hFG (twistedEllipticElt_mem_distinctSingularValues r (-θ) ρ u hr hρ hneg)]

private theorem fibreArcIntegral_nonneg (i l : ℕ) {Ψ : ℝ} (h0 : 0 ≤ Ψ) : 0 ≤ fibreArcIntegral i l Ψ := by
  unfold fibreArcIntegral
  apply intervalIntegral.integral_nonneg (by linarith)
  intro ψ _
  rw [pow_mul, pow_mul]
  positivity

private theorem unitaryAverage_twistedConj_of_invariant (f : GL (Fin 2) ℂ → ℂ)
    (hf : ∀ k g : GL (Fin 2) ℂ,
      star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 → f (k⁻¹ * g * conjEntries k) = f g)
    (hU : ∀ ψ η ξ₁ ξ₂ : ℝ, star ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (g : GL (Fin 2) ℂ) :
    unitaryAverage (fun k => f (k⁻¹ * g * conjEntries k)) = f g := by
  have hconst : unitaryAverage (fun k => f (k⁻¹ * g * conjEntries k)) = unitaryAverage (fun _ => f g) := by
    unfold unitaryAverage
    simp only [hf _ _ (hU _ _ _ _)]
  rw [hconst]
  exact ChartInvariance.unitaryAverage_const (f g)

private theorem fibreArcIntegral_le_self (i l : ℕ) {Ψ : ℝ} (h0 : 0 ≤ Ψ) : fibreArcIntegral i l Ψ ≤ Ψ := by
  unfold fibreArcIntegral
  have hbound : ∀ ψ ∈ Set.uIoc (-(Ψ / 2)) (Ψ / 2), ‖Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l)‖ ≤ 1 := by
    intro ψ _
    have hc : Real.cos ψ ^ (2 * i) ≤ 1 := by
      rw [pow_mul]; exact pow_le_one₀ (sq_nonneg _) (Real.cos_sq_le_one ψ)
    have hs : Real.sin ψ ^ (2 * l) ≤ 1 := by
      rw [pow_mul]; exact pow_le_one₀ (sq_nonneg _) (Real.sin_sq_le_one ψ)
    have hc0 : 0 ≤ Real.cos ψ ^ (2 * i) := by rw [pow_mul]; positivity
    have hs0 : 0 ≤ Real.sin ψ ^ (2 * l) := by rw [pow_mul]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc0 hs0)]
    exact mul_le_one₀ hc hs0 hs
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(Ψ / 2)) (b := Ψ / 2) (C := 1) hbound
  have habs : |Ψ / 2 - -(Ψ / 2)| = Ψ := by rw [abs_of_nonneg (by linarith)]; ring
  rw [habs, one_mul, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

private theorem fibreMonomialFactor_split_le_one (i l : ℕ) {T a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hT : a₁ + a₂ < T) :
    0 ≤ fibreMonomialFactor i l T (Real.sqrt (a₁ * a₂)) (a₁ + a₂) ∧
      fibreMonomialFactor i l T (Real.sqrt (a₁ * a₂)) (a₁ + a₂) ≤ 1 := by
  unfold fibreMonomialFactor
  have hd0 : 0 ≤ Real.sqrt (a₁ * a₂) := Real.sqrt_nonneg _
  have hamgm : 2 * Real.sqrt (a₁ * a₂) ≤ a₁ + a₂ := by
    rw [Real.sqrt_mul ha₁.le]
    nlinarith [sq_nonneg (Real.sqrt a₁ - Real.sqrt a₂), Real.mul_self_sqrt ha₁.le, Real.mul_self_sqrt ha₂.le]
  have hx : 0 < T - (a₁ + a₂) := by linarith
  have hminus : T - (a₁ + a₂) ≤ T - 2 * Real.sqrt (a₁ * a₂) := by linarith
  have hplus : T - (a₁ + a₂) ≤ T + 2 * Real.sqrt (a₁ * a₂) := by linarith
  have hm0 : 0 < T - 2 * Real.sqrt (a₁ * a₂) := lt_of_lt_of_le hx hminus
  have hp0 : 0 < T + 2 * Real.sqrt (a₁ * a₂) := lt_of_lt_of_le hx hplus
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity), pow_add]
  exact mul_le_mul (pow_le_pow_left₀ hx.le hplus i) (pow_le_pow_left₀ hx.le hminus l) (by positivity) (by positivity)

private theorem norm_splitFibreTerm_le (i l : ℕ) {T a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hT : a₁ + a₂ < T) :
    ‖splitFibreTerm i l T a₁ a₂‖ ≤ Real.pi := by
  unfold splitFibreTerm
  obtain ⟨hPnonneg, hPle_one⟩ := fibreMonomialFactor_split_le_one i l ha₁ ha₂ hT
  have harc_nonneg : 0 ≤ fibreArcIntegral i l (2 * Real.pi) := fibreArcIntegral_nonneg i l (by positivity)
  have harc_le : fibreArcIntegral i l (2 * Real.pi) ≤ 2 * Real.pi := fibreArcIntegral_le_self i l (by positivity)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc 1 / 2 * fibreMonomialFactor i l T (Real.sqrt (a₁ * a₂)) (a₁ + a₂) * fibreArcIntegral i l (2 * Real.pi)
      ≤ 1 / 2 * 1 * (2 * Real.pi) := by gcongr
    _ = Real.pi := by ring

private def levelProfile (C : ℝ → ℝ → ℂ) (d₀ : ℝ) (T : ℝ) : ℂ :=
  ((max 0 (min 1 (T - 2 * d₀ + 1)) : ℝ) : ℂ) * C (max T (2 * d₀)) d₀

private theorem levelProfile_of_le (C : ℝ → ℝ → ℂ) {d₀ T : ℝ} (hT : 2 * d₀ ≤ T) : levelProfile C d₀ T = C T d₀ := by
  unfold levelProfile
  rw [max_eq_left hT, min_eq_left (by linarith), max_eq_right zero_le_one]
  simp

private theorem continuous_levelProfile (C : ℝ → ℝ → ℂ) {d₀ : ℝ} (hd : 0 < d₀)
    (hC : ContinuousOn (fun q : ℝ × ℝ => C q.1 q.2) normDetCone) : Continuous (levelProfile C d₀) := by
  unfold levelProfile
  have hclamp : Continuous fun T : ℝ => ((max 0 (min 1 (T - 2 * d₀ + 1)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).add continuous_const)))
  have hmap : Continuous fun T : ℝ => ((max T (2 * d₀), d₀) : ℝ × ℝ) :=
    (continuous_id.max continuous_const).prodMk continuous_const
  have hright : Continuous fun T : ℝ => C (max T (2 * d₀)) d₀ :=
    hC.comp_continuous hmap (fun T => ⟨le_max_right _ _, hd⟩)
  exact hclamp.mul hright

private theorem hasCompactSupport_levelProfile (C : ℝ → ℝ → ℂ) (d₀ : ℝ) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hCK : ∀ q : ℝ × ℝ, q ∉ K → C q.1 q.2 = 0) : HasCompactSupport (levelProfile C d₀) := by
  obtain ⟨M, hM⟩ : BddAbove (Prod.fst '' K) := hK.bddAbove_image continuous_fst.continuousOn
  apply HasCompactSupport.intro (isCompact_Icc (a := 2 * d₀ - 1) (b := max M (2 * d₀)))
  intro T hT
  unfold levelProfile
  rw [Set.mem_Icc, not_and_or] at hT
  rcases hT with hlow | hhigh
  · have h0 : max 0 (min 1 (T - 2 * d₀ + 1)) = 0 := by
      apply max_eq_left
      exact (min_le_right _ _).trans (by linarith [not_le.mp hlow])
    rw [h0]; simp
  · have hhigh := not_le.mp hhigh
    have hTd : max T (2 * d₀) = T := max_eq_left (le_of_lt (lt_of_le_of_lt (le_max_right M (2 * d₀)) hhigh))
    have hnot : ((T, d₀) : ℝ × ℝ) ∉ K := by
      intro hmem
      have : T ≤ M := hM ⟨(T, d₀), hmem, rfl⟩
      have : M < T := lt_of_le_of_lt (le_max_left M (2 * d₀)) hhigh
      linarith
    rw [hTd, hCK (T, d₀) hnot, mul_zero]

private theorem fibreArcIntegral_le (i l : ℕ) {Ψ : ℝ} (h0 : 0 ≤ Ψ) (hπ : Ψ ≤ Real.pi) :
    fibreArcIntegral i l Ψ ≤ Ψ * (Real.sin (Ψ / 2) ^ 2) ^ l := by
  have hbound : ∀ ψ ∈ Set.uIoc (-(Ψ / 2)) (Ψ / 2),
      ‖Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l)‖ ≤ (Real.sin (Ψ / 2) ^ 2) ^ l := by
    intro ψ hψ
    rw [Set.uIoc_of_le (by linarith)] at hψ
    have hψ1 : -(Ψ / 2) ≤ ψ := hψ.1.le
    have hψ2 : ψ ≤ Ψ / 2 := hψ.2
    have hcos : Real.cos ψ ^ (2 * i) ≤ 1 := by
      rw [pow_mul]; exact pow_le_one₀ (sq_nonneg _) (Real.cos_sq_le_one ψ)
    have hsin_upper : Real.sin ψ ≤ Real.sin (Ψ / 2) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hψ2
    have hsin_lower : -Real.sin (Ψ / 2) ≤ Real.sin ψ := by
      rw [← Real.sin_neg]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hψ1
    have habs : |Real.sin ψ| ≤ Real.sin (Ψ / 2) := abs_le.mpr ⟨hsin_lower, hsin_upper⟩
    have hsq : Real.sin ψ ^ 2 ≤ Real.sin (Ψ / 2) ^ 2 := by
      rw [← sq_abs (Real.sin ψ)]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hsin : Real.sin ψ ^ (2 * l) ≤ (Real.sin (Ψ / 2) ^ 2) ^ l := by
      rw [pow_mul]; exact pow_le_pow_left₀ (sq_nonneg _) hsq l
    have hnn : 0 ≤ Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l) := by
      rw [pow_mul, pow_mul]; positivity
    rw [Real.norm_of_nonneg hnn]
    calc Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l) ≤ 1 * Real.sin ψ ^ (2 * l) :=
          mul_le_mul_of_nonneg_right hcos (by rw [pow_mul]; positivity)
      _ = Real.sin ψ ^ (2 * l) := one_mul _
      _ ≤ (Real.sin (Ψ / 2) ^ 2) ^ l := hsin
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hlen : |Ψ / 2 - -(Ψ / 2)| = Ψ := by
    rw [sub_neg_eq_add, add_halves, abs_of_nonneg h0]
  rw [hlen] at h
  calc fibreArcIntegral i l Ψ ≤ ‖fibreArcIntegral i l Ψ‖ := Real.le_norm_self _
    _ = ‖∫ ψ in (-(Ψ / 2))..(Ψ / 2), Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l)‖ := rfl
    _ ≤ (Real.sin (Ψ / 2) ^ 2) ^ l * Ψ := h
    _ = Ψ * (Real.sin (Ψ / 2) ^ 2) ^ l := mul_comm _ _

private theorem norm_unitaryAverage_le (F : GL (Fin 2) ℂ → ℂ) (M : ℝ) (_hM : 0 ≤ M)
    (hF : ∀ ψ η ξ₁ ξ₂ : ℝ, ‖F (unitaryElt ψ η ξ₁ ξ₂)‖ ≤ M) : ‖unitaryAverage F‖ ≤ Real.pi * M := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hin : ∀ ψ η ξ₁ : ℝ,
      ‖∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)‖ ≤
        M * |2 * Real.pi - 0| := by
    intro ψ η ξ₁
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro ξ₂ _
    rw [norm_mul]
    have hsc : ‖(Real.sin η * Real.cos η : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact mul_le_one₀ (Real.abs_sin_le_one η) (abs_nonneg _) (Real.abs_cos_le_one η)
    calc ‖(Real.sin η * Real.cos η : ℂ)‖ * ‖F (unitaryElt ψ η ξ₁ ξ₂)‖ ≤ 1 * M :=
          mul_le_mul hsc (hF ψ η ξ₁ ξ₂) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  have h1 : ∀ ψ η : ℝ,
      ‖∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)‖ ≤
        M * |2 * Real.pi - 0| * |2 * Real.pi - 0| := by
    intro ψ η
    exact intervalIntegral.norm_integral_le_of_norm_le_const (fun ξ₁ _ => hin ψ η ξ₁)
  have h2 : ∀ ψ : ℝ,
      ‖∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)‖ ≤
        M * |2 * Real.pi - 0| * |2 * Real.pi - 0| * |Real.pi / 2 - 0| := by
    intro ψ
    exact intervalIntegral.norm_integral_le_of_norm_le_const (fun η _ => h1 ψ η)
  have h3 : ‖∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)‖ ≤
      M * |2 * Real.pi - 0| * |2 * Real.pi - 0| * |Real.pi / 2 - 0| * |2 * Real.pi - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun ψ _ => h2 ψ)
  have habs : |2 * Real.pi - 0| = 2 * Real.pi := by rw [sub_zero]; exact abs_of_pos (by positivity)
  have habs' : |Real.pi / 2 - 0| = Real.pi / 2 := by rw [sub_zero]; exact abs_of_pos (by positivity)
  rw [habs, habs'] at h3
  unfold unitaryAverage
  rw [norm_mul]
  have hc : ‖(1 / (4 * Real.pi ^ 3) : ℂ)‖ = 1 / (4 * Real.pi ^ 3) := by
    have : ((1 / (4 * Real.pi ^ 3) : ℝ) : ℂ) = (1 / (4 * Real.pi ^ 3) : ℂ) := by push_cast; ring
    rw [← this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  calc 1 / (4 * Real.pi ^ 3) * ‖∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2),
          ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
            (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)‖
        ≤ 1 / (4 * Real.pi ^ 3) * (M * (2 * Real.pi) * (2 * Real.pi) * (Real.pi / 2) * (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = Real.pi * M := by field_simp; ring

private theorem unitaryAverage_eq_zero_of_forall (F : GL (Fin 2) ℂ → ℂ)
    (hF : ∀ ψ η ξ₁ ξ₂ : ℝ, F (unitaryElt ψ η ξ₁ ξ₂) = 0) : unitaryAverage F = 0 := by
  simp [unitaryAverage, hF]

private theorem invFrobSq_eq_sum (g : GL (Fin 2) ℂ) :
    invFrobSq g = ∑ i : Fin 2, ∑ j : Fin 2, Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) i j) := by
  unfold invFrobSq
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Complex.star_def, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

private theorem normSq_entry_le_invFrobSq (g : GL (Fin 2) ℂ) (i j : Fin 2) :
    Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) i j) ≤ invFrobSq g := by
  rw [invFrobSq_eq_sum]
  have hi : Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) i j) ≤
      ∑ j' : Fin 2, Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) i j') :=
    Finset.single_le_sum (fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
  exact hi.trans (Finset.single_le_sum (fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg _)
    (Finset.mem_univ i))

private theorem exists_forall_slice_eq_zero_of_lt_invFrobSq {P : Type} [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦc : HasCompactSupport Φ) :
    ∃ R : ℝ, ∀ (p : P) (g : GL (Fin 2) ℂ), R < invFrobSq g →
      Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p) = 0 := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_closedBall (0 : (Fin 2 → Fin 2 → ℂ) × P)).1
    hΦc.isBounded
  refine ⟨4 * B ^ 2, fun p g hg => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hball := hB hmem
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hball
  have hfst : ‖Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ B := (le_max_left _ _).trans hball
  have hentry : ∀ i j : Fin 2, Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) i j) ≤ B ^ 2 := by
    intro i j
    have h1 : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ B := by
      have h2 := norm_le_pi_norm (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ)) i
      have h3 := norm_le_pi_norm (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ) i) j
      exact (h3.trans h2).trans hfst
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hsum : invFrobSq g ≤ 4 * B ^ 2 := by
    rw [invFrobSq_eq_sum, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    linarith [hentry 0 0, hentry 0 1, hentry 1 0, hentry 1 1]
  exact absurd hg (not_lt.2 hsum)

private theorem continuous_unitaryAverage_of_continuous {X : Type} [TopologicalSpace X] (H : X → GL (Fin 2) ℂ → ℂ)
    (hH : Continuous fun q : X × ℝ × ℝ × ℝ × ℝ => H q.1 (unitaryElt q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)) :
    Continuous fun x => unitaryAverage (H x) := by
  unfold unitaryAverage
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : X) (ψ : ℝ) => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * H x (unitaryElt ψ η ξ₁ ξ₂)) ?_ _ _
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (q : X × ℝ) (η : ℝ) => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * H q.1 (unitaryElt q.2 η ξ₁ ξ₂)) ?_ _ _
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (q : (X × ℝ) × ℝ) (ξ₁ : ℝ) => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin q.2 * Real.cos q.2 : ℂ) * H q.1.1 (unitaryElt q.1.2 q.2 ξ₁ ξ₂)) ?_ _ _
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (q : ((X × ℝ) × ℝ) × ℝ) (ξ₂ : ℝ) =>
      (Real.sin q.1.2 * Real.cos q.1.2 : ℂ) * H q.1.1.1 (unitaryElt q.1.1.2 q.1.2 q.2 ξ₂)) ?_ _ _
  apply Continuous.mul
  · have h : Continuous fun q : (((X × ℝ) × ℝ) × ℝ) × ℝ => q.1.1.2 := by fun_prop
    exact (Complex.continuous_ofReal.comp (Real.continuous_sin.comp h)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_cos.comp h))
  · have hre : Continuous fun q : (((X × ℝ) × ℝ) × ℝ) × ℝ => ((q.1.1.1.1, q.1.1.1.2, q.1.1.2, q.1.2, q.2) :
        X × ℝ × ℝ × ℝ × ℝ) := by fun_prop
    exact hH.comp hre

private theorem sqrt_mul_sqrt_exp_neg (r t : ℝ) (hr : 0 < r) :
    Real.sqrt (r * Real.exp t) * Real.sqrt (r * Real.exp (-t)) = r := by
  rw [← Real.sqrt_mul (by positivity)]
  have h : r * Real.exp t * (r * Real.exp (-t)) = r ^ 2 := by
    rw [show r * Real.exp t * (r * Real.exp (-t)) = r ^ 2 * (Real.exp t * Real.exp (-t)) by ring,
      ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rw [h, Real.sqrt_sq hr.le]

private theorem exp_add_exp_neg_lt_iff_mem_Ioo_arcosh (r T t : ℝ) (hr : 0 < r) (hT : 2 * r ≤ T) :
    r * Real.exp t + r * Real.exp (-t) < T ↔
      t ∈ Set.Ioo (-Real.arcosh (T / (2 * r))) (Real.arcosh (T / (2 * r))) := by
  have hx : (1 : ℝ) ≤ T / (2 * r) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hcosh : r * Real.exp t + r * Real.exp (-t) = 2 * r * Real.cosh t := by rw [Real.cosh_eq]; ring
  have harc := Real.arcosh_nonneg hx
  have h2r : (0 : ℝ) < 2 * r := by positivity
  rw [hcosh, Set.mem_Ioo, ← abs_lt]
  constructor
  · intro h
    have h1 : Real.cosh t < Real.cosh (Real.arcosh (T / (2 * r))) := by
      rw [Real.cosh_arcosh hx, lt_div_iff₀ h2r]; linarith
    have h2 := Real.cosh_lt_cosh.1 h1
    rwa [abs_of_nonneg harc] at h2
  · intro h
    have h1 : Real.cosh t < Real.cosh (Real.arcosh (T / (2 * r))) :=
      Real.cosh_lt_cosh.2 (by rwa [abs_of_nonneg harc])
    rw [Real.cosh_arcosh hx, lt_div_iff₀ h2r] at h1
    linarith

section
open scoped Matrix

private theorem continuous_unitaryElt_coe :
    Continuous fun a : ℝ × ℝ × ℝ × ℝ =>
      ((unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h : (fun a : ℝ × ℝ × ℝ × ℝ =>
      ((unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) = fun a =>
      !![Complex.exp (a.1 * Complex.I) * (Real.cos a.2.1 * Complex.exp (a.2.2.1 * Complex.I)),
          Complex.exp (a.1 * Complex.I) * (Real.sin a.2.1 * Complex.exp (a.2.2.2 * Complex.I));
        Complex.exp (a.1 * Complex.I) * (-(Real.sin a.2.1 * Complex.exp (-(a.2.2.2 * Complex.I)))),
          Complex.exp (a.1 * Complex.I) * (Real.cos a.2.1 * Complex.exp (-(a.2.2.1 * Complex.I)))] := rfl
  rw [h]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one] <;> fun_prop

private theorem continuous_twistedSplitElt_coe (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) :
    Continuous fun v : ℂ => ((twistedSplitElt a₁ a₂ v h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [coe_twistedSplitElt]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one] <;> fun_prop

private theorem continuous_twistedEllipticElt_coe (r θ ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) :
    Continuous fun u : ℂ => ((twistedEllipticElt r θ ρ u hr hρ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [coe_twistedEllipticElt]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one] <;> fun_prop

private theorem continuous_twistedConj_coe {X : Type} [TopologicalSpace X] (A : X → GL (Fin 2) ℂ)
    (hA : Continuous fun x => ((A x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) :
    Continuous fun q : X × ℝ × ℝ × ℝ × ℝ =>
      (((unitaryElt q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)⁻¹ * A q.1 *
          conjEntries (unitaryElt q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) := by
  have hrw : (fun q : X × ℝ × ℝ × ℝ × ℝ =>
      (((unitaryElt q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)⁻¹ * A q.1 *
          conjEntries (unitaryElt q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ)) = fun q =>
      ((unitaryElt q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
        ((A q.1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((unitaryElt q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map
          (starRingEnd ℂ) := by
    funext q
    rw [Units.val_mul, Units.val_mul, ChartInvariance.inv_coe_of_unitary (ChartInvariance.unitaryElt_unitary _ _ _ _),
      ChartInvariance.conjEntries_coe]
  rw [hrw]
  have hU : Continuous fun q : X × ℝ × ℝ × ℝ × ℝ =>
      ((unitaryElt q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_unitaryElt_coe.comp continuous_snd
  exact ((hU.matrix_conjTranspose.matrix_mul (hA.comp continuous_fst)).matrix_mul
    (hU.matrix_map Complex.continuous_conj))

end

private theorem continuous_unitaryAverage_slice {X : Type} [TopologicalSpace X] {P : Type} [TopologicalSpace P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ) (p : P) (A : X → GL (Fin 2) ℂ)
    (hA : Continuous fun x => ((A x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) :
    Continuous fun x => unitaryAverage fun k =>
      Φ (Matrix.of.symm ((k⁻¹ * A x * conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), p) := by
  apply continuous_unitaryAverage_of_continuous
  exact hΦ.comp ((continuous_twistedConj_coe A hA).prodMk continuous_const)

private theorem normSq_le_of_invFrobSq_twistedEllipticElt_le (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ)
    (hθ : Real.cos θ < 1) (R : ℝ) (hR : invFrobSq (twistedEllipticElt r θ ρ u hr hρ) ≤ R) :
    Complex.normSq u ≤ (R / r - 2) / (2 * (1 - Real.cos θ)) := by
  rw [invFrobSq_twistedEllipticElt] at hR
  have hm := Complex.normSq_nonneg u
  have hsq : 0 ≤ (ρ * (Complex.normSq u + 1) - ρ⁻¹) ^ 2 := sq_nonneg _
  have hinv : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ.ne'
  have key : ρ ^ 2 + ρ⁻¹ ^ 2 + Complex.normSq u ^ 2 * ρ ^ 2 + 2 * Complex.normSq u * ρ ^ 2 =
      (ρ * (Complex.normSq u + 1) - ρ⁻¹) ^ 2 + 2 * (Complex.normSq u + 1) := by
    linear_combination (2 * (Complex.normSq u + 1)) * hinv
  rw [key] at hR
  have hkey : 2 + 2 * Complex.normSq u * (1 - Real.cos θ) ≤ R / r := by
    rw [le_div_iff₀ hr]
    nlinarith [mul_nonneg hr.le hsq]
  rw [le_div_iff₀ (by linarith)]
  linarith

private theorem exists_Icc_of_invFrobSq_twistedEllipticElt_le (r θ : ℝ) (hr : 0 < r) (hθ : Real.cos θ < 1) (R : ℝ) :
    ∃ ρ₀ ρ₁ : ℝ, 0 < ρ₀ ∧ ∀ (ρ : ℝ) (u : ℂ) (hρ : 0 < ρ),
      invFrobSq (twistedEllipticElt r θ ρ u hr hρ) ≤ R → ρ ∈ Set.Icc ρ₀ ρ₁ := by
  set m₁ : ℝ := max 0 ((R / r - 2) / (2 * (1 - Real.cos θ))) with hm₁
  set S : ℝ := max 1 ((R + 2 * r * m₁) / r) with hS
  have hone_le_S : 1 ≤ S := le_max_left _ _
  have hSpos : 0 < S := by linarith
  refine ⟨(Real.sqrt S)⁻¹, Real.sqrt S, inv_pos.2 (Real.sqrt_pos.2 hSpos), ?_⟩
  intro ρ u hρ hR
  have hm : Complex.normSq u ≤ m₁ :=
    (normSq_le_of_invFrobSq_twistedEllipticElt_le r θ ρ u hr hρ hθ R hR).trans (le_max_right _ _)
  have hm0 := Complex.normSq_nonneg u
  have hc : Real.cos θ ≤ 1 := hθ.le
  have hc' : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  rw [invFrobSq_twistedEllipticElt] at hR
  have hsum : r * (ρ ^ 2 + ρ⁻¹ ^ 2) ≤ R + 2 * r * m₁ := by
    nlinarith [mul_nonneg hm0 (sq_nonneg ρ), mul_nonneg (mul_nonneg hm0 hm0) (sq_nonneg ρ),
      mul_le_mul_of_nonneg_left hm hr.le, mul_nonneg hm0 (sub_nonneg.2 hc), mul_nonneg hr.le hm0]
  have hboth : ρ ^ 2 + ρ⁻¹ ^ 2 ≤ S := by
    have : ρ ^ 2 + ρ⁻¹ ^ 2 ≤ (R + 2 * r * m₁) / r := by rw [le_div_iff₀ hr]; linarith
    exact this.trans (le_max_right _ _)
  have hρ2 : ρ ^ 2 ≤ S := by nlinarith [sq_nonneg ρ⁻¹]
  have hρi2 : ρ⁻¹ ^ 2 ≤ S := by nlinarith [sq_nonneg ρ]
  constructor
  ·
    have h1 : ρ⁻¹ ≤ Real.sqrt S := Real.le_sqrt_of_sq_le hρi2
    have h2 : 0 < ρ⁻¹ := inv_pos.2 hρ
    calc (Real.sqrt S)⁻¹ ≤ (ρ⁻¹)⁻¹ := inv_anti₀ h2 h1
      _ = ρ := inv_inv ρ
  · exact Real.le_sqrt_of_sq_le hρ2

private theorem integrable_unitaryAverage_slice_split {P : Type} [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (p : P)
    (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) :
    MeasureTheory.Integrable fun v : ℂ => unitaryAverage fun k =>
      Φ (Matrix.of.symm ((k⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries k : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ), p) := by
  obtain ⟨R, hR⟩ := exists_forall_slice_eq_zero_of_lt_invFrobSq Φ hΦc
  have hcont := continuous_unitaryAverage_slice Φ hΦ p (fun v => twistedSplitElt a₁ a₂ v h)
    (continuous_twistedSplitElt_coe a₁ a₂ h)
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) (Real.sqrt (max 0 R))) (isCompact_closedBall _ _) ?_
  intro v hv
  apply unitaryAverage_eq_zero_of_forall
  intro ψ η ξ₁ ξ₂
  apply hR
  rw [ChartInvariance.invFrobSq_conj (ChartInvariance.unitaryElt_unitary ψ η ξ₁ ξ₂), invFrobSq_twistedSplitElt]
  rw [Metric.mem_closedBall, dist_zero_right] at hv
  have hv' : Real.sqrt (max 0 R) < ‖v‖ := lt_of_not_ge hv
  have hsq : max 0 R < Complex.normSq v := by
    rw [Complex.normSq_eq_norm_sq]
    calc max 0 R = Real.sqrt (max 0 R) ^ 2 := (Real.sq_sqrt (le_max_left _ _)).symm
      _ < ‖v‖ ^ 2 := by gcongr
  linarith [le_max_right 0 R, h.1, h.2]

private theorem ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing_of_add_two_le
    (i l k : ℕ) (hk : i + l + 2 ≤ k) (r T : ℝ) (hr : 0 < r) (hT : 2 * r ≤ T) :
    (∫ θ in (0 : ℝ)..Real.pi,
        ellipticFibreTerm i l T r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
      (2 * Real.pi / r : ℂ) *
        ∫ t in (-Real.arcosh (T / (2 * r)))..Real.arcosh (T / (2 * r)),
          (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreTerm i l T (r * Real.exp t) (r * Real.exp (-t)) := by
  exact FibreAlgebra.summation_identity ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing i l k hk r T hr hT

noncomputable section

namespace RightFiniteExpansion

variable {P : Type}

private def IsIsometry (u : GL (Fin 2) ℂ) : Prop :=
  star (u : Matrix (Fin 2) (Fin 2) ℂ) * (u : Matrix (Fin 2) (Fin 2) ℂ) = 1

private def entries (g : GL (Fin 2) ℂ) : Fin 2 × Fin 2 → ℂ :=
  fun ij => (g : Matrix (Fin 2) (Fin 2) ℂ) ij.1 ij.2

private def weightPoint (g : GL (Fin 2) ℂ) : Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2 → ℂ :=
  Sum.elim (entries g⁻¹) (entries g)

private def groupTranslate (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (g : GL (Fin 2) ℂ) : (Fin 2 → Fin 2 → ℂ) × P → ℂ :=
  fun q => Φ (Matrix.of.symm (Matrix.of q.1 * (g : Matrix (Fin 2) (Fin 2) ℂ)), q.2)

private def rightTranslate (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (k : rowIsometrySubgroup₀ ℂ) :
    (Fin 2 → Fin 2 → ℂ) × P → ℂ :=
  fun q => Φ (Matrix.of.symm (Matrix.of q.1 * ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), q.2)

private def translateSpan (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) : Submodule ℂ ((Fin 2 → Fin 2 → ℂ) × P → ℂ) :=
  Submodule.span ℂ (Set.range (rightTranslate Φ))

private def IsScalarInvariant (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ∀ q : (Fin 2 → Fin 2 → ℂ) × P, Φ (fun i j => z * q.1 i j, q.2) = Φ q

private def IsDetOneIsometryGroup : Prop :=
  ∀ u : GL (Fin 2) ℂ, IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 → u ∈ rowIsometrySubgroup₀ ℂ

private def IsPolynomialAlong (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (d : ℕ) (F : (Fin 2 → Fin 2 → ℂ) × P → ℂ) : Prop :=
  F ∈ translateSpan Φ ∧ ∃ Q : (Fin 2 → Fin 2 → ℂ) × P → MvPolynomial (Fin 2 × Fin 2) ℂ,
    (∀ q, (Q q).totalDegree ≤ d) ∧
    (∀ m, (fun q => (Q q).coeff m) ∈ translateSpan Φ) ∧
    ∀ q (u : GL (Fin 2) ℂ), IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      groupTranslate F u q = MvPolynomial.eval (entries u) (Q q)

private theorem IsPolynomialAlong.mono {Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ} {d d' : ℕ} (hdd' : d ≤ d')
    {F : (Fin 2 → Fin 2 → ℂ) × P → ℂ} (hF : IsPolynomialAlong Φ d F) : IsPolynomialAlong Φ d' F :=
  let ⟨hFW, Q, hQd, hQc, hQe⟩ := hF
  ⟨hFW, Q, fun q => (hQd q).trans hdd', hQc, hQe⟩

private def polynomialAlong (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (d : ℕ) : Submodule ℂ ((Fin 2 → Fin 2 → ℂ) × P → ℂ) where
  carrier := {F | IsPolynomialAlong Φ d F}
  zero_mem' := by
    refine ⟨(translateSpan Φ).zero_mem, fun _ => 0, fun _ => by simp, fun m => ?_, fun q u _ _ => ?_⟩
    · convert (translateSpan Φ).zero_mem using 1
      funext q; simp
    · simp [groupTranslate]
  add_mem' := by
    rintro F G ⟨hF, QF, hFd, hFc, hFe⟩ ⟨hG, QG, hGd, hGc, hGe⟩
    refine ⟨(translateSpan Φ).add_mem hF hG, fun q => QF q + QG q, fun q => ?_, fun m => ?_, fun q u hu hdet => ?_⟩
    · exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hFd q) (hGd q))
    · have h__af := (translateSpan Φ).add_mem (hFc m) (hGc m)
      simp [MvPolynomial.coeff_add] at h__af ⊢
      exact h__af
    · rw [MvPolynomial.eval_add, ← hFe q u hu hdet, ← hGe q u hu hdet]
      rfl
  smul_mem' := by
    rintro c F ⟨hF, QF, hFd, hFc, hFe⟩
    refine ⟨(translateSpan Φ).smul_mem c hF, fun q => c • QF q, fun q => ?_, fun m => ?_, fun q u hu hdet => ?_⟩
    · exact (MvPolynomial.totalDegree_smul_le _ _).trans (hFd q)
    · have h__af := (translateSpan Φ).smul_mem c (hFc m)
      simp [MvPolynomial.coeff_smul] at h__af ⊢
      exact h__af
    · rw [MvPolynomial.smul_eval, ← hFe q u hu hdet]
      rfl

private theorem mem_polynomialAlong {Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ} {d : ℕ} {F : (Fin 2 → Fin 2 → ℂ) × P → ℂ} :
    F ∈ polynomialAlong Φ d ↔ IsPolynomialAlong Φ d F := Iff.rfl

private theorem polynomialAlong_le_translateSpan (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (d : ℕ) :
    polynomialAlong Φ d ≤ translateSpan Φ := fun _ hF => hF.1

private def weightedIntegrand (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (w : MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ)
    (q : (Fin 2 → Fin 2 → ℂ) × P) : GL (Fin 2) ℂ → ℂ :=
  fun g => MvPolynomial.eval (weightPoint g) w * groupTranslate Φ g q

private def weightedAverage (avg : (GL (Fin 2) ℂ → ℂ) → ℂ) (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (w : MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ) : (Fin 2 → Fin 2 → ℂ) × P → ℂ :=
  fun q => avg (weightedIntegrand Φ w q)

section device

variable [TopologicalSpace P] (avg : (GL (Fin 2) ℂ → ℂ) → ℂ)

private structure IsAveragingDevice (weights : ℕ → MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ) : Prop where
  map_add : ∀ F G : GL (Fin 2) ℂ → ℂ, Continuous F → Continuous G →
    avg (fun h => F h + G h) = avg F + avg G
  map_smul : ∀ (c : ℂ) (F : GL (Fin 2) ℂ → ℂ), Continuous F → avg (fun h => c * F h) = c * avg F
  left_invariant : ∀ F : GL (Fin 2) ℂ → ℂ, Continuous F → ∀ u : GL (Fin 2) ℂ, IsIsometry u →
    avg (fun h => F (u * h)) = avg F
  congr_of_isometries : ∀ F G : GL (Fin 2) ℂ → ℂ, Continuous F → Continuous G →
    (∀ u : GL (Fin 2) ℂ, IsIsometry u → F u = G u) → avg F = avg G
  approximate : ∀ Ψ : GL (Fin 2) ℂ → ℂ, Continuous Ψ →
    Filter.Tendsto (fun n => avg fun h => MvPolynomial.eval (weightPoint h) (weights n) * Ψ h)
      Filter.atTop (nhds (Ψ 1))

variable {avg}

omit [TopologicalSpace P] in
private theorem exists_finite_interpolation (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) [FiniteDimensional ℂ (translateSpan Φ)] :
    ∃ s : Finset ((Fin 2 → Fin 2 → ℂ) × P), ∃ e : (Fin 2 → Fin 2 → ℂ) × P → (Fin 2 → Fin 2 → ℂ) × P → ℂ,
      (∀ x, e x ∈ translateSpan Φ) ∧ ∀ F ∈ translateSpan Φ, F = ∑ x ∈ s, F x • e x := by
  classical
  let ev : (Fin 2 → Fin 2 → ℂ) × P → Module.Dual ℂ (translateSpan Φ) := fun x =>
    (LinearMap.proj x : ((Fin 2 → Fin 2 → ℂ) × P → ℂ) →ₗ[ℂ] ℂ).comp (translateSpan Φ).subtype
  have hev : ∀ x (w : translateSpan Φ), ev x w = (w : (Fin 2 → Fin 2 → ℂ) × P → ℂ) x := fun _ _ => rfl
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have hco : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      apply Subtype.ext
      funext x
      exact hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev))
    rw [hco, Submodule.dualAnnihilator_bot] at h
    exact h.symm
  let b := Module.finBasis ℂ (translateSpan Φ)
  have hcoord : ∀ j, ∃ c : (Fin 2 → Fin 2 → ℂ) × P →₀ ℂ, (c.sum fun x a => a • ev x) = b.coord j := fun j =>
    (Finsupp.mem_span_range_iff_exists_finsupp).1 (by rw [hspan]; exact Submodule.mem_top)
  choose c hc using hcoord
  refine ⟨Finset.univ.biUnion fun j => (c j).support,
    fun x => ∑ j, c j x • ((b j : translateSpan Φ) : (Fin 2 → Fin 2 → ℂ) × P → ℂ), ?_, ?_⟩
  · intro x
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2
  · intro F hF
    set s : Finset ((Fin 2 → Fin 2 → ℂ) × P) := Finset.univ.biUnion fun j => (c j).support with hs
    have hcj : ∀ j, b.repr ⟨F, hF⟩ j = ∑ x ∈ s, c j x * F x := by
      intro j
      have h₁ := LinearMap.congr_fun (hc j) ⟨F, hF⟩
      rw [Module.Basis.coord_apply] at h₁
      rw [← h₁, LinearMap.finsupp_sum_apply]
      simp only [LinearMap.smul_apply, hev, smul_eq_mul]
      refine Finsupp.sum_of_support_subset (c j) ?_ (fun x a => a * F x) (fun x _ => by simp)
      intro x hx
      exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hx⟩
    have hF' := congrArg (fun w : translateSpan Φ => (w : (Fin 2 → Fin 2 → ℂ) × P → ℂ)) (b.sum_repr ⟨F, hF⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hF'
    conv_lhs => rw [← hF']
    simp only [hcj, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]

omit [TopologicalSpace P] in
private theorem groupTranslate_mem_translateSpan (hK : IsDetOneIsometryGroup) (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦ₀ : IsScalarInvariant Φ) (u : GL (Fin 2) ℂ) (hu : IsIsometry u) :
    groupTranslate Φ u ∈ translateSpan Φ := by
  have hdet : ‖Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
    have h := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq] at h
    have h'' : ‖Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ)‖ ^ 2 = 1 := by exact_mod_cast h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h''
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ)) two_pos
  have hznorm : ‖z‖ = 1 := by
    have : ‖z‖ ^ 2 = 1 := by rw [← norm_pow, hz, hdet]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
  have hz0 : z ≠ 0 := by rintro rfl; simp at hznorm
  let c : (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
    Units.map (Matrix.scalar (Fin 2)).toMonoidHom (Units.mk0 z⁻¹ (inv_ne_zero hz0))
  have hc : (c : Matrix (Fin 2) (Fin 2) ℂ) = z⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp [c, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hzz : (starRingEnd ℂ) z⁻¹ * z⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, Complex.conj_mul', hznorm]; simp
  have hk_iso : IsIsometry (c * u) := by
    simp only [IsIsometry, Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul, star_smul, Matrix.mul_smul,
      smul_smul, Complex.star_def]
    rw [hu, mul_comm, hzz, one_smul]
  have hk_det : Matrix.det ((c * u : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← hz,
      inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hz0)]
  have hmem : c * u ∈ rowIsometrySubgroup₀ ℂ := hK _ hk_iso hk_det
  have hzinv : ‖z⁻¹‖ = 1 := by rw [norm_inv, hznorm, inv_one]
  have heq : groupTranslate Φ u = rightTranslate Φ ⟨c * u, hmem⟩ := by
    funext q
    simp only [groupTranslate, rightTranslate, Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
    exact (hΦ₀ z⁻¹ hzinv _).symm
  rw [heq]
  exact Submodule.subset_span ⟨_, rfl⟩

private theorem IsAveragingDevice.avg_zero {weights : ℕ → MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ}
    (hd : IsAveragingDevice avg weights) : avg (fun _ => (0 : ℂ)) = 0 := by
  have h := hd.map_smul 0 (fun _ => (0 : ℂ)) continuous_const
  simpa using h

private theorem IsAveragingDevice.avg_finset_sum {weights : ℕ → MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ}
    (hd : IsAveragingDevice avg weights) {ι : Type} (s : Finset ι) (F : ι → GL (Fin 2) ℂ → ℂ)
    (hF : ∀ i, Continuous (F i)) : avg (fun g => ∑ i ∈ s, F i g) = ∑ i ∈ s, avg (F i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using hd.avg_zero
  · intro a t hat ih
    rw [Finset.sum_insert hat, ← ih]
    have h := hd.map_add (F a) (fun g => ∑ i ∈ t, F i g) (hF a) (continuous_finsetSum t fun i _ => hF i)
    simp only [Finset.sum_insert hat]
    exact h

private theorem continuous_groupTranslate
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ) (q : (Fin 2 → Fin 2 → ℂ) × P) :
    Continuous fun g : GL (Fin 2) ℂ => groupTranslate Φ g q := by
  unfold groupTranslate
  exact hΦ.comp (Continuous.prodMk (continuous_const.matrix_mul Units.continuous_val) continuous_const)

private theorem avg_mul_groupTranslate_mem {weights : ℕ → MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ}
    (hd : IsAveragingDevice avg weights)
    (hK : IsDetOneIsometryGroup) (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ) (hΦ₀ : IsScalarInvariant Φ)
    [FiniteDimensional ℂ (translateSpan Φ)] (γ : GL (Fin 2) ℂ → ℂ) (hγ : Continuous γ) :
    (fun q => avg fun g => γ g * groupTranslate Φ g q) ∈ translateSpan Φ := by
  obtain ⟨s, e, he, hexp⟩ := exists_finite_interpolation Φ
  have htr := continuous_groupTranslate Φ hΦ
  have hfun : (fun q => avg fun g => γ g * groupTranslate Φ g q) =
      ∑ x ∈ s, (avg fun g => γ g * groupTranslate Φ g x) • e x := by
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have h1 : (avg fun g => γ g * groupTranslate Φ g q) =
        avg fun g => ∑ x ∈ s, e x q * (γ g * groupTranslate Φ g x) := by
      refine hd.congr_of_isometries (fun g => γ g * groupTranslate Φ g q)
        (fun g => ∑ x ∈ s, e x q * (γ g * groupTranslate Φ g x)) (hγ.mul (htr q))
        (continuous_finsetSum _ fun x _ => continuous_const.mul (hγ.mul (htr x))) ?_
      intro u hu
      have h := congrFun (hexp _ (groupTranslate_mem_translateSpan hK Φ hΦ₀ u hu)) q
      rw [Finset.sum_apply] at h
      simp only [Pi.smul_apply, smul_eq_mul] at h
      show γ u * groupTranslate Φ u q = ∑ x ∈ s, e x q * (γ u * groupTranslate Φ u x)
      rw [h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [h1, show (avg fun g => ∑ x ∈ s, e x q * (γ g * groupTranslate Φ g x)) =
        ∑ x ∈ s, avg (fun g => e x q * (γ g * groupTranslate Φ g x)) from
        hd.avg_finset_sum s _ fun x => continuous_const.mul (hγ.mul (htr x))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (avg fun g => e x q * (γ g * groupTranslate Φ g x)) = e x q * avg (fun g => γ g * groupTranslate Φ g x)
      from hd.map_smul _ _ (hγ.mul (htr x))]
    ring
  rw [hfun]
  exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (he x)

private def inverseEntry (i l : Fin 2) : C(GL (Fin 2) ℂ, ℂ) :=
  ⟨fun g => ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i l, Units.continuous_coe_inv.matrix_elem i l⟩

private def entryFun (l j : Fin 2) : C(GL (Fin 2) ℂ, ℂ) :=
  ⟨fun g => (g : Matrix (Fin 2) (Fin 2) ℂ) l j, Units.continuous_val.matrix_elem l j⟩

private def adjugateForm (i l : Fin 2) : MvPolynomial (Fin 2 × Fin 2) C(GL (Fin 2) ℂ, ℂ) :=
  ![![MvPolynomial.X (1, 1), -MvPolynomial.X (0, 1)], ![-MvPolynomial.X (1, 0), MvPolynomial.X (0, 0)]] i l

private def linearForm : Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2 → MvPolynomial (Fin 2 × Fin 2) C(GL (Fin 2) ℂ, ℂ)
  | Sum.inl ij => ∑ l : Fin 2, MvPolynomial.C (inverseEntry ij.1 l) * MvPolynomial.X (l, ij.2)
  | Sum.inr ij => ∑ l : Fin 2, adjugateForm ij.1 l * MvPolynomial.C (entryFun l ij.2)

private def substituted (w : MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ) :
    MvPolynomial (Fin 2 × Fin 2) C(GL (Fin 2) ℂ, ℂ) :=
  MvPolynomial.eval₂ (MvPolynomial.C.comp (algebraMap ℂ C(GL (Fin 2) ℂ, ℂ))) linearForm w

private def evalAt (g : GL (Fin 2) ℂ) : C(GL (Fin 2) ℂ, ℂ) →+* ℂ :=
  (Pi.evalRingHom (fun _ : GL (Fin 2) ℂ => ℂ) g).comp ContinuousMap.coeFnRingHom

@[scoped simp] private theorem evalAt_apply (g : GL (Fin 2) ℂ) (f : C(GL (Fin 2) ℂ, ℂ)) : evalAt g f = f g := rfl

private theorem coe_inv_of_det_eq_one (u : GL (Fin 2) ℂ) (hdet : Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    ((u⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.adjugate (u : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [Matrix.coe_units_inv, Matrix.inv_def, hdet]

private theorem eval₂_adjugateForm (g u : GL (Fin 2) ℂ) (i l : Fin 2) :
    MvPolynomial.eval₂ (evalAt g) (entries u) (adjugateForm i l) =
      Matrix.adjugate (u : Matrix (Fin 2) (Fin 2) ℂ) i l := by
  fin_cases i <;> fin_cases l <;> simp [adjugateForm, Matrix.adjugate_fin_two, entries]

private theorem weightPoint_inv_mul (u g : GL (Fin 2) ℂ) (hdet : Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    ∀ v, weightPoint (u⁻¹ * g) v =
      Sum.elim (fun ij : Fin 2 × Fin 2 => (((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
          (u : Matrix (Fin 2) (Fin 2) ℂ)) ij.1 ij.2)
        (fun ij : Fin 2 × Fin 2 => (Matrix.adjugate (u : Matrix (Fin 2) (Fin 2) ℂ) *
          (g : Matrix (Fin 2) (Fin 2) ℂ)) ij.1 ij.2) v
  | Sum.inl ij => by simp [weightPoint, entries, mul_inv_rev]
  | Sum.inr ij => by simp [weightPoint, entries, coe_inv_of_det_eq_one u hdet]

private theorem eval₂_linearForm (g u : GL (Fin 2) ℂ) (hdet : Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    ∀ v, MvPolynomial.eval₂ (evalAt g) (entries u) (linearForm v) = weightPoint (u⁻¹ * g) v
  | Sum.inl ij => by
    rw [weightPoint_inv_mul u g hdet]
    simp [linearForm, inverseEntry, entries, Matrix.mul_apply]
  | Sum.inr ij => by
    rw [weightPoint_inv_mul u g hdet]
    simp [linearForm, eval₂_adjugateForm, entryFun, Matrix.mul_apply]

private theorem eval₂_substituted (w : MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ) (g u : GL (Fin 2) ℂ)
    (hdet : Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    MvPolynomial.eval₂ (evalAt g) (entries u) (substituted w) = MvPolynomial.eval (weightPoint (u⁻¹ * g)) w := by
  induction w using MvPolynomial.induction_on with
  | C a => simp [substituted]
  | add p r hp hr => simp only [substituted, MvPolynomial.eval₂_add, MvPolynomial.eval_add] at hp hr ⊢; rw [hp, hr]
  | mul_X p i hp =>
    simp only [substituted, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval_mul,
      MvPolynomial.eval_X] at hp ⊢
    rw [hp, eval₂_linearForm g u hdet]

private theorem totalDegree_adjugateForm_le (i l : Fin 2) : (adjugateForm i l).totalDegree ≤ 1 := by
  fin_cases i <;> fin_cases l <;> simp [adjugateForm, MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_neg]

private theorem totalDegree_linearForm_le : ∀ v, (linearForm v).totalDegree ≤ 1
  | Sum.inl ij => by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (by simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X])
  | Sum.inr ij => by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, add_zero]
    exact totalDegree_adjugateForm_le _ _

private theorem totalDegree_substituted (w : MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ) :
    (substituted w).totalDegree ≤ w.totalDegree := by
  unfold substituted
  rw [MvPolynomial.eval₂_eq]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [RingHom.comp_apply, MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ =>
    (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (totalDegree_linearForm_le i))).trans ?_
  simp only [mul_one]
  simpa [Finsupp.sum] using MvPolynomial.le_totalDegree hm

private theorem continuous_weightPoint : Continuous weightPoint := by
  refine continuous_pi fun v => ?_
  rcases v with ij | ij
  · exact Units.continuous_coe_inv.matrix_elem ij.1 ij.2
  · exact Units.continuous_val.matrix_elem ij.1 ij.2

private theorem isPolynomialAlong_weightedAverage {weights : ℕ → MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ}
    (hd : IsAveragingDevice avg weights) (hK : IsDetOneIsometryGroup) (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦ : Continuous Φ) (hΦ₀ : IsScalarInvariant Φ) [FiniteDimensional ℂ (translateSpan Φ)]
    (w : MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ) :
    IsPolynomialAlong Φ w.totalDegree (weightedAverage avg Φ w) := by
  classical
  have htr := continuous_groupTranslate Φ hΦ
  refine ⟨?_, fun q => ∑ m ∈ (substituted w).support,
      MvPolynomial.monomial m (avg fun g => (substituted w).coeff m g * groupTranslate Φ g q), ?_, ?_, ?_⟩
  ·
    have hent : Continuous fun g : GL (Fin 2) ℂ => MvPolynomial.eval (weightPoint g) w :=
      (MvPolynomial.continuous_eval w).comp continuous_weightPoint
    exact avg_mul_groupTranslate_mem hd hK Φ hΦ hΦ₀ _ hent
  ·
    intro q
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    simpa [Finsupp.sum] using (MvPolynomial.le_totalDegree hm).trans (totalDegree_substituted w)
  ·
    intro m
    by_cases hm : m ∈ (substituted w).support
    · have h : (fun q => MvPolynomial.coeff m (∑ m' ∈ (substituted w).support,
          MvPolynomial.monomial m' (avg fun g => (substituted w).coeff m' g * groupTranslate Φ g q))) =
          fun q => avg fun g => (substituted w).coeff m g * groupTranslate Φ g q := by
        funext q
        simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hm]
      rw [h]
      exact avg_mul_groupTranslate_mem hd hK Φ hΦ hΦ₀ _ ((substituted w).coeff m).continuous
    · have h : (fun q => MvPolynomial.coeff m (∑ m' ∈ (substituted w).support,
          MvPolynomial.monomial m' (avg fun g => (substituted w).coeff m' g * groupTranslate Φ g q))) =
          fun _ => (0 : ℂ) := by
        funext q
        simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hm]
      rw [h]
      exact (translateSpan Φ).zero_mem
  ·
    intro q u hu hdet
    have hGc : Continuous fun g : GL (Fin 2) ℂ => MvPolynomial.eval (weightPoint (u⁻¹ * g)) w * groupTranslate Φ g q :=
      ((MvPolynomial.continuous_eval w).comp (continuous_weightPoint.comp (continuous_const.mul continuous_id))).mul
        (htr q)
    have h1 : groupTranslate (weightedAverage avg Φ w) u q =
        avg fun h => MvPolynomial.eval (weightPoint (u⁻¹ * (u * h))) w * groupTranslate Φ (u * h) q := by
      show avg (weightedIntegrand Φ w _) = _
      congr 1
      funext h
      simp only [weightedIntegrand, groupTranslate, inv_mul_cancel_left, Units.val_mul, Matrix.mul_assoc,
        Equiv.apply_symm_apply]
    rw [h1, show (avg fun h => MvPolynomial.eval (weightPoint (u⁻¹ * (u * h))) w * groupTranslate Φ (u * h) q) =
        avg (fun g => MvPolynomial.eval (weightPoint (u⁻¹ * g)) w * groupTranslate Φ g q) from
        hd.left_invariant _ hGc u hu]
    have h2 : (fun g => MvPolynomial.eval (weightPoint (u⁻¹ * g)) w * groupTranslate Φ g q) = fun g =>
        ∑ m ∈ (substituted w).support,
          (∏ i ∈ m.support, entries u i ^ m i) * ((substituted w).coeff m g * groupTranslate Φ g q) := by
      funext g
      rw [← eval₂_substituted w g u hdet, MvPolynomial.eval₂_eq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [evalAt_apply]
      ring
    rw [h2, show (avg fun g => ∑ m ∈ (substituted w).support,
          (∏ i ∈ m.support, entries u i ^ m i) * ((substituted w).coeff m g * groupTranslate Φ g q)) =
        ∑ m ∈ (substituted w).support,
          avg (fun g => (∏ i ∈ m.support, entries u i ^ m i) * ((substituted w).coeff m g * groupTranslate Φ g q))
        from hd.avg_finset_sum _ _ fun m => continuous_const.mul (((substituted w).coeff m).continuous.mul (htr q))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.eval_monomial, show
        (avg fun g => (∏ i ∈ m.support, entries u i ^ m i) * ((substituted w).coeff m g * groupTranslate Φ g q)) =
        (∏ i ∈ m.support, entries u i ^ m i) * avg (fun g => (substituted w).coeff m g * groupTranslate Φ g q) from
        hd.map_smul _ _ (((substituted w).coeff m).continuous.mul (htr q)), mul_comm]
    rfl

omit [TopologicalSpace P] in
private theorem exists_degree_forall_isPolynomialAlong (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    [FiniteDimensional ℂ (translateSpan Φ)] :
    ∃ D : ℕ, ∀ d : ℕ, ∀ F, IsPolynomialAlong Φ d F → IsPolynomialAlong Φ D F := by
  let V : ℕ →o Submodule ℂ (translateSpan Φ) :=
    ⟨fun d => (polynomialAlong Φ d).comap (translateSpan Φ).subtype,
      fun d d' hdd' F hF => IsPolynomialAlong.mono hdd' hF⟩
  obtain ⟨D, hD⟩ := monotone_stabilizes_iff_noetherian.2 (inferInstance : IsNoetherian ℂ (translateSpan Φ)) V
  refine ⟨D, fun d F hF => ?_⟩
  rcases le_or_gt d D with hdD | hDd
  · exact hF.mono hdD
  · have hmem : (⟨F, hF.1⟩ : translateSpan Φ) ∈ V d := hF
    rw [← hD d hDd.le] at hmem
    exact hmem

omit [TopologicalSpace P] in
private theorem isPolynomialAlong_of_tendsto (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) [FiniteDimensional ℂ (translateSpan Φ)]
    (D : ℕ) (F : ℕ → (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hF : ∀ n, IsPolynomialAlong Φ D (F n))
    (G : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hlim : ∀ q, Filter.Tendsto (fun n => F n q) Filter.atTop (nhds (G q))) :
    IsPolynomialAlong Φ D G := by
  haveI : FiniteDimensional ℂ (polynomialAlong Φ D) :=
    Submodule.finiteDimensional_of_le (polynomialAlong_le_translateSpan Φ D)
  have hclosed : IsClosed ((polynomialAlong Φ D : Set ((Fin 2 → Fin 2 → ℂ) × P → ℂ))) :=
    Submodule.closed_of_finiteDimensional _
  have htend : Filter.Tendsto F Filter.atTop (nhds G) := tendsto_pi_nhds.2 hlim
  exact hclosed.mem_of_tendsto htend (Filter.Eventually.of_forall hF)

private theorem tendsto_weightedAverage {weights : ℕ → MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ}
    (hd : IsAveragingDevice avg weights) (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ)
    (q : (Fin 2 → Fin 2 → ℂ) × P) :
    Filter.Tendsto (fun n => weightedAverage avg Φ (weights n) q) Filter.atTop (nhds (Φ q)) := by
  have h := hd.approximate _ (continuous_groupTranslate Φ hΦ q)
  have h1 : groupTranslate Φ (1 : GL (Fin 2) ℂ) q = Φ q := by
    simp [groupTranslate]
  show Filter.Tendsto (fun n => avg fun h => MvPolynomial.eval (weightPoint h) (weights n) * groupTranslate Φ h q)
    Filter.atTop (nhds (Φ q))
  rw [← h1]
  exact h

private theorem exists_isPolynomialAlong_self {weights : ℕ → MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ}
    (hd : IsAveragingDevice avg weights) (hK : IsDetOneIsometryGroup) (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦ : Continuous Φ) (hΦ₀ : IsScalarInvariant Φ) [FiniteDimensional ℂ (translateSpan Φ)] :
    ∃ D : ℕ, IsPolynomialAlong Φ D Φ := by
  obtain ⟨D, hD⟩ := exists_degree_forall_isPolynomialAlong Φ
  exact ⟨D, isPolynomialAlong_of_tendsto Φ D (fun n => weightedAverage avg Φ (weights n))
    (fun n => hD _ _ (isPolynomialAlong_weightedAverage hd hK Φ hΦ hΦ₀ (weights n))) Φ
    (fun q => tendsto_weightedAverage hd Φ hΦ q)⟩

end device

end RightFiniteExpansion
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted.RightFiniteExpansion"

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted.RightFiniteExpansion"

noncomputable section

namespace RightFiniteExpansion

variable {P : Type} [TopologicalSpace P]

private theorem isIsometry_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) : IsIsometry (unitaryElt ψ η ξ₁ ξ₂) := by
  exact ChartInvariance.unitaryElt_unitary ψ η ξ₁ ξ₂

private theorem det_unitaryElt_zero (η ξ₁ ξ₂ : ℝ) :
    Matrix.det ((unitaryElt 0 η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  have hU : ((unitaryElt 0 η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp ((0 : ℝ) * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
        Complex.exp ((0 : ℝ) * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
      Complex.exp ((0 : ℝ) * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
        Complex.exp ((0 : ℝ) * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))] := rfl
  have h1 : Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h2 : Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h3 : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq η
  rw [hU, Matrix.det_fin_two_of]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  linear_combination (Real.cos η : ℂ) ^ 2 * h1 + (Real.sin η : ℂ) ^ 2 * h2 + h3

private def scalarElt (z : ℂ) (hz : z ≠ 0) : GL (Fin 2) ℂ :=
  Units.map (Matrix.scalar (Fin 2)).toMonoidHom (Units.mk0 z hz)

private theorem unitaryElt_eq_scalarElt_mul (ψ η ξ₁ ξ₂ : ℝ) :
    unitaryElt ψ η ξ₁ ξ₂ = scalarElt (Complex.exp (ψ * Complex.I)) (Complex.exp_ne_zero _) * unitaryElt 0 η ξ₁ ξ₂ := by
  have hU : ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
        Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
      Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
        Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))] := rfl
  have hU0 : ((unitaryElt 0 η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp ((0 : ℝ) * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
        Complex.exp ((0 : ℝ) * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
      Complex.exp ((0 : ℝ) * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
        Complex.exp ((0 : ℝ) * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))] := rfl
  have hs : ((scalarElt (Complex.exp (ψ * Complex.I)) (Complex.exp_ne_zero _) : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = Matrix.scalar (Fin 2) (Complex.exp (ψ * Complex.I)) := rfl
  apply Units.ext
  rw [Units.val_mul, hU, hU0, hs, Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, Complex.ofReal_zero]

private theorem continuous_conjEntries : Continuous conjEntries := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : (Units.val ∘ conjEntries) =
        fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) := by
      funext g
      ext i j
      simp [conjEntries]
    rw [h]
    exact Units.continuous_val.matrix_map Complex.continuous_conj
  · have h : (fun g : GL (Fin 2) ℂ => (((conjEntries g)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) =
        fun g : GL (Fin 2) ℂ => ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) := by
      funext g
      rw [show (conjEntries g)⁻¹ = conjEntries g⁻¹ from (Matrix.GeneralLinearGroup.map_inv (starRingEnd ℂ) g).symm]
      ext i j
      simp only [conjEntries, Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
    rw [h]
    exact Units.continuous_coe_inv.matrix_map Complex.continuous_conj

private theorem continuous_unitaryElt : Continuous fun a : ℝ × ℝ × ℝ × ℝ => unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2 := by
  refine Units.continuous_iff.2 ⟨continuous_unitaryElt_coe, ?_⟩
  have h : (fun a : ℝ × ℝ × ℝ × ℝ => (((unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2)⁻¹ : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ)) = fun a : ℝ × ℝ × ℝ × ℝ =>
        star ((unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext a
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.inv_eq_left_inv (isIsometry_unitaryElt _ _ _ _)
  rw [h]
  exact continuous_unitaryElt_coe.star

private def scalarFreeAverage (F : GL (Fin 2) ℂ → ℂ) : ℂ :=
  (1 / (2 * Real.pi ^ 2) : ℂ) *
    ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * F (unitaryElt 0 η ξ₁ ξ₂)

private theorem unitaryAverage_eq_scalarFreeAverage (F : GL (Fin 2) ℂ → ℂ)
    (hF : ∀ ψ η ξ₁ ξ₂ : ℝ, F (unitaryElt ψ η ξ₁ ξ₂) = F (unitaryElt 0 η ξ₁ ξ₂)) :
    unitaryAverage F = scalarFreeAverage F := by
  unfold unitaryAverage scalarFreeAverage
  have hin : ∀ ψ : ℝ, (∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)) =
      ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * F (unitaryElt 0 η ξ₁ ξ₂) := by
    intro ψ
    simp only [hF ψ]
  simp only [hin]
  rw [intervalIntegral.integral_const, sub_zero]
  erw [Complex.real_smul]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp
  ring

private theorem continuous_scalarFreeAverage {X : Type} [TopologicalSpace X] (H : X → GL (Fin 2) ℂ → ℂ)
    (hH : Continuous fun q : X × GL (Fin 2) ℂ => H q.1 q.2) : Continuous fun x => scalarFreeAverage (H x) := by
  unfold scalarFreeAverage
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : X) (η : ℝ) => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * H x (unitaryElt 0 η ξ₁ ξ₂)) ?_ _ _
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (q : X × ℝ) (ξ₁ : ℝ) => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin q.2 * Real.cos q.2 : ℂ) * H q.1 (unitaryElt 0 q.2 ξ₁ ξ₂)) ?_ _ _
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (q : (X × ℝ) × ℝ) (ξ₂ : ℝ) =>
      (Real.sin q.1.2 * Real.cos q.1.2 : ℂ) * H q.1.1 (unitaryElt 0 q.1.2 q.2 ξ₂)) ?_ _ _
  apply Continuous.mul
  · have h : Continuous fun q : ((X × ℝ) × ℝ) × ℝ => q.1.1.2 := by fun_prop
    exact (Complex.continuous_ofReal.comp (Real.continuous_sin.comp h)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_cos.comp h))
  · have hang : Continuous fun q : ((X × ℝ) × ℝ) × ℝ => ((0, q.1.1.2, q.1.2, q.2) : ℝ × ℝ × ℝ × ℝ) := by fun_prop
    have hU := continuous_unitaryElt.comp hang
    simp only [Function.comp_def] at hU
    have hx : Continuous fun q : ((X × ℝ) × ℝ) × ℝ => q.1.1.1 := by fun_prop
    have hpair : Continuous fun q : ((X × ℝ) × ℝ) × ℝ =>
        ((q.1.1.1, unitaryElt 0 q.1.1.2 q.1.2 q.2) : X × GL (Fin 2) ℂ) := hx.prodMk hU
    exact hH.comp hpair

private theorem scalarFreeAverage_add (F G : GL (Fin 2) ℂ → ℂ) (hF : Continuous F) (hG : Continuous G) :
    scalarFreeAverage (fun h => F h + G h) = scalarFreeAverage F + scalarFreeAverage G := by
  unfold scalarFreeAverage
  have hk : ∀ (K : GL (Fin 2) ℂ → ℂ), Continuous K → Continuous fun q : (ℝ × ℝ) × ℝ =>
      (Real.sin q.1.1 * Real.cos q.1.1 : ℂ) * K (unitaryElt 0 q.1.1 q.1.2 q.2) := by
    intro K hK
    have hang : Continuous fun q : (ℝ × ℝ) × ℝ => ((0, q.1.1, q.1.2, q.2) : ℝ × ℝ × ℝ × ℝ) := by fun_prop
    have hU := continuous_unitaryElt.comp hang
    simp only [Function.comp_def] at hU
    have h1 : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.1 := by fun_prop
    exact ((Complex.continuous_ofReal.comp (Real.continuous_sin.comp h1)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_cos.comp h1))).mul (hK.comp hU)
  have hin1 : ∀ (K : GL (Fin 2) ℂ → ℂ), Continuous K → ∀ η : ℝ, Continuous fun ξ₁ : ℝ =>
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * K (unitaryElt 0 η ξ₁ ξ₂) := by
    intro K hK η
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (ξ₁ : ℝ) (ξ₂ : ℝ) => (Real.sin η * Real.cos η : ℂ) * K (unitaryElt 0 η ξ₁ ξ₂)) ?_ _ _
    have hc : Continuous fun q : ℝ × ℝ => (((η, q.1), q.2) : (ℝ × ℝ) × ℝ) := by fun_prop
    have h := (hk K hK).comp hc
    simp only [Function.comp_def] at h
    exact h
  have hin2 : ∀ (K : GL (Fin 2) ℂ → ℂ), Continuous K → Continuous fun η : ℝ =>
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * K (unitaryElt 0 η ξ₁ ξ₂) := by
    intro K hK
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (η : ℝ) (ξ₁ : ℝ) => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * K (unitaryElt 0 η ξ₁ ξ₂)) ?_ _ _
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (q : ℝ × ℝ) (ξ₂ : ℝ) => (Real.sin q.1 * Real.cos q.1 : ℂ) * K (unitaryElt 0 q.1 q.2 ξ₂)) ?_ _ _
    exact hk K hK
  have h3 : ∀ η ξ₁ : ℝ, (∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * (F (unitaryElt 0 η ξ₁ ξ₂) + G (unitaryElt 0 η ξ₁ ξ₂))) =
      (∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt 0 η ξ₁ ξ₂)) +
        ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * G (unitaryElt 0 η ξ₁ ξ₂) := by
    intro η ξ₁
    simp only [mul_add]
    have hc : Continuous fun ξ₂ : ℝ => (((η, ξ₁), ξ₂) : (ℝ × ℝ) × ℝ) := by fun_prop
    have hcF := (hk F hF).comp hc
    have hcG := (hk G hG).comp hc
    simp only [Function.comp_def] at hcF hcG
    exact intervalIntegral.integral_add (hcF.intervalIntegrable _ _) (hcG.intervalIntegrable _ _)
  have h2 : ∀ η : ℝ, (∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * (F (unitaryElt 0 η ξ₁ ξ₂) + G (unitaryElt 0 η ξ₁ ξ₂))) =
      (∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * F (unitaryElt 0 η ξ₁ ξ₂)) +
        ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * G (unitaryElt 0 η ξ₁ ξ₂) := by
    intro η
    simp only [h3]
    exact intervalIntegral.integral_add ((hin1 F hF η).intervalIntegrable _ _) ((hin1 G hG η).intervalIntegrable _ _)
  simp only [h2]
  rw [intervalIntegral.integral_add ((hin2 F hF).intervalIntegrable _ _) ((hin2 G hG).intervalIntegrable _ _), mul_add]

private theorem scalarFreeAverage_const_mul (c : ℂ) (F : GL (Fin 2) ℂ → ℂ) :
    scalarFreeAverage (fun h => c * F h) = c * scalarFreeAverage F := by
  unfold scalarFreeAverage
  have h : ∀ (η : ℝ) (k : GL (Fin 2) ℂ),
      (Real.sin η * Real.cos η : ℂ) * (c * F k) = c * ((Real.sin η * Real.cos η : ℂ) * F k) :=
    fun η k => by ring
  simp only [h]
  have e3 : ∀ η ξ₁ : ℝ, (∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      c * ((Real.sin η * Real.cos η : ℂ) * F (unitaryElt 0 η ξ₁ ξ₂))) =
      c * ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt 0 η ξ₁ ξ₂) :=
    fun η ξ₁ => intervalIntegral.integral_const_mul c _
  simp only [e3]
  have e2 : ∀ η : ℝ, (∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), c * ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * F (unitaryElt 0 η ξ₁ ξ₂)) =
      c * ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * F (unitaryElt 0 η ξ₁ ξ₂) :=
    fun η => intervalIntegral.integral_const_mul c _
  simp only [e2]
  have e1 : (∫ η in (0 : ℝ)..(Real.pi / 2), c * ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * F (unitaryElt 0 η ξ₁ ξ₂)) =
      c * ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * F (unitaryElt 0 η ξ₁ ξ₂) :=
    intervalIntegral.integral_const_mul c _
  rw [e1]
  ring

private theorem unitaryAverage_add (F G : GL (Fin 2) ℂ → ℂ) (hF : Continuous F) (hG : Continuous G) :
    unitaryAverage (fun h => F h + G h) = unitaryAverage F + unitaryAverage G := by
  simp only [unitaryAverage]
  have hF4 : Continuous fun a : ℝ × ℝ × ℝ × ℝ => F (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) :=
    hF.comp continuous_unitaryElt
  have hG4 : Continuous fun a : ℝ × ℝ × ℝ × ℝ => G (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) :=
    hG.comp continuous_unitaryElt
  have hwc : Continuous fun a : ℝ × ℝ × ℝ × ℝ => (Real.sin a.2.1 * Real.cos a.2.1 : ℂ) := by fun_prop
  have hIF : Continuous fun a : ℝ × ℝ × ℝ × ℝ =>
      (Real.sin a.2.1 * Real.cos a.2.1 : ℂ) * F (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) := hwc.mul hF4
  have hIG : Continuous fun a : ℝ × ℝ × ℝ × ℝ =>
      (Real.sin a.2.1 * Real.cos a.2.1 : ℂ) * G (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) := hwc.mul hG4
  have hr₃ : Continuous fun p : (ℝ × ℝ × ℝ) × ℝ => ((p.1.1, p.1.2.1, p.1.2.2, p.2) : ℝ × ℝ × ℝ × ℝ) := by fun_prop
  have hr₂ : Continuous fun p : (ℝ × ℝ) × ℝ => ((p.1.1, p.1.2, p.2) : ℝ × ℝ × ℝ) := by fun_prop
  have hUF := hIF.comp hr₃
  have hUG := hIG.comp hr₃
  have hJF : Continuous fun b : ℝ × ℝ × ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin b.2.1 * Real.cos b.2.1 : ℂ) * F (unitaryElt b.1 b.2.1 b.2.2 ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (b : ℝ × ℝ × ℝ) (ξ₂ : ℝ) =>
      (Real.sin b.2.1 * Real.cos b.2.1 : ℂ) * F (unitaryElt b.1 b.2.1 b.2.2 ξ₂)) hUF _ _
  have hJG : Continuous fun b : ℝ × ℝ × ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin b.2.1 * Real.cos b.2.1 : ℂ) * G (unitaryElt b.1 b.2.1 b.2.2 ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (b : ℝ × ℝ × ℝ) (ξ₂ : ℝ) =>
      (Real.sin b.2.1 * Real.cos b.2.1 : ℂ) * G (unitaryElt b.1 b.2.1 b.2.2 ξ₂)) hUG _ _
  have hVF := hJF.comp hr₂
  have hVG := hJG.comp hr₂
  have hKF : Continuous fun c : ℝ × ℝ => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin c.2 * Real.cos c.2 : ℂ) * F (unitaryElt c.1 c.2 ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (c : ℝ × ℝ) (ξ₁ : ℝ) =>
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin c.2 * Real.cos c.2 : ℂ) * F (unitaryElt c.1 c.2 ξ₁ ξ₂)) hVF _ _
  have hKG : Continuous fun c : ℝ × ℝ => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin c.2 * Real.cos c.2 : ℂ) * G (unitaryElt c.1 c.2 ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (c : ℝ × ℝ) (ξ₁ : ℝ) =>
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin c.2 * Real.cos c.2 : ℂ) * G (unitaryElt c.1 c.2 ξ₁ ξ₂)) hVG _ _
  have hLF : Continuous fun ψ : ℝ => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (ψ η : ℝ) =>
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)) hKF _ _
  have hLG : Continuous fun ψ : ℝ => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * G (unitaryElt ψ η ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (ψ η : ℝ) =>
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * G (unitaryElt ψ η ξ₁ ξ₂)) hKG _ _
  have e₄ : ∀ ψ η ξ₁ : ℝ, (∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * (F (unitaryElt ψ η ξ₁ ξ₂) + G (unitaryElt ψ η ξ₁ ξ₂))) =
      (∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)) +
        ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * G (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ η ξ₁
    have ht : Continuous fun ξ₂ : ℝ => ((ψ, η, ξ₁, ξ₂) : ℝ × ℝ × ℝ × ℝ) := by fun_prop
    have h₁ := hIF.comp ht
    have h₂ := hIG.comp ht
    simp_rw [mul_add]
    exact intervalIntegral.integral_add (h₁.intervalIntegrable _ _) (h₂.intervalIntegrable _ _)
  have e₃ : ∀ ψ η : ℝ, (∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * (F (unitaryElt ψ η ξ₁ ξ₂) + G (unitaryElt ψ η ξ₁ ξ₂))) =
      (∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)) +
        ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * G (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ η
    have ht : Continuous fun ξ₁ : ℝ => ((ψ, η, ξ₁) : ℝ × ℝ × ℝ) := by fun_prop
    have h₁ := hJF.comp ht
    have h₂ := hJG.comp ht
    simp_rw [e₄]
    exact intervalIntegral.integral_add (h₁.intervalIntegrable _ _) (h₂.intervalIntegrable _ _)
  have e₂ : ∀ ψ : ℝ, (∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * (F (unitaryElt ψ η ξ₁ ξ₂) + G (unitaryElt ψ η ξ₁ ξ₂))) =
      (∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)) +
        ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * G (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ
    have ht : Continuous fun η : ℝ => ((ψ, η) : ℝ × ℝ) := by fun_prop
    have h₁ := hKF.comp ht
    have h₂ := hKG.comp ht
    simp_rw [e₃]
    exact intervalIntegral.integral_add (h₁.intervalIntegrable _ _) (h₂.intervalIntegrable _ _)
  simp_rw [e₂]
  rw [intervalIntegral.integral_add (hLF.intervalIntegrable _ _) (hLG.intervalIntegrable _ _), mul_add]

private theorem unitaryAverage_const_mul' (c : ℂ) (F : GL (Fin 2) ℂ → ℂ) :
    unitaryAverage (fun h => c * F h) = c * unitaryAverage F := by
  exact ChartInvariance.unitaryAverage_const_mul c F

private theorem unitaryAverage_congr_of_isIsometry (F G : GL (Fin 2) ℂ → ℂ)
    (hFG : ∀ u : GL (Fin 2) ℂ, IsIsometry u → F u = G u) : unitaryAverage F = unitaryAverage G := by
  have h : ∀ ψ η ξ₁ ξ₂ : ℝ, F (unitaryElt ψ η ξ₁ ξ₂) = G (unitaryElt ψ η ξ₁ ξ₂) :=
    fun ψ η ξ₁ ξ₂ => hFG _ (isIsometry_unitaryElt ψ η ξ₁ ξ₂)
  simp only [unitaryAverage, h]

private def realAverage (G : GL (Fin 2) ℂ → ℝ) : ℝ :=
  (1 / (4 * Real.pi ^ 3)) *
    ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2),
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂)

private theorem unitaryAverage_ofReal (G : GL (Fin 2) ℂ → ℝ) :
    unitaryAverage (fun h => (G h : ℂ)) = (realAverage G : ℂ) := by
  unfold unitaryAverage realAverage
  have e4 : ∀ ψ η ξ₁ : ℝ, (∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * (G (unitaryElt ψ η ξ₁ ξ₂) : ℂ)) =
      ((∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) : ℝ) : ℂ) := by
    intro ψ η ξ₁
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    funext ξ₂
    push_cast
    ring
  have e3 : ∀ ψ η : ℝ, (∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * (G (unitaryElt ψ η ξ₁ ξ₂) : ℂ)) =
      ((∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) : ℝ) : ℂ) := by
    intro ψ η
    simp only [e4]
    exact intervalIntegral.integral_ofReal
  have e2 : ∀ ψ : ℝ, (∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * (G (unitaryElt ψ η ξ₁ ξ₂) : ℂ)) =
      ((∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) : ℝ) : ℂ) := by
    intro ψ
    simp only [e3]
    exact intervalIntegral.integral_ofReal
  simp only [e2, intervalIntegral.integral_ofReal]
  push_cast
  ring

private theorem norm_unitaryAverage_le_realAverage (F : GL (Fin 2) ℂ → ℂ) (G : GL (Fin 2) ℂ → ℝ) (hF : Continuous F)
    (hG : Continuous G) (hFG : ∀ u : GL (Fin 2) ℂ, IsIsometry u → ‖F u‖ ≤ G u) :
    ‖unitaryAverage F‖ ≤ realAverage G := by
  simp only [unitaryAverage, realAverage]
  have hwc : Continuous fun a : ℝ × ℝ × ℝ × ℝ => (Real.sin a.2.1 * Real.cos a.2.1 : ℂ) := by fun_prop
  have hwr : Continuous fun a : ℝ × ℝ × ℝ × ℝ => Real.sin a.2.1 * Real.cos a.2.1 := by fun_prop
  have hr₃ : Continuous fun p : (ℝ × ℝ × ℝ) × ℝ => ((p.1.1, p.1.2.1, p.1.2.2, p.2) : ℝ × ℝ × ℝ × ℝ) := by fun_prop
  have hr₂ : Continuous fun p : (ℝ × ℝ) × ℝ => ((p.1.1, p.1.2, p.2) : ℝ × ℝ × ℝ) := by fun_prop
  have hF4 : Continuous fun a : ℝ × ℝ × ℝ × ℝ => F (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) :=
    hF.comp continuous_unitaryElt
  have hIF : Continuous fun a : ℝ × ℝ × ℝ × ℝ =>
      (Real.sin a.2.1 * Real.cos a.2.1 : ℂ) * F (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) := hwc.mul hF4
  have hUF := hIF.comp hr₃
  have hJF : Continuous fun b : ℝ × ℝ × ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin b.2.1 * Real.cos b.2.1 : ℂ) * F (unitaryElt b.1 b.2.1 b.2.2 ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (b : ℝ × ℝ × ℝ) (ξ₂ : ℝ) =>
      (Real.sin b.2.1 * Real.cos b.2.1 : ℂ) * F (unitaryElt b.1 b.2.1 b.2.2 ξ₂)) hUF _ _
  have hVF := hJF.comp hr₂
  have hKF : Continuous fun c : ℝ × ℝ => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin c.2 * Real.cos c.2 : ℂ) * F (unitaryElt c.1 c.2 ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (c : ℝ × ℝ) (ξ₁ : ℝ) =>
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin c.2 * Real.cos c.2 : ℂ) * F (unitaryElt c.1 c.2 ξ₁ ξ₂)) hVF _ _
  have hLF : Continuous fun ψ : ℝ => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (ψ η : ℝ) =>
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)) hKF _ _
  have hG4 : Continuous fun a : ℝ × ℝ × ℝ × ℝ => G (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) :=
    hG.comp continuous_unitaryElt
  have hIG : Continuous fun a : ℝ × ℝ × ℝ × ℝ =>
      Real.sin a.2.1 * Real.cos a.2.1 * G (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) := hwr.mul hG4
  have hUG := hIG.comp hr₃
  have hJG : Continuous fun b : ℝ × ℝ × ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.sin b.2.1 * Real.cos b.2.1 * G (unitaryElt b.1 b.2.1 b.2.2 ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (b : ℝ × ℝ × ℝ) (ξ₂ : ℝ) =>
      Real.sin b.2.1 * Real.cos b.2.1 * G (unitaryElt b.1 b.2.1 b.2.2 ξ₂)) hUG _ _
  have hVG := hJG.comp hr₂
  have hKG : Continuous fun c : ℝ × ℝ => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.sin c.2 * Real.cos c.2 * G (unitaryElt c.1 c.2 ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (c : ℝ × ℝ) (ξ₁ : ℝ) =>
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin c.2 * Real.cos c.2 * G (unitaryElt c.1 c.2 ξ₁ ξ₂)) hVG _ _
  have hLG : Continuous fun ψ : ℝ => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (ψ η : ℝ) =>
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂)) hKG _ _
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have b₄ : ∀ ψ η : ℝ, η ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → ∀ ξ₁ ξ₂ : ℝ,
      ‖(Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)‖ ≤
        Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ η hη ξ₁ ξ₂
    have hw : 0 ≤ Real.sin η * Real.cos η :=
      mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hη.1 (by linarith [hη.2, Real.pi_pos]))
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hη.1, Real.pi_pos], hη.2⟩)
    rw [norm_mul, show (Real.sin η * Real.cos η : ℂ) = ((Real.sin η * Real.cos η : ℝ) : ℂ) by norm_cast,
      Complex.norm_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (hFG _ (isIsometry_unitaryElt ψ η ξ₁ ξ₂)) hw
  have b₃ : ∀ ψ η : ℝ, η ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → ∀ ξ₁ : ℝ,
      ‖∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)‖ ≤
        ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ η hη ξ₁
    have ht : Continuous fun ξ₂ : ℝ => ((ψ, η, ξ₁, ξ₂) : ℝ × ℝ × ℝ × ℝ) := by fun_prop
    refine (intervalIntegral.norm_integral_le_integral_norm h2π).trans ?_
    exact intervalIntegral.integral_mono_on h2π ((hIF.comp ht).norm.intervalIntegrable _ _)
      ((hIG.comp ht).intervalIntegrable _ _) fun ξ₂ _ => b₄ ψ η hη ξ₁ ξ₂
  have b₂ : ∀ ψ η : ℝ, η ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      ‖∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)‖ ≤
        ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ η hη
    have ht : Continuous fun ξ₁ : ℝ => ((ψ, η, ξ₁) : ℝ × ℝ × ℝ) := by fun_prop
    refine (intervalIntegral.norm_integral_le_integral_norm h2π).trans ?_
    exact intervalIntegral.integral_mono_on h2π ((hJF.comp ht).norm.intervalIntegrable _ _)
      ((hJG.comp ht).intervalIntegrable _ _) fun ξ₁ _ => b₃ ψ η hη ξ₁
  have b₁ : ∀ ψ : ℝ,
      ‖∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)‖ ≤
        ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ
    have ht : Continuous fun η : ℝ => ((ψ, η) : ℝ × ℝ) := by fun_prop
    have hπ2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    refine (intervalIntegral.norm_integral_le_integral_norm hπ2).trans ?_
    exact intervalIntegral.integral_mono_on hπ2 ((hKF.comp ht).norm.intervalIntegrable _ _)
      ((hKG.comp ht).intervalIntegrable _ _) fun η hη => b₂ ψ η hη
  have b₀ : ‖∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)‖ ≤
      ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) := by
    refine (intervalIntegral.norm_integral_le_integral_norm h2π).trans ?_
    exact intervalIntegral.integral_mono_on h2π (hLF.norm.intervalIntegrable _ _) (hLG.intervalIntegrable _ _)
      fun ψ _ => b₁ ψ
  have hc : ‖(1 / (4 * Real.pi ^ 3) : ℂ)‖ = 1 / (4 * Real.pi ^ 3) := by
    rw [show (1 / (4 * Real.pi ^ 3) : ℂ) = ((1 / (4 * Real.pi ^ 3) : ℝ) : ℂ) by norm_cast,
      Complex.norm_of_nonneg (by positivity)]
  rw [norm_mul, hc]
  exact mul_le_mul_of_nonneg_left b₀ (by positivity)

private theorem realAverage_mono (G₁ G₂ : GL (Fin 2) ℂ → ℝ) (hG₁ : Continuous G₁) (hG₂ : Continuous G₂)
    (h : ∀ u : GL (Fin 2) ℂ, IsIsometry u → G₁ u ≤ G₂ u) : realAverage G₁ ≤ realAverage G₂ := by
  simp only [realAverage]
  have hwr : Continuous fun a : ℝ × ℝ × ℝ × ℝ => Real.sin a.2.1 * Real.cos a.2.1 := by fun_prop
  have hr₃ : Continuous fun p : (ℝ × ℝ × ℝ) × ℝ => ((p.1.1, p.1.2.1, p.1.2.2, p.2) : ℝ × ℝ × ℝ × ℝ) := by fun_prop
  have hr₂ : Continuous fun p : (ℝ × ℝ) × ℝ => ((p.1.1, p.1.2, p.2) : ℝ × ℝ × ℝ) := by fun_prop
  have h₁4 : Continuous fun a : ℝ × ℝ × ℝ × ℝ => G₁ (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) :=
    hG₁.comp continuous_unitaryElt
  have hI₁ : Continuous fun a : ℝ × ℝ × ℝ × ℝ =>
      Real.sin a.2.1 * Real.cos a.2.1 * G₁ (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) := hwr.mul h₁4
  have hU₁ := hI₁.comp hr₃
  have hJ₁ : Continuous fun b : ℝ × ℝ × ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.sin b.2.1 * Real.cos b.2.1 * G₁ (unitaryElt b.1 b.2.1 b.2.2 ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (b : ℝ × ℝ × ℝ) (ξ₂ : ℝ) =>
      Real.sin b.2.1 * Real.cos b.2.1 * G₁ (unitaryElt b.1 b.2.1 b.2.2 ξ₂)) hU₁ _ _
  have hV₁ := hJ₁.comp hr₂
  have hK₁ : Continuous fun c : ℝ × ℝ => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.sin c.2 * Real.cos c.2 * G₁ (unitaryElt c.1 c.2 ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (c : ℝ × ℝ) (ξ₁ : ℝ) =>
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin c.2 * Real.cos c.2 * G₁ (unitaryElt c.1 c.2 ξ₁ ξ₂)) hV₁ _ _
  have hL₁ : Continuous fun ψ : ℝ => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η * Real.cos η * G₁ (unitaryElt ψ η ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (ψ η : ℝ) =>
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        Real.sin η * Real.cos η * G₁ (unitaryElt ψ η ξ₁ ξ₂)) hK₁ _ _
  have h₂4 : Continuous fun a : ℝ × ℝ × ℝ × ℝ => G₂ (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) :=
    hG₂.comp continuous_unitaryElt
  have hI₂ : Continuous fun a : ℝ × ℝ × ℝ × ℝ =>
      Real.sin a.2.1 * Real.cos a.2.1 * G₂ (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) := hwr.mul h₂4
  have hU₂ := hI₂.comp hr₃
  have hJ₂ : Continuous fun b : ℝ × ℝ × ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.sin b.2.1 * Real.cos b.2.1 * G₂ (unitaryElt b.1 b.2.1 b.2.2 ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (b : ℝ × ℝ × ℝ) (ξ₂ : ℝ) =>
      Real.sin b.2.1 * Real.cos b.2.1 * G₂ (unitaryElt b.1 b.2.1 b.2.2 ξ₂)) hU₂ _ _
  have hV₂ := hJ₂.comp hr₂
  have hK₂ : Continuous fun c : ℝ × ℝ => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.sin c.2 * Real.cos c.2 * G₂ (unitaryElt c.1 c.2 ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (c : ℝ × ℝ) (ξ₁ : ℝ) =>
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin c.2 * Real.cos c.2 * G₂ (unitaryElt c.1 c.2 ξ₁ ξ₂)) hV₂ _ _
  have hL₂ : Continuous fun ψ : ℝ => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η * Real.cos η * G₂ (unitaryElt ψ η ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (ψ η : ℝ) =>
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        Real.sin η * Real.cos η * G₂ (unitaryElt ψ η ξ₁ ξ₂)) hK₂ _ _
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have m₄ : ∀ ψ η : ℝ, η ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → ∀ ξ₁ ξ₂ : ℝ,
      Real.sin η * Real.cos η * G₁ (unitaryElt ψ η ξ₁ ξ₂) ≤ Real.sin η * Real.cos η * G₂ (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ η hη ξ₁ ξ₂
    have hw : 0 ≤ Real.sin η * Real.cos η :=
      mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hη.1 (by linarith [hη.2, Real.pi_pos]))
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hη.1, Real.pi_pos], hη.2⟩)
    exact mul_le_mul_of_nonneg_left (h _ (isIsometry_unitaryElt ψ η ξ₁ ξ₂)) hw
  have m₃ : ∀ ψ η : ℝ, η ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → ∀ ξ₁ : ℝ,
      (∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η * Real.cos η * G₁ (unitaryElt ψ η ξ₁ ξ₂)) ≤
        ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η * Real.cos η * G₂ (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ η hη ξ₁
    have ht : Continuous fun ξ₂ : ℝ => ((ψ, η, ξ₁, ξ₂) : ℝ × ℝ × ℝ × ℝ) := by fun_prop
    exact intervalIntegral.integral_mono_on h2π ((hI₁.comp ht).intervalIntegrable _ _)
      ((hI₂.comp ht).intervalIntegrable _ _) fun ξ₂ _ => m₄ ψ η hη ξ₁ ξ₂
  have m₂ : ∀ ψ η : ℝ, η ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      (∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          Real.sin η * Real.cos η * G₁ (unitaryElt ψ η ξ₁ ξ₂)) ≤
        ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          Real.sin η * Real.cos η * G₂ (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ η hη
    have ht : Continuous fun ξ₁ : ℝ => ((ψ, η, ξ₁) : ℝ × ℝ × ℝ) := by fun_prop
    exact intervalIntegral.integral_mono_on h2π ((hJ₁.comp ht).intervalIntegrable _ _)
      ((hJ₂.comp ht).intervalIntegrable _ _) fun ξ₁ _ => m₃ ψ η hη ξ₁
  have m₁ : ∀ ψ : ℝ,
      (∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          Real.sin η * Real.cos η * G₁ (unitaryElt ψ η ξ₁ ξ₂)) ≤
        ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          Real.sin η * Real.cos η * G₂ (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ
    have ht : Continuous fun η : ℝ => ((ψ, η) : ℝ × ℝ) := by fun_prop
    exact intervalIntegral.integral_mono_on (by positivity) ((hK₁.comp ht).intervalIntegrable _ _)
      ((hK₂.comp ht).intervalIntegrable _ _) fun η hη => m₂ ψ η hη
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact intervalIntegral.integral_mono_on h2π (hL₁.intervalIntegrable _ _) (hL₂.intervalIntegrable _ _)
    fun ψ _ => m₁ ψ

private theorem realAverage_const_mul (c : ℝ) (G : GL (Fin 2) ℂ → ℝ) :
    realAverage (fun h => c * G h) = c * realAverage G := by
  unfold realAverage
  have h : ∀ (η : ℝ) (k : GL (Fin 2) ℂ), Real.sin η * Real.cos η * (c * G k) = c * (Real.sin η * Real.cos η * G k) :=
    fun η k => by ring
  simp only [h, intervalIntegral.integral_const_mul]
  ring

private theorem realAverage_const (c : ℝ) : realAverage (fun _ => c) = c := by
  have h1 := unitaryAverage_ofReal (fun _ : GL (Fin 2) ℂ => c)
  have h2 := ChartInvariance.unitaryAverage_const_mul (c : ℂ) (fun _ => (1 : ℂ))
  simp only [mul_one] at h2
  rw [h2, ChartInvariance.unitaryAverage_one, mul_one] at h1
  exact_mod_cast h1.symm

private theorem realAverage_pos
    (G : GL (Fin 2) ℂ → ℝ) (hG : Continuous G) (h0 : ∀ u : GL (Fin 2) ℂ, IsIsometry u → 0 ≤ G u)
    (ψ₀ η₀ ξ₁₀ ξ₂₀ : ℝ) (hψ : ψ₀ ∈ Set.Ioo 0 (2 * Real.pi)) (hη : η₀ ∈ Set.Ioo 0 (Real.pi / 2))
    (hξ₁ : ξ₁₀ ∈ Set.Ioo 0 (2 * Real.pi)) (hξ₂ : ξ₂₀ ∈ Set.Ioo 0 (2 * Real.pi))
    (hpos : 0 < G (unitaryElt ψ₀ η₀ ξ₁₀ ξ₂₀)) : 0 < realAverage G := by
  simp only [realAverage]
  have hwr : Continuous fun a : ℝ × ℝ × ℝ × ℝ => Real.sin a.2.1 * Real.cos a.2.1 := by fun_prop
  have hr₃ : Continuous fun p : (ℝ × ℝ × ℝ) × ℝ => ((p.1.1, p.1.2.1, p.1.2.2, p.2) : ℝ × ℝ × ℝ × ℝ) := by fun_prop
  have hr₂ : Continuous fun p : (ℝ × ℝ) × ℝ => ((p.1.1, p.1.2, p.2) : ℝ × ℝ × ℝ) := by fun_prop
  have h4 : Continuous fun a : ℝ × ℝ × ℝ × ℝ => G (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) :=
    hG.comp continuous_unitaryElt
  have hI : Continuous fun a : ℝ × ℝ × ℝ × ℝ =>
      Real.sin a.2.1 * Real.cos a.2.1 * G (unitaryElt a.1 a.2.1 a.2.2.1 a.2.2.2) := hwr.mul h4
  have hU := hI.comp hr₃
  have hJ : Continuous fun b : ℝ × ℝ × ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.sin b.2.1 * Real.cos b.2.1 * G (unitaryElt b.1 b.2.1 b.2.2 ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (b : ℝ × ℝ × ℝ) (ξ₂ : ℝ) =>
      Real.sin b.2.1 * Real.cos b.2.1 * G (unitaryElt b.1 b.2.1 b.2.2 ξ₂)) hU _ _
  have hV := hJ.comp hr₂
  have hK : Continuous fun c : ℝ × ℝ => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.sin c.2 * Real.cos c.2 * G (unitaryElt c.1 c.2 ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (c : ℝ × ℝ) (ξ₁ : ℝ) =>
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin c.2 * Real.cos c.2 * G (unitaryElt c.1 c.2 ξ₁ ξ₂)) hV _ _
  have hL : Continuous fun ψ : ℝ => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (ψ η : ℝ) =>
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂)) hK _ _
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπ2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hw : ∀ η : ℝ, η ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → 0 ≤ Real.sin η * Real.cos η := fun η hηI =>
    mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hηI.1 (by linarith [hηI.2, Real.pi_pos]))
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hηI.1, Real.pi_pos], hηI.2⟩)
  have n₄ : ∀ ψ η : ℝ, η ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → ∀ ξ₁ ξ₂ : ℝ,
      0 ≤ Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) :=
    fun ψ η hηI ξ₁ ξ₂ => mul_nonneg (hw η hηI) (h0 _ (isIsometry_unitaryElt ψ η ξ₁ ξ₂))
  have n₃ : ∀ ψ η : ℝ, η ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → ∀ ξ₁ : ℝ,
      0 ≤ ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) :=
    fun ψ η hηI ξ₁ => intervalIntegral.integral_nonneg h2π.le fun ξ₂ _ => n₄ ψ η hηI ξ₁ ξ₂
  have n₂ : ∀ ψ η : ℝ, η ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      0 ≤ ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) :=
    fun ψ η hηI => intervalIntegral.integral_nonneg h2π.le fun ξ₁ _ => n₃ ψ η hηI ξ₁
  have n₁ : ∀ ψ : ℝ, 0 ≤ ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) :=
    fun ψ => intervalIntegral.integral_nonneg hπ2.le fun η hηI => n₂ ψ η hηI
  have hη₀ : η₀ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hη.1.le, hη.2.le⟩
  have p₄ : 0 < Real.sin η₀ * Real.cos η₀ * G (unitaryElt ψ₀ η₀ ξ₁₀ ξ₂₀) :=
    mul_pos (mul_pos (Real.sin_pos_of_pos_of_lt_pi hη.1 (by linarith [hη.2, Real.pi_pos]))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hη.1, Real.pi_pos], hη.2⟩)) hpos
  have p₃ : 0 < ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η₀ * Real.cos η₀ * G (unitaryElt ψ₀ η₀ ξ₁₀ ξ₂) := by
    have ht : Continuous fun ξ₂ : ℝ => ((ψ₀, η₀, ξ₁₀, ξ₂) : ℝ × ℝ × ℝ × ℝ) := by fun_prop
    have hc := hI.comp ht
    have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (f := fun _ => (0 : ℝ)) h2π
      continuousOn_const hc.continuousOn (fun ξ₂ _ => n₄ ψ₀ η₀ hη₀ ξ₁₀ ξ₂)
      ⟨ξ₂₀, ⟨hξ₂.1.le, hξ₂.2.le⟩, p₄⟩
    simpa using this
  have p₂ : 0 < ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.sin η₀ * Real.cos η₀ * G (unitaryElt ψ₀ η₀ ξ₁ ξ₂) := by
    have ht : Continuous fun ξ₁ : ℝ => ((ψ₀, η₀, ξ₁) : ℝ × ℝ × ℝ) := by fun_prop
    have hc := hJ.comp ht
    have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (f := fun _ => (0 : ℝ)) h2π
      continuousOn_const hc.continuousOn (fun ξ₁ _ => n₃ ψ₀ η₀ hη₀ ξ₁)
      ⟨ξ₁₀, ⟨hξ₁.1.le, hξ₁.2.le⟩, p₃⟩
    simpa using this
  have p₁ : 0 < ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.sin η * Real.cos η * G (unitaryElt ψ₀ η ξ₁ ξ₂) := by
    have ht : Continuous fun η : ℝ => ((ψ₀, η) : ℝ × ℝ) := by fun_prop
    have hc := hK.comp ht
    have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (f := fun _ => (0 : ℝ)) hπ2
      continuousOn_const hc.continuousOn (fun η hηI => n₂ ψ₀ η ⟨hηI.1.le, hηI.2⟩) ⟨η₀, hη₀, p₂⟩
    simpa using this
  have p₀ : 0 < ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), Real.sin η * Real.cos η * G (unitaryElt ψ η ξ₁ ξ₂) := by
    have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (f := fun _ => (0 : ℝ)) h2π
      continuousOn_const hL.continuousOn (fun ψ _ => n₁ ψ) ⟨ψ₀, ⟨hψ.1.le, hψ.2.le⟩, p₁⟩
    simpa using this
  exact mul_pos (by positivity) p₀

private def traceWeight : MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ :=
  MvPolynomial.C (8 : ℂ)⁻¹ *
    (MvPolynomial.C 4 + (MvPolynomial.X (Sum.inl (0, 0)) + MvPolynomial.X (Sum.inl (1, 1))) +
      (MvPolynomial.X (Sum.inr (0, 0)) + MvPolynomial.X (Sum.inr (1, 1))))

private def weightValue (h : GL (Fin 2) ℂ) : ℝ :=
  (2 + (Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ)).re) / 4

private theorem continuous_weightValue : Continuous weightValue := by
  unfold weightValue
  exact (continuous_const.add (Complex.continuous_re.comp Units.continuous_val.matrix_trace)).div_const 4

private theorem eval_traceWeight_of_isIsometry (h : GL (Fin 2) ℂ) (hh : IsIsometry h) :
    MvPolynomial.eval (weightPoint h) traceWeight = (weightValue h : ℂ) := by
  have hinv : ((h⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = star (h : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.inv_eq_left_inv hh
  have htr : ∀ i : Fin 2, ((h⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i i =
      (starRingEnd ℂ) ((h : Matrix (Fin 2) (Fin 2) ℂ) i i) := fun i => by
    rw [hinv, Matrix.star_apply, Complex.star_def]
  simp only [traceWeight, weightPoint, entries, map_mul, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Sum.elim_inl, Sum.elim_inr, htr]
  rw [weightValue, Matrix.trace_fin_two]
  simp only [Complex.add_re]
  have key := Complex.add_conj ((h : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (h : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
  simp only [map_add, Complex.add_re] at key
  push_cast at key ⊢
  linear_combination (1 / 8 : ℂ) * key

private theorem weightValue_nonneg (h : GL (Fin 2) ℂ) (hh : IsIsometry h) : 0 ≤ weightValue h := by
  have hdiag : ∀ j : Fin 2, |((h : Matrix (Fin 2) (Fin 2) ℂ) j j).re| ≤ 1 := by
    intro j
    have h1 := congrFun (congrFun hh j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self] at h1
    have h2 : ∑ i : Fin 2, Complex.normSq ((h : Matrix (Fin 2) (Fin 2) ℂ) i j) = 1 := by exact_mod_cast h1
    have h3 : Complex.normSq ((h : Matrix (Fin 2) (Fin 2) ℂ) j j) ≤ 1 := by
      have h5 := Finset.single_le_sum (f := fun i => Complex.normSq ((h : Matrix (Fin 2) (Fin 2) ℂ) i j))
        (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      rw [h2] at h5
      exact h5
    rw [Complex.normSq_eq_norm_sq] at h3
    have h4 : ‖(h : Matrix (Fin 2) (Fin 2) ℂ) j j‖ ≤ 1 := by
      nlinarith [norm_nonneg ((h : Matrix (Fin 2) (Fin 2) ℂ) j j)]
    exact (Complex.abs_re_le_norm _).trans h4
  have h0 := abs_le.1 (hdiag 0)
  have h1 := abs_le.1 (hdiag 1)
  unfold weightValue
  rw [Matrix.trace_fin_two, Complex.add_re]
  linarith [h0.1, h1.1]

private theorem weightValue_le_one (h : GL (Fin 2) ℂ) (hh : IsIsometry h) : weightValue h ≤ 1 := by
  have hdiag : ∀ j : Fin 2, |((h : Matrix (Fin 2) (Fin 2) ℂ) j j).re| ≤ 1 := by
    intro j
    have h1 := congrFun (congrFun hh j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self] at h1
    have h2 : ∑ i : Fin 2, Complex.normSq ((h : Matrix (Fin 2) (Fin 2) ℂ) i j) = 1 := by exact_mod_cast h1
    have h3 : Complex.normSq ((h : Matrix (Fin 2) (Fin 2) ℂ) j j) ≤ 1 := by
      have h5 := Finset.single_le_sum (f := fun i => Complex.normSq ((h : Matrix (Fin 2) (Fin 2) ℂ) i j))
        (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      rw [h2] at h5
      exact h5
    rw [Complex.normSq_eq_norm_sq] at h3
    have h4 : ‖(h : Matrix (Fin 2) (Fin 2) ℂ) j j‖ ≤ 1 := by
      nlinarith [norm_nonneg ((h : Matrix (Fin 2) (Fin 2) ℂ) j j)]
    exact (Complex.abs_re_le_norm _).trans h4
  have h0 := abs_le.1 (hdiag 0)
  have h1 := abs_le.1 (hdiag 1)
  unfold weightValue
  rw [Matrix.trace_fin_two, Complex.add_re]
  linarith [h0.2, h1.2]

private theorem sum_norm_sub_one_sq_eq (h : GL (Fin 2) ℂ) (hh : IsIsometry h) :
    ∑ i : Fin 2, ∑ j : Fin 2, ‖(h : Matrix (Fin 2) (Fin 2) ℂ) i j - (1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2 =
      8 * (1 - weightValue h) := by
  have hcol : ∀ j : Fin 2, ∑ i : Fin 2, Complex.normSq ((h : Matrix (Fin 2) (Fin 2) ℂ) i j) = 1 := by
    intro j
    have h1 := congrFun (congrFun hh j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self] at h1
    exact_mod_cast h1
  have h0 := hcol 0
  have h1 := hcol 1
  simp only [Fin.sum_univ_two] at h0 h1 ⊢
  simp only [← Complex.normSq_eq_norm_sq, Matrix.one_apply, Fin.isValue, if_true, zero_ne_one,
    one_ne_zero, if_false, sub_zero, Complex.normSq_sub, map_one, mul_one]
  unfold weightValue
  rw [Matrix.trace_fin_two, Complex.add_re]
  linarith

private theorem weightValue_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    weightValue (unitaryElt ψ η ξ₁ ξ₂) = (1 + Real.cos η * Real.cos ξ₁ * Real.cos ψ) / 2 := by
  have hU : ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
        Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
      Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
        Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))] := rfl
  have e1 : Complex.exp (-(ξ₁ * Complex.I)) = Complex.exp (((-ξ₁ : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  unfold weightValue
  rw [hU, Matrix.trace_fin_two_of, e1]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, Real.cos_neg, Real.sin_neg]
  ring

private theorem exists_pos_le_realAverage_weightValue_pow (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ m : ℝ, 0 < m ∧ ∀ n : ℕ, (1 - δ) ^ n * m ≤ realAverage (fun h => weightValue h ^ n) := by
  set b : GL (Fin 2) ℂ → ℝ := fun u => max 0 (weightValue u - (1 - δ)) / δ with hb
  have hbc : Continuous b := (continuous_const.max (continuous_weightValue.sub continuous_const)).div_const δ
  have hb0 : ∀ u : GL (Fin 2) ℂ, 0 ≤ b u := fun u => div_nonneg (le_max_left _ _) hδ.le
  set θ : ℝ := min (1 / 2) δ with hθ
  have hθ0 : 0 < θ := lt_min (by norm_num) hδ
  have hθh : θ ≤ 1 / 2 := min_le_left _ _
  have hθδ : θ ≤ δ := min_le_right _ _
  have hcos : 1 - θ ^ 2 / 2 ≤ Real.cos θ := Real.one_sub_sq_div_two_le_cos
  have hcube : (1 - θ ^ 2 / 2) ^ 3 ≤ Real.cos θ ^ 3 := pow_le_pow_left₀ (by nlinarith) hcos 3
  have hw : 1 - δ < weightValue (unitaryElt θ θ θ θ) := by
    rw [weightValue_unitaryElt]
    have hθsq : θ ^ 2 ≤ δ / 2 := by nlinarith
    have hbern : 1 - 3 * (θ ^ 2 / 2) ≤ (1 - θ ^ 2 / 2) ^ 3 := by
      nlinarith [sq_nonneg (θ ^ 2 / 2), hθsq, hδ1]
    nlinarith [hcube, hθsq, hθ0, hbern]
  have hθπ : θ < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hθ2π : θ < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hbpos : 0 < b (unitaryElt θ θ θ θ) := by
    simp only [hb]
    exact div_pos (lt_max_of_lt_right (by linarith)) hδ
  have hm : 0 < realAverage b :=
    realAverage_pos b hbc (fun u _ => hb0 u) θ θ θ θ ⟨hθ0, hθ2π⟩ ⟨hθ0, hθπ⟩ ⟨hθ0, hθ2π⟩ ⟨hθ0, hθ2π⟩ hbpos
  refine ⟨realAverage b, hm, fun n => ?_⟩
  have hpt : ∀ u : GL (Fin 2) ℂ, IsIsometry u → (1 - δ) ^ n * b u ≤ weightValue u ^ n := by
    intro u hu
    have hw0 := weightValue_nonneg u hu
    have hw1 := weightValue_le_one u hu
    by_cases hcase : weightValue u ≤ 1 - δ
    · have hbz : b u = 0 := by
        simp only [hb]
        rw [max_eq_left (by linarith), zero_div]
      rw [hbz, mul_zero]
      exact pow_nonneg hw0 n
    · have hcase' := not_le.1 hcase
      have hb1 : b u ≤ 1 := by
        simp only [hb]
        rw [div_le_one hδ, max_le_iff]
        exact ⟨hδ.le, by linarith [hcase']⟩
      calc (1 - δ) ^ n * b u ≤ (1 - δ) ^ n * 1 :=
            mul_le_mul_of_nonneg_left hb1 (pow_nonneg (by linarith) n)
        _ = (1 - δ) ^ n := mul_one _
        _ ≤ weightValue u ^ n := pow_le_pow_left₀ (by linarith) hcase'.le n
  rw [← realAverage_const_mul]
  exact realAverage_mono _ _ (continuous_const.mul hbc) (continuous_weightValue.pow n) hpt

private theorem realAverage_weightValue_pow_pos (n : ℕ) : 0 < realAverage (fun h => weightValue h ^ n) := by
  obtain ⟨m, hm, hle⟩ := exists_pos_le_realAverage_weightValue_pow (1 / 2) (by norm_num) (by norm_num)
  exact lt_of_lt_of_le (mul_pos (pow_pos (by norm_num) n) hm) (hle n)

private def normalizedWeights (n : ℕ) : MvPolynomial (Fin 2 × Fin 2 ⊕ Fin 2 × Fin 2) ℂ :=
  MvPolynomial.C ((realAverage (fun h => weightValue h ^ n) : ℝ) : ℂ)⁻¹ * traceWeight ^ n

private theorem eval_normalizedWeights_of_isIsometry (n : ℕ) (h : GL (Fin 2) ℂ) (hh : IsIsometry h) :
    MvPolynomial.eval (weightPoint h) (normalizedWeights n) =
      ((realAverage (fun h => weightValue h ^ n))⁻¹ * weightValue h ^ n : ℝ) := by
  simp only [normalizedWeights, map_mul, map_pow, MvPolynomial.eval_C, eval_traceWeight_of_isIsometry h hh]
  push_cast
  ring

private theorem tendsto_unitaryAverage_normalizedWeights_mul (Ψ : GL (Fin 2) ℂ → ℂ) (hΨ : Continuous Ψ) :
    Filter.Tendsto (fun n => unitaryAverage fun h => MvPolynomial.eval (weightPoint h) (normalizedWeights n) * Ψ h)
      Filter.atTop (nhds (Ψ 1)) := by
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, ∀ n, A n = realAverage (fun h => weightValue h ^ n) := ⟨_, fun _ => rfl⟩
  have hApos : ∀ n, 0 < A n := fun n => by rw [hA]; exact realAverage_weightValue_pow_pos n
  obtain ⟨D, hD⟩ : ∃ D : GL (Fin 2) ℂ → ℝ, ∀ u, D u = ‖Ψ u - Ψ 1‖ := ⟨_, fun _ => rfl⟩
  have hDc : Continuous D := by
    have hDf : D = fun u => ‖Ψ u - Ψ 1‖ := funext hD
    rw [hDf]
    exact (hΨ.sub continuous_const).norm
  have hD0 : ∀ u, 0 ≤ D u := fun u => by rw [hD]; exact norm_nonneg _
  have hwc : ∀ n, Continuous fun h : GL (Fin 2) ℂ => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) := fun n =>
    Complex.continuous_ofReal.comp (continuous_const.mul (continuous_weightValue.pow n))
  have hE : ∀ n, unitaryAverage (fun h => MvPolynomial.eval (weightPoint h) (normalizedWeights n) * Ψ h) =
      Ψ 1 + unitaryAverage (fun h => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * (Ψ h - Ψ 1)) := by
    intro n
    have h1 : unitaryAverage (fun h => MvPolynomial.eval (weightPoint h) (normalizedWeights n) * Ψ h) =
        unitaryAverage (fun h => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * Ψ h) :=
      unitaryAverage_congr_of_isIsometry _ _ fun u hu => by
        rw [eval_normalizedWeights_of_isIsometry n u hu, hA]
    have h2 : (fun h => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * Ψ h) = fun h =>
        (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * Ψ 1 + (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * (Ψ h - Ψ 1) := by
      funext h
      ring
    have h3 : unitaryAverage (fun h => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * Ψ 1) = Ψ 1 := by
      have h4 : (fun h : GL (Fin 2) ℂ => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * Ψ 1) =
          fun h => Ψ 1 * (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) := by
        funext h
        ring
      rw [h4, unitaryAverage_const_mul', unitaryAverage_ofReal (fun h => (A n)⁻¹ * weightValue h ^ n),
        realAverage_const_mul (A n)⁻¹ (fun h => weightValue h ^ n), ← hA, inv_mul_cancel₀ (hApos n).ne',
        Complex.ofReal_one, mul_one]
    rw [h1, h2, unitaryAverage_add (fun h => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * Ψ 1)
      (fun h => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * (Ψ h - Ψ 1)) ((hwc n).mul continuous_const)
      ((hwc n).mul (hΨ.sub continuous_const)), h3]
  have hadd : ∀ G₁ G₂ : GL (Fin 2) ℂ → ℝ, Continuous G₁ → Continuous G₂ →
      realAverage (fun u => G₁ u + G₂ u) = realAverage G₁ + realAverage G₂ := by
    intro G₁ G₂ h₁ h₂
    apply Complex.ofReal_injective
    rw [Complex.ofReal_add, ← unitaryAverage_ofReal, ← unitaryAverage_ofReal, ← unitaryAverage_ofReal,
      ← unitaryAverage_add (fun h => ((G₁ h : ℝ) : ℂ)) (fun h => ((G₂ h : ℝ) : ℂ)) (Complex.continuous_ofReal.comp h₁)
        (Complex.continuous_ofReal.comp h₂)]
    simp only [Complex.ofReal_add]
  have hR0 : 0 ≤ realAverage D := by
    have h := realAverage_mono (fun _ => (0 : ℝ)) D continuous_const hDc fun u _ => hD0 u
    rwa [realAverage_const] at h
  have hnear : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ u : GL (Fin 2) ℂ, IsIsometry u → 1 - δ < weightValue u → D u < ε := by
    intro ε hε
    have hD1 : D 1 = 0 := by rw [hD, sub_self, norm_zero]
    have hIio : Set.Iio ε ∈ nhds (D 1) := by rw [hD1]; exact Iio_mem_nhds hε
    have hN : D ⁻¹' Set.Iio ε ∈ nhds (1 : GL (Fin 2) ℂ) := hDc.continuousAt.preimage_mem_nhds hIio
    rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hN
    obtain ⟨W, hW, hWN⟩ := hN
    have hc : Continuous fun m : Matrix (Fin 2) (Fin 2) ℂ => (m, MulOpposite.op (star m)) :=
      continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_star)
    have hV : (fun m : Matrix (Fin 2) (Fin 2) ℂ => (m, MulOpposite.op (star m))) ⁻¹' W ∈
        nhds (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      have h1 : Units.embedProduct (Matrix (Fin 2) (Fin 2) ℂ) 1 =
          ((1 : Matrix (Fin 2) (Fin 2) ℂ), MulOpposite.op (star (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
        rw [Units.embedProduct_apply, inv_one, Units.val_one, star_one]
      rw [h1] at hW
      exact hW
    obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1
      (show (fun m : Matrix (Fin 2) (Fin 2) ℂ => (m, MulOpposite.op (star m))) ⁻¹' W ∈
        nhds (show Fin 2 → Fin 2 → ℂ from (1 : Matrix (Fin 2) (Fin 2) ℂ)) from hV)
    refine ⟨min (r ^ 2 / 8) (1 / 2), by positivity, lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
    intro u hu hwu
    have hsum := sum_norm_sub_one_sq_eq u hu
    have hlt : 8 * (1 - weightValue u) < r ^ 2 := by
      have h8 : 1 - weightValue u < min (r ^ 2 / 8) (1 / 2) := by linarith
      have h9 := lt_of_lt_of_le h8 (min_le_left _ _)
      linarith
    have hent : ∀ i j : Fin 2,
        ‖(u : Matrix (Fin 2) (Fin 2) ℂ) i j - (1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ < r := by
      intro i j
      have hij : ‖(u : Matrix (Fin 2) (Fin 2) ℂ) i j - (1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2 ≤
          ∑ i : Fin 2, ∑ j : Fin 2,
            ‖(u : Matrix (Fin 2) (Fin 2) ℂ) i j - (1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2 := by
        refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j : Fin 2,
          ‖(u : Matrix (Fin 2) (Fin 2) ℂ) i j - (1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2)
          (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ i))
        exact Finset.single_le_sum (f := fun j =>
          ‖(u : Matrix (Fin 2) (Fin 2) ℂ) i j - (1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ j)
      rw [hsum] at hij
      exact lt_of_le_of_lt (le_abs_self _) (abs_lt_of_sq_lt_sq (lt_of_le_of_lt hij hlt) hr.le)
    have hmem : (show Fin 2 → Fin 2 → ℂ from (u : Matrix (Fin 2) (Fin 2) ℂ)) ∈
        Metric.ball (show Fin 2 → Fin 2 → ℂ from (1 : Matrix (Fin 2) (Fin 2) ℂ)) r := by
      rw [Metric.mem_ball, dist_pi_lt_iff hr]
      intro i
      rw [dist_pi_lt_iff hr]
      intro j
      rw [Complex.dist_eq]
      exact hent i j
    have hinv : ((u⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = star (u : Matrix (Fin 2) (Fin 2) ℂ) :=
      Units.inv_eq_of_mul_eq_one_left hu
    have huW : Units.embedProduct (Matrix (Fin 2) (Fin 2) ℂ) u ∈ W := by
      have h := hrV hmem
      rw [Units.embedProduct_apply, hinv]
      exact h
    exact hWN huW
  have hfun : (fun n => unitaryAverage fun h => MvPolynomial.eval (weightPoint h) (normalizedWeights n) * Ψ h) =
      fun n => Ψ 1 + unitaryAverage (fun h => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * (Ψ h - Ψ 1)) := funext hE
  rw [hfun]
  have hlim : Filter.Tendsto
      (fun n => unitaryAverage (fun h => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * (Ψ h - Ψ 1)))
      Filter.atTop (nhds 0) := by
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨δ, hδ0, hδ1, hδ⟩ := hnear (ε / 2) (by positivity)
    obtain ⟨m, hm, hmA⟩ := exists_pos_le_realAverage_weightValue_pow (δ / 2) (by positivity) (by linarith)
    have hρ0 : 0 ≤ (1 - δ) / (1 - δ / 2) := div_nonneg (by linarith) (by linarith)
    have hρ1 : (1 - δ) / (1 - δ / 2) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    have htail : Filter.Tendsto (fun n : ℕ => ((1 - δ) / (1 - δ / 2)) ^ n / m * realAverage D) Filter.atTop
        (nhds (0 / m * realAverage D)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).div_const m).mul_const _
    have hev := htail.eventually (gt_mem_nhds (show 0 / m * realAverage D < ε / 2 by simp; positivity))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_zero_right]
    have h1 := norm_unitaryAverage_le_realAverage (fun h => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * (Ψ h - Ψ 1))
      (fun u => (A n)⁻¹ * (weightValue u ^ n * D u)) ((hwc n).mul (hΨ.sub continuous_const))
      (continuous_const.mul ((continuous_weightValue.pow n).mul hDc)) fun u hu => by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hD]
        exact le_of_eq (by
          rw [abs_of_nonneg (inv_nonneg.2 (hApos n).le), abs_of_nonneg (pow_nonneg (weightValue_nonneg u hu) n),
            mul_assoc])
    have h2 := realAverage_mono (fun u => weightValue u ^ n * D u)
      (fun u => ε / 2 * weightValue u ^ n + (1 - δ) ^ n * D u) ((continuous_weightValue.pow n).mul hDc)
      ((continuous_const.mul (continuous_weightValue.pow n)).add (continuous_const.mul hDc)) fun u hu => by
        have hw0 : 0 ≤ weightValue u := weightValue_nonneg u hu
        have hwn : 0 ≤ weightValue u ^ n := pow_nonneg hw0 n
        have hδn : 0 ≤ (1 - δ) ^ n := pow_nonneg (by linarith) n
        by_cases hcase : 1 - δ < weightValue u
        · have hp := mul_le_mul_of_nonneg_left (hδ u hu hcase).le hwn
          have hq := mul_nonneg hδn (hD0 u)
          linarith
        · have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw0 (not_lt.1 hcase) n) (hD0 u)
          have hq := mul_nonneg (by positivity : (0 : ℝ) ≤ ε / 2) hwn
          linarith
    rw [hadd (fun u => ε / 2 * weightValue u ^ n) (fun u => (1 - δ) ^ n * D u)
      (continuous_const.mul (continuous_weightValue.pow n)) (continuous_const.mul hDc),
      realAverage_const_mul, realAverage_const_mul, ← hA] at h2
    rw [realAverage_const_mul] at h1
    have hAn : (1 - δ / 2) ^ n * m ≤ A n := by rw [hA]; exact hmA n
    have hratio : (1 - δ) ^ n / A n ≤ ((1 - δ) / (1 - δ / 2)) ^ n / m := by
      rw [div_pow, div_div]
      exact div_le_div_of_nonneg_left (pow_nonneg (by linarith) n) (mul_pos (pow_pos (by linarith) n) hm) hAn
    have h3 : (A n)⁻¹ * (ε / 2 * A n + (1 - δ) ^ n * realAverage D) =
        ε / 2 + (1 - δ) ^ n / A n * realAverage D := by
      have hinv : (A n)⁻¹ * A n = 1 := inv_mul_cancel₀ (hApos n).ne'
      linear_combination (ε / 2) * hinv
    calc ‖unitaryAverage (fun h => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * (Ψ h - Ψ 1))‖
        ≤ (A n)⁻¹ * realAverage (fun u => weightValue u ^ n * D u) := h1
      _ ≤ (A n)⁻¹ * (ε / 2 * A n + (1 - δ) ^ n * realAverage D) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 (hApos n).le)
      _ = ε / 2 + (1 - δ) ^ n / A n * realAverage D := h3
      _ ≤ ε / 2 + ((1 - δ) / (1 - δ / 2)) ^ n / m * realAverage D := by
          gcongr
      _ < ε / 2 + ε / 2 := by linarith [hN n hn]
      _ = ε := by ring
  have h : Filter.Tendsto
      (fun n => Ψ 1 + unitaryAverage (fun h => (((A n)⁻¹ * weightValue h ^ n : ℝ) : ℂ) * (Ψ h - Ψ 1)))
      Filter.atTop (nhds (Ψ 1 + 0)) :=
    tendsto_const_nhds.add hlim
  rwa [add_zero] at h

private theorem isAveragingDevice_unitaryAverage : IsAveragingDevice unitaryAverage normalizedWeights := by
  refine ⟨fun F G hF hG => unitaryAverage_add F G hF hG, fun c F _ => unitaryAverage_const_mul' c F,
    fun F hF u hu => ?_, fun F G _ _ h => unitaryAverage_congr_of_isIsometry F G h,
    fun Ψ hΨ => tendsto_unitaryAverage_normalizedWeights_mul Ψ hΨ⟩
  have h := unitaryAverage_translate F hF u 1 hu (by simp)
  simpa only [mul_one] using h

private def preparedInput (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) : (Fin 2 → Fin 2 → ℂ) × P → ℂ :=
  fun q => (1 / (2 * Real.pi) : ℂ) *
    ∫ ψ in (0 : ℝ)..(2 * Real.pi), Φ (fun i j => Complex.exp (-(2 * ψ * Complex.I)) * q.1 i j, q.2)

private theorem isScalarInvariant_preparedInput (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ) :
    IsScalarInvariant (preparedInput Φ) := by
  have _ := hΦ
  unfold IsScalarInvariant
  intro z hz q
  obtain ⟨α, rfl⟩ := (Complex.norm_eq_one_iff z).1 hz
  simp only [preparedInput]
  congr 1
  have hper : Function.Periodic
      (fun ψ : ℝ => Φ (fun i j => Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) * q.1 i j, q.2)) (2 * Real.pi) := by
    intro ψ
    have h : Complex.exp (-(2 * ((ψ + 2 * Real.pi : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) := by
      rw [show -(2 * ((ψ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
            -(2 * (ψ : ℂ) * Complex.I) + ((-2 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
          push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simp only [h]
  have hshift : ∀ ψ : ℝ,
      Φ (fun i j => Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) * (Complex.exp ((α : ℂ) * Complex.I) * q.1 i j), q.2) =
        Φ (fun i j => Complex.exp (-(2 * ((ψ - α / 2 : ℝ) : ℂ) * Complex.I)) * q.1 i j, q.2) := by
    intro ψ
    congr 2
    funext i j
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  calc (∫ ψ in (0 : ℝ)..(2 * Real.pi),
          Φ (fun i j => Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) * (Complex.exp ((α : ℂ) * Complex.I) * q.1 i j), q.2))
      = ∫ ψ in (0 : ℝ)..(2 * Real.pi),
          Φ (fun i j => Complex.exp (-(2 * ((ψ - α / 2 : ℝ) : ℂ) * Complex.I)) * q.1 i j, q.2) :=
        intervalIntegral.integral_congr fun ψ _ => hshift ψ
    _ = ∫ ψ in (0 - α / 2)..(2 * Real.pi - α / 2),
          Φ (fun i j => Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) * q.1 i j, q.2) :=
        intervalIntegral.integral_comp_sub_right
          (fun ψ : ℝ => Φ (fun i j => Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) * q.1 i j, q.2)) (α / 2)
    _ = ∫ ψ in (0 : ℝ)..(2 * Real.pi), Φ (fun i j => Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) * q.1 i j, q.2) := by
        have h := hper.intervalIntegral_add_eq (0 - α / 2) 0
        rw [zero_add] at h
        rw [← h]
        congr 1
        ring

private theorem continuous_preparedInput (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ) :
    Continuous (preparedInput Φ) := by
  show Continuous fun q : (Fin 2 → Fin 2 → ℂ) × P => (1 / (2 * Real.pi) : ℂ) *
    ∫ ψ in (0 : ℝ)..(2 * Real.pi), Φ (fun i j => Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) * q.1 i j, q.2)
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : (Fin 2 → Fin 2 → ℂ) × P) (ψ : ℝ) =>
      Φ (fun i j => Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) * x.1 i j, x.2)) ?_ 0 (2 * Real.pi)
  have hg : Continuous fun p : ((Fin 2 → Fin 2 → ℂ) × P) × ℝ =>
      ((fun i j => Complex.exp (-(2 * (p.2 : ℂ) * Complex.I)) * p.1.1 i j, p.1.2) : (Fin 2 → Fin 2 → ℂ) × P) := by
    fun_prop
  exact hΦ.comp hg

private theorem finiteDimensional_translateSpan_preparedInput (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ)
    [FiniteDimensional ℂ (translateSpan Φ)] : FiniteDimensional ℂ (translateSpan (preparedInput Φ)) := by
  have hψ : ∀ q : (Fin 2 → Fin 2 → ℂ) × P, Continuous fun ψ : ℝ =>
      ((fun i j => Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) * q.1 i j, q.2) : (Fin 2 → Fin 2 → ℂ) × P) :=
    fun q => by fun_prop
  have hgen : ∀ k : rowIsometrySubgroup₀ ℂ, Continuous (rightTranslate Φ k) := fun k =>
    hΦ.comp ((continuous_fst.matrix_mul continuous_const).prodMk continuous_snd)
  have hmem : ∀ f : translateSpan Φ, Continuous (f : (Fin 2 → Fin 2 → ℂ) × P → ℂ) := by
    rintro ⟨f, hf⟩
    have hf' : f ∈ Submodule.span ℂ (Set.range (rightTranslate Φ)) := hf
    refine Submodule.span_induction (p := fun f _ => Continuous f) ?_ continuous_zero ?_ ?_ hf'
    · rintro _ ⟨k, rfl⟩
      exact hgen k
    · intro f g _ _ hf hg
      exact hf.add hg
    · intro c f _ hf
      exact hf.const_smul c
  have hint : ∀ f : translateSpan Φ, ∀ q : (Fin 2 → Fin 2 → ℂ) × P,
      IntervalIntegrable (fun ψ : ℝ => (f : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
        (fun i j => Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) * q.1 i j, q.2)) MeasureTheory.volume 0 (2 * Real.pi) :=
    fun f q => ((hmem f).comp (hψ q)).intervalIntegrable 0 (2 * Real.pi)
  let L : translateSpan Φ →ₗ[ℂ] ((Fin 2 → Fin 2 → ℂ) × P → ℂ) :=
    { toFun := fun f => preparedInput (f : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
      map_add' := by
        intro f g
        funext q
        simp only [preparedInput, Submodule.coe_add, Pi.add_apply]
        rw [intervalIntegral.integral_add (hint f q) (hint g q), mul_add]
      map_smul' := by
        intro c f
        funext q
        simp only [preparedInput, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [show (∫ ψ in (0 : ℝ)..(2 * Real.pi), c * (f : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
              (fun i j => Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) * q.1 i j, q.2)) =
            c * ∫ ψ in (0 : ℝ)..(2 * Real.pi), (f : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
              (fun i j => Complex.exp (-(2 * (ψ : ℂ) * Complex.I)) * q.1 i j, q.2) from
          intervalIntegral.integral_const_mul c _]
        ring }
  have hcomm : ∀ k : rowIsometrySubgroup₀ ℂ,
      preparedInput (rightTranslate Φ k) = rightTranslate (preparedInput Φ) k := by
    intro k
    funext q
    simp only [preparedInput, rightTranslate]
    congr 1
    refine intervalIntegral.integral_congr fun ψ _ => ?_
    congr 2
    funext i j
    simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]
  have hle : translateSpan (preparedInput Φ) ≤ LinearMap.range L := by
    show Submodule.span ℂ (Set.range (rightTranslate (preparedInput Φ))) ≤ LinearMap.range L
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨rightTranslate Φ k, Submodule.subset_span ⟨k, rfl⟩⟩, hcomm k⟩
  exact Submodule.finiteDimensional_of_le hle

private theorem unitaryAverage_intervalIntegral (a b : ℝ) (H : ℝ → GL (Fin 2) ℂ → ℂ)
    (hH : Continuous fun q : ℝ × GL (Fin 2) ℂ => H q.1 q.2) :
    unitaryAverage (fun k => ∫ t in a..b, H t k) = ∫ t in a..b, unitaryAverage (H t) := by
  have swap : ∀ {c d : ℝ}, c ≤ d → ∀ G : ℝ → ℝ → ℂ, Continuous (fun q : ℝ × ℝ => G q.1 q.2) →
      ∫ x in c..d, ∫ t in a..b, G x t = ∫ t in a..b, ∫ x in c..d, G x t := by
    intro c d hcd G hG
    simp only [intervalIntegral.integral_of_le hcd]
    have hint : MeasureTheory.Integrable (Function.uncurry fun t x => G x t)
        ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod (MeasureTheory.volume.restrict (Set.Ioc c d))) := by
      rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
      have hK : IsCompact (Set.uIcc a b ×ˢ Set.Icc c d) :=
        IsCompact.prod (isCompact_uIcc : IsCompact (Set.uIcc a b)) (isCompact_Icc : IsCompact (Set.Icc c d))
      have hsub : Set.uIoc a b ×ˢ Set.Ioc c d ⊆ Set.uIcc a b ×ˢ Set.Icc c d :=
        Set.prod_mono Set.uIoc_subset_uIcc Set.Ioc_subset_Icc_self
      exact ((hG.comp continuous_swap).continuousOn.integrableOn_compact hK).mono_set hsub
    exact (MeasureTheory.intervalIntegral_integral_swap hint).symm
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hπ2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have C4 : Continuous fun v : ℝ × ℝ × ℝ × ℝ × ℝ =>
      (Real.sin v.2.1 * Real.cos v.2.1 : ℂ) * H v.2.2.2.2 (unitaryElt v.1 v.2.1 v.2.2.1 v.2.2.2.1) := by
    have hu : Continuous fun v : ℝ × ℝ × ℝ × ℝ × ℝ => unitaryElt v.1 v.2.1 v.2.2.1 v.2.2.2.1 :=
      continuous_unitaryElt.comp (f := fun v : ℝ × ℝ × ℝ × ℝ × ℝ => (v.1, v.2.1, v.2.2.1, v.2.2.2.1)) (by fun_prop)
    have hpair : Continuous fun v : ℝ × ℝ × ℝ × ℝ × ℝ => (v.2.2.2.2, unitaryElt v.1 v.2.1 v.2.2.1 v.2.2.2.1) :=
      Continuous.prodMk (by fun_prop) hu
    exact Continuous.mul (by fun_prop)
      (hH.comp (f := fun v : ℝ × ℝ × ℝ × ℝ × ℝ => (v.2.2.2.2, unitaryElt v.1 v.2.1 v.2.2.1 v.2.2.2.1)) hpair)
  have C3 : Continuous fun v : ℝ × ℝ × ℝ × ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin v.2.1 * Real.cos v.2.1 : ℂ) * H v.2.2.2 (unitaryElt v.1 v.2.1 v.2.2.1 ξ₂) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
    exact C4.comp (f := fun p : (ℝ × ℝ × ℝ × ℝ) × ℝ => (p.1.1, p.1.2.1, p.1.2.2.1, p.2, p.1.2.2.2)) (by fun_prop)
  have C2 : Continuous fun v : ℝ × ℝ × ℝ => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin v.2.1 * Real.cos v.2.1 : ℂ) * H v.2.2 (unitaryElt v.1 v.2.1 ξ₁ ξ₂) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
    exact C3.comp (f := fun p : (ℝ × ℝ × ℝ) × ℝ => (p.1.1, p.1.2.1, p.2, p.1.2.2)) (by fun_prop)
  have C1 : Continuous fun v : ℝ × ℝ => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * H v.2 (unitaryElt v.1 η ξ₁ ξ₂) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
    exact C2.comp (f := fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.2, p.1.2)) (by fun_prop)
  have e4 : ∀ ψ η ξ₁ : ℝ, ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * ∫ t in a..b, H t (unitaryElt ψ η ξ₁ ξ₂) =
      ∫ t in a..b, ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * H t (unitaryElt ψ η ξ₁ ξ₂) := by
    intro ψ η ξ₁
    have hc : ∀ ξ₂ : ℝ, (Real.sin η * Real.cos η : ℂ) * ∫ t in a..b, H t (unitaryElt ψ η ξ₁ ξ₂) =
        ∫ t in a..b, (Real.sin η * Real.cos η : ℂ) * H t (unitaryElt ψ η ξ₁ ξ₂) := fun ξ₂ =>
      (intervalIntegral.integral_const_mul _ _).symm
    simp only [hc]
    exact swap h2π _ (C4.comp (f := fun q : ℝ × ℝ => (ψ, η, ξ₁, q.1, q.2)) (by fun_prop))
  have e3 : ∀ ψ η : ℝ, ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ t in a..b, ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * H t (unitaryElt ψ η ξ₁ ξ₂) =
      ∫ t in a..b, ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * H t (unitaryElt ψ η ξ₁ ξ₂) := fun ψ η =>
    swap h2π _ (C3.comp (f := fun q : ℝ × ℝ => (ψ, η, q.1, q.2)) (by fun_prop))
  have e2 : ∀ ψ : ℝ, ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ t in a..b, ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * H t (unitaryElt ψ η ξ₁ ξ₂) =
      ∫ t in a..b, ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * H t (unitaryElt ψ η ξ₁ ξ₂) := fun ψ =>
    swap hπ2 _ (C2.comp (f := fun q : ℝ × ℝ => (ψ, q.1, q.2)) (by fun_prop))
  have e1 : ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ t in a..b, ∫ η in (0 : ℝ)..(Real.pi / 2),
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * H t (unitaryElt ψ η ξ₁ ξ₂) =
      ∫ t in a..b, ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2),
        ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * H t (unitaryElt ψ η ξ₁ ξ₂) :=
    swap h2π _ C1
  simp only [unitaryAverage, e4, e3, e2, e1]
  exact (intervalIntegral.integral_const_mul _ _).symm

private theorem coe_scalarElt (z : ℂ) (hz : z ≠ 0) :
    ((scalarElt z hz : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.scalar (Fin 2) z := rfl

private theorem scalarElt_mul_scalarElt (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    scalarElt z hz * scalarElt w hw = scalarElt (z * w) (mul_ne_zero hz hw) := by
  apply Units.ext
  simp only [Units.val_mul, coe_scalarElt, map_mul]

private theorem scalarElt_inv (z : ℂ) (hz : z ≠ 0) : (scalarElt z hz)⁻¹ = scalarElt z⁻¹ (inv_ne_zero hz) := by
  apply Units.ext
  rw [scalarElt, ← map_inv, Units.coe_map, Units.val_inv_eq_inv_val, Units.val_mk0]
  rfl

private theorem conjEntries_mul (a b : GL (Fin 2) ℂ) : conjEntries (a * b) = conjEntries a * conjEntries b :=
  map_mul (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) a b

private theorem conjEntries_scalarElt (z : ℂ) (hz : z ≠ 0) :
    conjEntries (scalarElt z hz) = scalarElt ((starRingEnd ℂ) z) ((_root_.map_ne_zero _).2 hz) := by
  apply Units.ext
  ext i j
  simp only [conjEntries, Matrix.GeneralLinearGroup.map_apply, coe_scalarElt, Matrix.scalar_apply,
    Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem scalarElt_mul_twisted (z : ℂ) (hz : z ≠ 0) (k g : GL (Fin 2) ℂ) :
    ((scalarElt z hz * k)⁻¹ * g * conjEntries (scalarElt z hz * k) : GL (Fin 2) ℂ) =
      scalarElt (z⁻¹ * (starRingEnd ℂ) z) (mul_ne_zero (inv_ne_zero hz) ((_root_.map_ne_zero _).2 hz)) *
        (k⁻¹ * g * conjEntries k) := by
  rw [mul_inv_rev, scalarElt_inv, conjEntries_mul, conjEntries_scalarElt,
    ← scalarElt_mul_scalarElt z⁻¹ ((starRingEnd ℂ) z) (inv_ne_zero hz) ((_root_.map_ne_zero _).2 hz)]
  apply Units.ext
  simp only [Units.val_mul, coe_scalarElt, Matrix.scalar_apply, mul_assoc, ← Matrix.smul_eq_diagonal_mul,
    Matrix.mul_smul, smul_smul, mul_comm]

private theorem unitaryAverage_twisted_preparedInput (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ) (p : P)
    (g : GL (Fin 2) ℂ) :
    unitaryAverage (fun k => parameterSlice Φ p (k⁻¹ * g * conjEntries k)) =
      unitaryAverage (fun k => parameterSlice (preparedInput Φ) p (k⁻¹ * g * conjEntries k)) := by
  set F : GL (Fin 2) ℂ → ℂ := fun k => parameterSlice Φ p (k⁻¹ * g * conjEntries k) with hFdef
  have hX : Continuous fun k : GL (Fin 2) ℂ => ((k⁻¹ * g * conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
    Units.continuous_val.comp ((continuous_inv.mul continuous_const).mul continuous_conjEntries)
  have hFc : Continuous F := hΦ.comp (hX.prodMk continuous_const)
  have hscalar : ∀ ψ : ℝ, (Complex.exp (ψ * Complex.I))⁻¹ * (starRingEnd ℂ) (Complex.exp (ψ * Complex.I)) =
      Complex.exp (-(2 * ψ * Complex.I)) := by
    intro ψ
    rw [← Complex.exp_conj, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hpt : ∀ k : GL (Fin 2) ℂ, parameterSlice (preparedInput Φ) p (k⁻¹ * g * conjEntries k) =
      (1 / (2 * Real.pi) : ℂ) * ∫ ψ in (0 : ℝ)..(2 * Real.pi),
        F (scalarElt (Complex.exp (ψ * Complex.I)) (Complex.exp_ne_zero _) * k) := by
    intro k
    simp only [parameterSlice, preparedInput]
    congr 1
    refine intervalIntegral.integral_congr fun ψ _ => ?_
    simp only [hFdef, parameterSlice, scalarElt_mul_twisted]
    refine congrArg Φ (Prod.ext ?_ rfl)
    funext i j
    simp only [Matrix.of_symm_apply, Units.val_mul, coe_scalarElt, Matrix.scalar_apply, Matrix.diagonal_mul, hscalar]
  have hs : Continuous fun ψ : ℝ => scalarElt (Complex.exp (ψ * Complex.I)) (Complex.exp_ne_zero _) := by
    have he : Continuous fun ψ : ℝ => Complex.exp (ψ * Complex.I) :=
      Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun ψ : ℝ => Matrix.scalar (Fin 2) (Complex.exp (ψ * Complex.I))
      simp only [Matrix.scalar_apply]
      exact Continuous.matrix_diagonal (continuous_pi fun _ => he)
    · have h : (fun ψ : ℝ => (((scalarElt (Complex.exp (ψ * Complex.I)) (Complex.exp_ne_zero _))⁻¹ : GL (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ)) = fun ψ : ℝ => Matrix.scalar (Fin 2) (Complex.exp (ψ * Complex.I))⁻¹ := by
        funext ψ
        rw [scalarElt_inv, coe_scalarElt]
      rw [h]
      simp only [Matrix.scalar_apply]
      exact Continuous.matrix_diagonal (continuous_pi fun _ => he.inv₀ fun ψ => Complex.exp_ne_zero _)
  have hjoint : Continuous fun q : ℝ × GL (Fin 2) ℂ =>
      F (scalarElt (Complex.exp (q.1 * Complex.I)) (Complex.exp_ne_zero _) * q.2) :=
    hFc.comp ((hs.comp continuous_fst).mul continuous_snd)
  have hiso : ∀ ψ : ℝ, star ((scalarElt (Complex.exp (ψ * Complex.I)) (Complex.exp_ne_zero _) : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) * ((scalarElt (Complex.exp (ψ * Complex.I)) (Complex.exp_ne_zero _) : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    intro ψ
    have hψ : (starRingEnd ℂ) (Complex.exp (ψ * Complex.I)) * Complex.exp (ψ * Complex.I) = 1 := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      simp
    rw [coe_scalarElt, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext _
    simpa only [Pi.star_apply, Complex.star_def] using hψ
  have hdock : ∀ ψ : ℝ, unitaryAverage
      (fun k => F (scalarElt (Complex.exp (ψ * Complex.I)) (Complex.exp_ne_zero _) * k)) = unitaryAverage F := by
    intro ψ
    have h := unitaryAverage_translate F hFc _ 1 (hiso ψ) (by simp)
    simpa only [mul_one] using h
  simp only [hpt]
  rw [unitaryAverage_const_mul', unitaryAverage_intervalIntegral 0 (2 * Real.pi)
    (fun ψ k => F (scalarElt (Complex.exp (ψ * Complex.I)) (Complex.exp_ne_zero _) * k)) hjoint]
  simp only [hdock]
  rw [intervalIntegral.integral_const, sub_zero]
  erw [Complex.real_smul]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp

end RightFiniteExpansion
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted.RightFiniteExpansion"

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted.RightFiniteExpansion"

noncomputable section

namespace TwistedAverageExpansion

open RightFiniteExpansion

variable {P : Type}

private def twistedAverage (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (p : P) (g : GL (Fin 2) ℂ) : ℂ :=
  unitaryAverage fun k => parameterSlice Φ p (k⁻¹ * g * conjEntries k)

private def oddPart (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (p : P) (g : GL (Fin 2) ℂ) : ℂ :=
  (twistedAverage Φ p g - twistedAverage Φ p (conjEntries g)) / 2

private theorem oddPart_conjEntries (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (p : P) (g : GL (Fin 2) ℂ) :
    oddPart Φ p (conjEntries g) = -oddPart Φ p g := by
  unfold oddPart
  rw [AutomorphicForm.GL2Twisted.OddInputs.conjEntries_conjEntries]
  ring

private theorem isDetOneIsometryGroup : IsDetOneIsometryGroup := by
  intro u hu hdet
  exact mem_rowIsometrySubgroup₀_of_star_mul_self u hu hdet

private def IsBalancedDecomposition (g k₁ k₂ : GL (Fin 2) ℂ) : Prop :=
  star (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
    star (k₂ : Matrix (Fin 2) (Fin 2) ℂ) * (k₂ : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
    Matrix.det (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.det (k₂ : Matrix (Fin 2) (Fin 2) ℂ) ∧
    (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal (invFrobSq g) (invAbsDet g) * (k₂ : Matrix (Fin 2) (Fin 2) ℂ)

private theorem exists_isBalancedDecomposition (g : GL (Fin 2) ℂ) :
    ∃ k₁ k₂ : GL (Fin 2) ℂ, IsBalancedDecomposition g k₁ k₂ := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hdet₂, hg⟩ := exists_unitary_mul_singularDiagonal_mul_unitary g
  have hd : (starRingEnd ℂ) (Matrix.det (k₁ : Matrix (Fin 2) (Fin 2) ℂ)) *
      Matrix.det (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have h1 := congrArg Matrix.det hk₁
    rwa [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at h1
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (Matrix.det (k₁ : Matrix (Fin 2) (Fin 2) ℂ)) (by norm_num : 0 < 4)
  have hcc : (starRingEnd ℂ) c * c = 1 := by
    have h4 : ((Complex.normSq c : ℝ) : ℂ) ^ 4 = 1 := by
      rw [Complex.normSq_eq_conj_mul_self, mul_pow, ← map_pow, hc, hd]
    have h4' : Complex.normSq c ^ 4 = 1 := by exact_mod_cast h4
    have h1 : Complex.normSq c = 1 := (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg c) (by norm_num)).1 h4'
    rw [← Complex.normSq_eq_conj_mul_self, h1, Complex.ofReal_one]
  have hc0 : c ≠ 0 := right_ne_zero_of_mul_eq_one hcc
  have hci : (starRingEnd ℂ) c⁻¹ * c⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hcc, inv_one]
  have hdetc : Matrix.det (Matrix.diagonal ![c, c] : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp [hc0]
  obtain ⟨s, hs⟩ : ∃ s : GL (Fin 2) ℂ, (s : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![c, c] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetc, rfl⟩
  have hsi : ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![c⁻¹, c⁻¹] := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [mul_inv_cancel₀ hc0]
  have hdu : ∀ x : ℂ, (starRingEnd ℂ) x * x = 1 →
      star (Matrix.diagonal ![x, x] : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.diagonal ![x, x] = 1 := by
    intro x hx
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simpa [Complex.star_def] using hx
  have hsu : star (s : Matrix (Fin 2) (Fin 2) ℂ) * (s : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [hs]
    exact hdu c hcc
  have hsiu : star ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [hsi]
    exact hdu c⁻¹ hci
  have hds : Matrix.det (s : Matrix (Fin 2) (Fin 2) ℂ) = c * c := by
    rw [hs, Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  have hdsi : Matrix.det ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = c⁻¹ * c⁻¹ := by
    rw [hsi, Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  have hcomm : singularDiagonal (invFrobSq g) (invAbsDet g) * ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal (invFrobSq g) (invAbsDet g) := by
    rw [hsi]
    simp only [singularDiagonal, Matrix.diagonal_mul_diagonal, mul_comm]
  refine ⟨k₁ * s⁻¹, s * k₂, ?_⟩
  unfold IsBalancedDecomposition
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul, star_mul, mul_assoc, ← mul_assoc (star (k₁ : Matrix (Fin 2) (Fin 2) ℂ)), hk₁, one_mul, hsiu]
  · rw [Units.val_mul, star_mul, mul_assoc, ← mul_assoc (star (s : Matrix (Fin 2) (Fin 2) ℂ)), hsu, one_mul, hk₂]
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdsi, hds, hdet₂, mul_one, ← hc,
      show (c ^ 4 : ℂ) = c * c * (c * c) by ring, mul_assoc,
      show (c * c) * (c⁻¹ * c⁻¹) = (1 : ℂ) by rw [mul_mul_mul_comm, mul_inv_cancel₀ hc0, one_mul], mul_one]
  · rw [Units.val_mul, Units.val_mul, hg]
    simp only [mul_assoc]
    rw [← mul_assoc ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), ← hcomm, mul_assoc,
      ← mul_assoc ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), Units.inv_mul, one_mul]

private theorem IsBalancedDecomposition.star_mul_self {g k₁ k₂ : GL (Fin 2) ℂ} (h : IsBalancedDecomposition g k₁ k₂) :
    star ((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  obtain ⟨hk₁, hk₂, -, -⟩ := h
  have hc : star ((conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    star_mul_self_conjEntries k₁ hk₁
  rw [Units.val_mul, star_mul, mul_assoc, ← mul_assoc (star (k₂ : Matrix (Fin 2) (Fin 2) ℂ)), hk₂, one_mul, hc]

private theorem IsBalancedDecomposition.det_eq_one {g k₁ k₂ : GL (Fin 2) ℂ} (h : IsBalancedDecomposition g k₁ k₂) :
    Matrix.det ((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  obtain ⟨hk₁, hk₂, hdet, -⟩ := h
  have hunit : (starRingEnd ℂ) (Matrix.det (k₂ : Matrix (Fin 2) (Fin 2) ℂ)) *
      Matrix.det (k₂ : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have h1 := congrArg Matrix.det hk₂
    rwa [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at h1
  rw [Units.val_mul, Matrix.det_mul, det_conjEntries, hdet, mul_comm, hunit]

private theorem IsBalancedDecomposition.torus {g k₁ k₂ : GL (Fin 2) ℂ} (h : IsBalancedDecomposition g k₁ k₂) (φ : ℝ) :
    ∃ k₁' k₂' : GL (Fin 2) ℂ, IsBalancedDecomposition g k₁' k₂' ∧
      ((k₂' * conjEntries k₁' : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] *
            ((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
          Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] := by
  obtain ⟨hk₁, hk₂, hdet, hg⟩ := h
  have hee : Complex.exp (φ * Complex.I) * Complex.exp (-(φ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hee' : Complex.exp (-(φ * Complex.I)) * Complex.exp (φ * Complex.I) = 1 := by
    rw [mul_comm, hee]
  have hcφ : (starRingEnd ℂ) (Complex.exp (φ * Complex.I)) = Complex.exp (-(φ * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hcφ' : (starRingEnd ℂ) (Complex.exp (-(φ * Complex.I))) = Complex.exp (φ * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hst : (Matrix.diagonal ![Complex.exp (φ * Complex.I), Complex.exp (-(φ * Complex.I))] :
        Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hee, hee']
  have hdets : Matrix.det
      (Matrix.diagonal ![Complex.exp (φ * Complex.I), Complex.exp (-(φ * Complex.I))] :
        Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp [hee]
  obtain ⟨s, hs⟩ : ∃ s : GL (Fin 2) ℂ, (s : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![Complex.exp (φ * Complex.I), Complex.exp (-(φ * Complex.I))] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdets, rfl⟩
  have hsi : ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hs]; exact hst)
  have hcs : ((conjEntries s : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] := by
    show (s : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) = _
    rw [hs, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    fin_cases i <;> simp [hcφ, hcφ']
  have hdu : ∀ x y : ℂ, star x * x = 1 → star y * y = 1 →
      star (Matrix.diagonal ![x, y] : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.diagonal ![x, y] = 1 := by
    intro x y hx hy
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simpa using hx
    · simpa using hy
  have hux : star (Complex.exp (φ * Complex.I)) * Complex.exp (φ * Complex.I) = 1 := by
    rw [Complex.star_def, hcφ, hee']
  have huy : star (Complex.exp (-(φ * Complex.I))) * Complex.exp (-(φ * Complex.I)) = 1 := by
    rw [Complex.star_def, hcφ', hee]
  have hsu : star (s : Matrix (Fin 2) (Fin 2) ℂ) * (s : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [hs]
    exact hdu _ _ hux huy
  have hsiu : star ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [hsi]
    exact hdu _ _ huy hux
  have hds : Matrix.det (s : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [hs, Matrix.det_diagonal, Fin.prod_univ_two]
    simpa using hee
  have hdsi : Matrix.det ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [hsi, Matrix.det_diagonal, Fin.prod_univ_two]
    simpa using hee'
  have hcomm : singularDiagonal (invFrobSq g) (invAbsDet g) * (s : Matrix (Fin 2) (Fin 2) ℂ) =
      (s : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal (invFrobSq g) (invAbsDet g) := by
    rw [hs]
    simp only [singularDiagonal, Matrix.diagonal_mul_diagonal, mul_comm]
  have hcm : conjEntries (k₁ * s) = conjEntries k₁ * conjEntries s := by
    unfold conjEntries
    exact map_mul _ _ _
  refine ⟨k₁ * s, s⁻¹ * k₂, ?_, ?_⟩
  · unfold IsBalancedDecomposition
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Units.val_mul, star_mul, mul_assoc, ← mul_assoc (star (k₁ : Matrix (Fin 2) (Fin 2) ℂ)), hk₁, one_mul, hsu]
    · rw [Units.val_mul, star_mul, mul_assoc,
        ← mul_assoc (star ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), hsiu, one_mul, hk₂]
    · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, hds, hdsi, mul_one, one_mul]
    · rw [Units.val_mul, Units.val_mul, hg]
      simp only [mul_assoc]
      rw [← mul_assoc (s : Matrix (Fin 2) (Fin 2) ℂ), ← hcomm, mul_assoc, ← mul_assoc (s : Matrix (Fin 2) (Fin 2) ℂ),
        Units.mul_inv, one_mul]
  ·
    rw [Units.val_mul, Units.val_mul, hcm, Units.val_mul, hsi, hcs, Units.val_mul]
    simp only [mul_assoc]

private theorem IsBalancedDecomposition.neg {g k₁ k₂ : GL (Fin 2) ℂ} (h : IsBalancedDecomposition g k₁ k₂) :
    ∃ k₁' k₂' : GL (Fin 2) ℂ, IsBalancedDecomposition g k₁' k₂' ∧ k₂' * conjEntries k₁' = -(k₂ * conjEntries k₁) := by
  obtain ⟨hk₁, hk₂, hdet, hg⟩ := h
  have hdetI : Matrix.det (Matrix.diagonal ![Complex.I, Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  obtain ⟨s, hs⟩ : ∃ s : GL (Fin 2) ℂ, (s : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![Complex.I, Complex.I] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetI, rfl⟩
  have hII : (Matrix.diagonal ![Complex.I, Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.diagonal ![-Complex.I, -Complex.I] = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  have hsi : ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![-Complex.I, -Complex.I] :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hs]; exact hII)
  have hcs : ((conjEntries s : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![-Complex.I, -Complex.I] := by
    show (s : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) = _
    rw [hs, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    fin_cases i <;> simp
  have hdu : ∀ x : ℂ, star x * x = 1 →
      star (Matrix.diagonal ![x, x] : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.diagonal ![x, x] = 1 := by
    intro x hx
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simpa using hx
  have hsu : star (s : Matrix (Fin 2) (Fin 2) ℂ) * (s : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [hs]
    exact hdu _ (by simp)
  have hsiu : star ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [hsi]
    exact hdu _ (by simp)
  have hds : Matrix.det (s : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    rw [hs, Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  have hdsi : Matrix.det ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    rw [hsi, Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  have hcomm : singularDiagonal (invFrobSq g) (invAbsDet g) * (s : Matrix (Fin 2) (Fin 2) ℂ) =
      (s : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal (invFrobSq g) (invAbsDet g) := by
    rw [hs]
    simp only [singularDiagonal, Matrix.diagonal_mul_diagonal, mul_comm]
  have hsm : (Matrix.diagonal ![-Complex.I, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) =
      (-Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hcm : conjEntries (k₁ * s) = conjEntries k₁ * conjEntries s := by
    unfold conjEntries
    exact map_mul _ _ _
  refine ⟨k₁ * s, s⁻¹ * k₂, ?_, ?_⟩
  · unfold IsBalancedDecomposition
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Units.val_mul, star_mul, mul_assoc, ← mul_assoc (star (k₁ : Matrix (Fin 2) (Fin 2) ℂ)), hk₁, one_mul, hsu]
    · rw [Units.val_mul, star_mul, mul_assoc,
        ← mul_assoc (star ((s⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), hsiu, one_mul, hk₂]
    · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, hds, hdsi, mul_comm]
    · rw [Units.val_mul, Units.val_mul, hg]
      simp only [mul_assoc]
      rw [← mul_assoc (s : Matrix (Fin 2) (Fin 2) ℂ), ← hcomm, mul_assoc, ← mul_assoc (s : Matrix (Fin 2) (Fin 2) ℂ),
        Units.mul_inv, one_mul]
  ·
    apply Units.ext
    rw [Units.val_neg, Units.val_mul, Units.val_mul, Units.val_mul, hcm, Units.val_mul, hsi, hcs, hsm]
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul, neg_mul_neg, Complex.I_mul_I,
      neg_one_smul]

private theorem invFrobSq_conjEntries (g : GL (Fin 2) ℂ) : invFrobSq (conjEntries g) = invFrobSq g := by
  have hc : ((conjEntries g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) := rfl
  simp only [invFrobSq, hc, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Fin.sum_univ_two, Complex.star_def, Complex.conj_conj, Complex.add_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  ring

private theorem invAbsDet_conjEntries (g : GL (Fin 2) ℂ) : invAbsDet (conjEntries g) = invAbsDet g := by
  simp only [invAbsDet, det_conjEntries, Complex.norm_conj]

private theorem IsBalancedDecomposition.conjEntries {g k₁ k₂ : GL (Fin 2) ℂ} (h : IsBalancedDecomposition g k₁ k₂) :
    IsBalancedDecomposition (conjEntries g) (conjEntries k₁) (conjEntries k₂) := by
  obtain ⟨hk₁, hk₂, hdet, hg⟩ := h
  have hc : ∀ k : GL (Fin 2) ℂ,
      ((AutomorphicForm.GL2Twisted.conjEntries k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        (k : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) :=
    fun _ => rfl
  have hD : (singularDiagonal (invFrobSq g) (invAbsDet g)).map (starRingEnd ℂ) =
      singularDiagonal (invFrobSq g) (invAbsDet g) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [singularDiagonal, Complex.conj_ofReal]
  unfold IsBalancedDecomposition
  refine ⟨star_mul_self_conjEntries k₁ hk₁, star_mul_self_conjEntries k₂ hk₂, ?_, ?_⟩
  · rw [det_conjEntries, det_conjEntries, hdet]
  · rw [invFrobSq_conjEntries, invAbsDet_conjEntries, hc, hc, hc, hg, Matrix.map_mul, Matrix.map_mul, hD]

private theorem conjEntries_mul_conjEntries_conjEntries (k₁ k₂ : GL (Fin 2) ℂ) :
    conjEntries k₂ * conjEntries (conjEntries k₁) = conjEntries (k₂ * conjEntries k₁) := by
  unfold conjEntries
  exact (map_mul _ _ _).symm

private theorem invFrobSq_eq_of_coe_eq {g k₁ k₂ : GL (Fin 2) ℂ} {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hk₁ : star (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (hk₂ : star (k₂ : Matrix (Fin 2) (Fin 2) ℂ) * (k₂ : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * M * (k₂ : Matrix (Fin 2) (Fin 2) ℂ)) :
    invFrobSq g = (Matrix.trace (M * M.conjTranspose)).re := by
  have hk₂' : (k₂ : Matrix (Fin 2) (Fin 2) ℂ) * star (k₂ : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    _root_.mul_eq_one_comm.1 hk₂
  rw [Matrix.star_eq_conjTranspose] at hk₁ hk₂'
  unfold invFrobSq
  rw [hg]
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (k₂ : Matrix (Fin 2) (Fin 2) ℂ), hk₂', Matrix.one_mul, ← Matrix.mul_assoc M,
    ← Matrix.mul_assoc (k₁ : Matrix (Fin 2) (Fin 2) ℂ), Matrix.trace_mul_cycle, hk₁, Matrix.one_mul]

private theorem invAbsDet_eq_of_coe_eq {g k₁ k₂ : GL (Fin 2) ℂ} {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hk₁ : star (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (hk₂ : star (k₂ : Matrix (Fin 2) (Fin 2) ℂ) * (k₂ : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * M * (k₂ : Matrix (Fin 2) (Fin 2) ℂ)) :
    invAbsDet g = ‖Matrix.det M‖ := by
  have hdet : ∀ k : GL (Fin 2) ℂ, star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
    intro k hk
    have h₁ := congrArg Matrix.det hk
    rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at h₁
    have h₂ := congrArg norm h₁
    rw [norm_mul, norm_star, norm_one] at h₂
    exact (mul_self_eq_one_iff.1 h₂).resolve_right (by
      intro h₃
      linarith [norm_nonneg (Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ))])
  unfold invAbsDet
  rw [hg, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, hdet k₁ hk₁, hdet k₂ hk₂, one_mul, mul_one]

private theorem re_trace_singularDiagonal_mul_conjTranspose (T d : ℝ) (hd : 0 ≤ d) (hT : 2 * d ≤ T) :
    (Matrix.trace (singularDiagonal T d * (singularDiagonal T d).conjTranspose)).re = T := by
  obtain ⟨-, -, hsum, -⟩ := singularValues_spec T d hd hT
  simp only [singularDiagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.star_def, Complex.conj_ofReal]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination hsum

private theorem norm_det_singularDiagonal (T d : ℝ) (hd : 0 ≤ d) (hT : 2 * d ≤ T) :
    ‖Matrix.det (singularDiagonal T d)‖ = d := by
  rw [det_singularDiagonal T d hd hT, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]

private def diagonalElt (q : ℝ × ℝ) (hq : q ∈ normDetCone) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (singularDiagonal q.1 q.2) (by
    rw [det_singularDiagonal q.1 q.2 hq.2.le hq.1]
    exact Complex.ofReal_ne_zero.2 hq.2.ne')

private def discElt (a b : ℝ) (h : a ^ 2 + b ^ 2 ≤ 1) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ), (a : ℂ) + (b : ℂ) * Complex.I;
      -((a : ℂ) - (b : ℂ) * Complex.I), (Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ)] (by
    rw [Matrix.det_fin_two_of]
    have hs : (Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ) ^ 2 = 1 - (a : ℂ) ^ 2 - (b : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
      push_cast
      ring
    have h1 : (Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ) * (Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ) -
        ((a : ℂ) + (b : ℂ) * Complex.I) * -((a : ℂ) - (b : ℂ) * Complex.I) = 1 := by
      linear_combination hs - (b : ℂ) ^ 2 * Complex.I_sq
    rw [h1]
    exact one_ne_zero)

private theorem discElt_apply_zero_one (a b : ℝ) (h : a ^ 2 + b ^ 2 ≤ 1) :
    ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = (a : ℂ) + (b : ℂ) * Complex.I := by
  rfl

private theorem isBalancedDecomposition_diagonalElt_mul_discElt (q : ℝ × ℝ) (hq : q ∈ normDetCone) (a b : ℝ)
    (h : a ^ 2 + b ^ 2 ≤ 1) : IsBalancedDecomposition (diagonalElt q hq * discElt a b h) 1 (discElt a b h) := by
  have hs : (Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ) ^ 2 = 1 - (a : ℂ) ^ 2 - (b : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
    push_cast
    ring
  have hW : ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ), (a : ℂ) + (b : ℂ) * Complex.I;
        -((a : ℂ) - (b : ℂ) * Complex.I), (Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ)] := rfl
  have hw : star ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [hW, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hs - (b : ℂ) ^ 2 * Complex.I_sq
  have h1 : star ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simp
  have hg : ((diagonalElt q hq * discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal q.1 q.2 *
        ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Units.val_mul, Units.val_one, Matrix.one_mul]
    rfl
  have hF : invFrobSq (diagonalElt q hq * discElt a b h) = q.1 := by
    rw [invFrobSq_eq_of_coe_eq h1 hw hg]
    exact re_trace_singularDiagonal_mul_conjTranspose q.1 q.2 hq.2.le hq.1
  have hA : invAbsDet (diagonalElt q hq * discElt a b h) = q.2 := by
    rw [invAbsDet_eq_of_coe_eq h1 hw hg]
    exact norm_det_singularDiagonal q.1 q.2 hq.2.le hq.1
  have hdetw : Matrix.det ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [hW, Matrix.det_fin_two_of]
    linear_combination hs - (b : ℂ) ^ 2 * Complex.I_sq
  refine ⟨h1, hw, ?_, ?_⟩
  · rw [Units.val_one, Matrix.det_one, hdetw]
  · rw [hF, hA, Units.val_mul, Units.val_one, Matrix.one_mul]
    rfl

private theorem invFrobSq_diagonalElt_mul_discElt (q : ℝ × ℝ) (hq : q ∈ normDetCone) (a b : ℝ)
    (h : a ^ 2 + b ^ 2 ≤ 1) : invFrobSq (diagonalElt q hq * discElt a b h) = q.1 := by
  have hs : (Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ) ^ 2 = 1 - (a : ℂ) ^ 2 - (b : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
    push_cast
    ring
  have hW : ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ), (a : ℂ) + (b : ℂ) * Complex.I;
        -((a : ℂ) - (b : ℂ) * Complex.I), (Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ)] := rfl
  have hw : star ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [hW, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hs - (b : ℂ) ^ 2 * Complex.I_sq
  have h1 : star ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simp
  have hg : ((diagonalElt q hq * discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal q.1 q.2 *
        ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Units.val_mul, Units.val_one, Matrix.one_mul]
    rfl
  rw [invFrobSq_eq_of_coe_eq h1 hw hg]
  exact re_trace_singularDiagonal_mul_conjTranspose q.1 q.2 hq.2.le hq.1

private theorem invAbsDet_diagonalElt_mul_discElt (q : ℝ × ℝ) (hq : q ∈ normDetCone) (a b : ℝ)
    (h : a ^ 2 + b ^ 2 ≤ 1) : invAbsDet (diagonalElt q hq * discElt a b h) = q.2 := by
  have hs : (Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ) ^ 2 = 1 - (a : ℂ) ^ 2 - (b : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
    push_cast
    ring
  have hW : ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ), (a : ℂ) + (b : ℂ) * Complex.I;
        -((a : ℂ) - (b : ℂ) * Complex.I), (Real.sqrt (1 - a ^ 2 - b ^ 2) : ℂ)] := rfl
  have hw : star ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [hW, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hs - (b : ℂ) ^ 2 * Complex.I_sq
  have h1 : star ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simp
  have hg : ((diagonalElt q hq * discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal q.1 q.2 *
        ((discElt a b h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Units.val_mul, Units.val_one, Matrix.one_mul]
    rfl
  rw [invAbsDet_eq_of_coe_eq h1 hw hg]
  exact norm_det_singularDiagonal q.1 q.2 hq.2.le hq.1

private theorem continuous_diagonalElt : Continuous fun x : ↥normDetCone => diagonalElt (x : ℝ × ℝ) x.2 := by
  have hu : Continuous fun x : ↥normDetCone => ((upperSingularValue (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_upperSingularValue.comp continuous_subtype_val)
  have hl : Continuous fun x : ↥normDetCone => ((lowerSingularValue (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_lowerSingularValue.comp continuous_subtype_val)
  have hval : Continuous fun x : ↥normDetCone =>
      ((diagonalElt (x : ℝ × ℝ) x.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    show Continuous fun x : ↥normDetCone => singularDiagonal (x : ℝ × ℝ).1 (x : ℝ × ℝ).2
    unfold singularDiagonal
    exact (hu.matrixVecCons (hl.matrixVecCons continuous_const)).matrix_diagonal
  have hdet : ∀ x : ↥normDetCone,
      Matrix.det ((diagonalElt (x : ℝ × ℝ) x.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
    intro x
    show Matrix.det (singularDiagonal (x : ℝ × ℝ).1 (x : ℝ × ℝ).2) ≠ 0
    rw [det_singularDiagonal _ _ x.2.2.le x.2.1]
    exact Complex.ofReal_ne_zero.2 x.2.2.ne'
  have hinv : Continuous fun x : ↥normDetCone =>
      (Matrix.det ((diagonalElt (x : ℝ × ℝ) x.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ •
        Matrix.adjugate ((diagonalElt (x : ℝ × ℝ) x.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
    (hval.matrix_det.inv₀ hdet).smul hval.matrix_adjugate
  refine Units.continuous_iff.2 ⟨hval, hinv.congr fun x => ?_⟩
  rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv]

private def rightSubst (v : Matrix (Fin 2) (Fin 2) ℂ) (Q : MvPolynomial (Fin 2 × Fin 2) ℂ) :
    MvPolynomial (Fin 2 × Fin 2) ℂ :=
  MvPolynomial.aeval
    (fun ij : Fin 2 × Fin 2 => ∑ k : Fin 2, MvPolynomial.X (R := ℂ) (ij.1, k) * MvPolynomial.C (v k ij.2)) Q

private theorem totalDegree_rightSubst_le (v : Matrix (Fin 2) (Fin 2) ℂ) (Q : MvPolynomial (Fin 2 × Fin 2) ℂ) :
    (rightSubst v Q).totalDegree ≤ Q.totalDegree := by
  have hf : ∀ ij : Fin 2 × Fin 2,
      (∑ k : Fin 2, MvPolynomial.X (R := ℂ) (ij.1, k) * MvPolynomial.C (v k ij.2)).totalDegree ≤ 1 := by
    intro ij
    refine MvPolynomial.totalDegree_finsetSum_le fun k _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, add_zero]
    exact (MvPolynomial.totalDegree_X _).le
  have hprod : ∀ (m : (Fin 2 × Fin 2) →₀ ℕ) (s : Finset (Fin 2 × Fin 2)),
      (∏ ij ∈ s, (∑ k : Fin 2, MvPolynomial.X (R := ℂ) (ij.1, k) * MvPolynomial.C (v k ij.2)) ^ m ij).totalDegree ≤
        ∑ ij ∈ s, m ij := by
    intro m s
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (MvPolynomial.totalDegree_mul _ _).trans (add_le_add
      (((MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left (m a) (hf a))).trans_eq (mul_one _)) ih)
  unfold rightSubst
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine MvPolynomial.totalDegree_finsetSum_le fun m hm => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  exact (hprod m m.support).trans (MvPolynomial.le_totalDegree hm)

private theorem eval_rightSubst (w v : Matrix (Fin 2) (Fin 2) ℂ) (Q : MvPolynomial (Fin 2 × Fin 2) ℂ) :
    MvPolynomial.eval (fun ij : Fin 2 × Fin 2 => w ij.1 ij.2) (rightSubst v Q) =
      MvPolynomial.eval (fun ij : Fin 2 × Fin 2 => (w * v) ij.1 ij.2) Q := by
  unfold rightSubst
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
    simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X, map_sum, MvPolynomial.eval_C,
      Matrix.mul_apply]

private theorem exists_linear_reconstruction (D : ℕ) :
    ∃ (s : Finset (ℝ × ℝ)) (L : (↥s → ℂ) →ₗ[ℂ] MvPolynomial (Fin 2) ℂ),
      (∀ q ∈ s, q.1 ^ 2 + q.2 ^ 2 ≤ 1) ∧
      (∀ v, L v ∈ MvPolynomial.restrictDegree (Fin 2) ℂ D) ∧
      ∀ F ∈ MvPolynomial.restrictDegree (Fin 2) ℂ D,
        L (fun q => MvPolynomial.eval ![((q : ℝ × ℝ).1 : ℂ), ((q : ℝ × ℝ).2 : ℂ)] F) = F := by
  classical
  set c : ℝ := 2 * ((D : ℝ) + 1)
  have hc : 0 < c := by positivity
  have hinjN : Function.Injective (fun k : ℕ => (k : ℝ) / c) := by
    intro a b h
    have h' := congrArg (fun x : ℝ => x * c) h
    simp only [div_mul_cancel₀ _ hc.ne'] at h'
    exact_mod_cast h'
  set N : Finset ℝ := (Finset.range (D + 1)).image (fun k : ℕ => (k : ℝ) / c) with hN
  have hNbound : ∀ t ∈ N, 0 ≤ t ∧ t ≤ 1 / 2 := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 ht
    rw [Finset.mem_range] at hk
    have hk' : (k : ℝ) ≤ D := by exact_mod_cast Nat.lt_succ_iff.1 hk
    refine ⟨div_nonneg (Nat.cast_nonneg k) hc.le, ?_⟩
    rw [div_le_iff₀ hc]
    linarith
  have hNcard : N.card = D + 1 := by
    rw [hN, Finset.card_image_of_injective _ hinjN, Finset.card_range]
  set S : Fin 2 → Finset ℂ := fun _ => N.image (fun t : ℝ => (t : ℂ)) with hS
  have hScard : ∀ i, (S i).card = D + 1 := fun _ => by
    rw [hS, Finset.card_image_of_injective _ Complex.ofReal_injective, hNcard]
  let ev : ↥(MvPolynomial.restrictDegree (Fin 2) ℂ D) →ₗ[ℂ] (↥(N ×ˢ N) → ℂ) :=
    { toFun := fun F q =>
        MvPolynomial.eval ![((q : ℝ × ℝ).1 : ℂ), ((q : ℝ × ℝ).2 : ℂ)] (F : MvPolynomial (Fin 2) ℂ)
      map_add' := fun F G => funext fun q => by simp only [Submodule.coe_add, map_add, Pi.add_apply]
      map_smul' := fun r F => funext fun q => by
        simp only [Submodule.coe_smul, MvPolynomial.smul_eval, RingHom.id_apply, Pi.smul_apply, smul_eq_mul] }
  have hker : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    refine (injective_iff_map_eq_zero ev).2 fun F hF => ?_
    apply Subtype.ext
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset (F : MvPolynomial (Fin 2) ℂ) S (fun i => ?_)
      (fun x hx => ?_)
    · rw [hScard i]
      have hd : 0 < D + 1 := Nat.succ_pos D
      refine (MvPolynomial.degreeOf_lt_iff hd).2 fun m hm => ?_
      have hF2 := F.2
      rw [MvPolynomial.mem_restrictDegree] at hF2
      exact Nat.lt_succ_of_le (hF2 m hm i)
    · have hx0 := hx 0
      have hx1 := hx 1
      simp only [hS] at hx0 hx1
      obtain ⟨t₀, ht₀, h0⟩ := Finset.mem_image.1 hx0
      obtain ⟨t₁, ht₁, h1⟩ := Finset.mem_image.1 hx1
      have hq : (t₀, t₁) ∈ N ×ˢ N := Finset.mem_product.2 ⟨ht₀, ht₁⟩
      have hx' : x = ![(t₀ : ℂ), (t₁ : ℂ)] := by
        funext i
        fin_cases i
        · exact h0.symm
        · exact h1.symm
      rw [hx']
      exact congrFun hF ⟨(t₀, t₁), hq⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ev hker
  refine ⟨N ×ˢ N, (MvPolynomial.restrictDegree (Fin 2) ℂ D).subtype ∘ₗ g, fun q hq => ?_, fun v => (g v).2,
    fun F hF => ?_⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
    obtain ⟨ha0, ha1⟩ := hNbound _ h1
    obtain ⟨hb0, hb1⟩ := hNbound _ h2
    nlinarith
  · exact congrArg Subtype.val (LinearMap.congr_fun hg ⟨F, hF⟩)

private def grid (D : ℕ) : Finset (ℝ × ℝ) :=
  (exists_linear_reconstruction D).choose

private def reconstruct (D : ℕ) : (↥(grid D) → ℂ) →ₗ[ℂ] MvPolynomial (Fin 2) ℂ :=
  (exists_linear_reconstruction D).choose_spec.choose

private theorem sq_add_sq_le_one_of_mem_grid (D : ℕ) : ∀ q ∈ grid D, q.1 ^ 2 + q.2 ^ 2 ≤ 1 :=
  (exists_linear_reconstruction D).choose_spec.choose_spec.1

private theorem reconstruct_mem_restrictDegree (D : ℕ) (v : ↥(grid D) → ℂ) :
    reconstruct D v ∈ MvPolynomial.restrictDegree (Fin 2) ℂ D :=
  (exists_linear_reconstruction D).choose_spec.choose_spec.2.1 v

private theorem reconstruct_eval (D : ℕ) (F : MvPolynomial (Fin 2) ℂ)
    (hF : F ∈ MvPolynomial.restrictDegree (Fin 2) ℂ D) :
    reconstruct D (fun q => MvPolynomial.eval ![((q : ℝ × ℝ).1 : ℂ), ((q : ℝ × ℝ).2 : ℂ)] F) = F :=
  (exists_linear_reconstruction D).choose_spec.choose_spec.2.2 F hF

open scoped Classical in
private def averagedPolynomial (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (D : ℕ) (p : P) (q : ℝ × ℝ) :
    MvPolynomial (Fin 2) ℂ :=
  if hq : q ∈ normDetCone then
    reconstruct D fun x =>
      twistedAverage Φ p
        (diagonalElt q hq * discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2))
  else 0

private def evenPart (F : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (F + MvPolynomial.aeval (fun j : Fin 2 => -(MvPolynomial.X j : MvPolynomial (Fin 2) ℂ)) F)

private theorem aeval_neg_evenPart (F : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.aeval (fun j : Fin 2 => -(MvPolynomial.X j : MvPolynomial (Fin 2) ℂ)) (evenPart F) = evenPart F := by
  have key : ∀ G : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.aeval (fun j : Fin 2 => -(MvPolynomial.X j : MvPolynomial (Fin 2) ℂ))
        (MvPolynomial.aeval (fun j : Fin 2 => -(MvPolynomial.X j : MvPolynomial (Fin 2) ℂ)) G) = G := by
    intro G
    induction G using MvPolynomial.induction_on
    · simp
    · rename_i p q hp hq
      simp only [map_add, hp, hq]
    · rename_i p i hp
      simp only [map_mul, MvPolynomial.aeval_X, map_neg, neg_neg, hp]
  unfold evenPart
  simp only [map_smul, map_add, key]
  rw [add_comm]

private theorem eval_evenPart (F : MvPolynomial (Fin 2) ℂ) (a b : ℂ) :
    MvPolynomial.eval ![a, b] (evenPart F) =
      (2 : ℂ)⁻¹ * (MvPolynomial.eval ![a, b] F + MvPolynomial.eval ![-a, -b] F) := by
  have key : ∀ (G : MvPolynomial (Fin 2) ℂ) (y : Fin 2 → ℂ),
      MvPolynomial.eval y (MvPolynomial.aeval (fun j : Fin 2 => -(MvPolynomial.X j : MvPolynomial (Fin 2) ℂ)) G) =
        MvPolynomial.eval (fun j => -(y j)) G := by
    intro G y
    induction G using MvPolynomial.induction_on
    · simp
    · rename_i p q hp hq
      simp only [map_add, hp, hq]
    · rename_i p i hp
      simp only [map_mul, MvPolynomial.aeval_X, map_neg, MvPolynomial.eval_X, hp]
  have hneg : (fun j : Fin 2 => -(![a, b] j)) = ![-a, -b] := by
    funext j
    fin_cases j <;> rfl
  unfold evenPart
  rw [MvPolynomial.smul_eval, map_add, key, hneg]

private theorem totalDegree_evenPart_le (F : MvPolynomial (Fin 2) ℂ) : (evenPart F).totalDegree ≤ F.totalDegree := by
  have hsub : (MvPolynomial.aeval (fun j : Fin 2 => -(MvPolynomial.X j : MvPolynomial (Fin 2) ℂ)) F).totalDegree ≤
      F.totalDegree := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    refine MvPolynomial.totalDegree_finsetSum_le fun m hm => ?_
    have hle : ∑ j ∈ m.support, m j ≤ F.totalDegree := MvPolynomial.le_totalDegree hm
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
    refine le_trans ?_ hle
    have hprod : ∀ s : Finset (Fin 2),
        (∏ j ∈ s, (-(MvPolynomial.X j : MvPolynomial (Fin 2) ℂ)) ^ m j).totalDegree ≤ ∑ j ∈ s, m j := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp
      · intro a s ha ih
        rw [Finset.prod_insert ha, Finset.sum_insert ha]
        refine (MvPolynomial.totalDegree_mul _ _).trans (add_le_add ?_ ih)
        refine (MvPolynomial.totalDegree_pow _ _).trans ?_
        simp only [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_X, mul_one, le_refl]
    exact hprod m.support
  unfold evenPart
  exact (MvPolynomial.totalDegree_smul_le _ _).trans ((MvPolynomial.totalDegree_add _ _).trans (max_le le_rfl hsub))

private def expansionCoeff (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (D : ℕ) (p : P) (i l : ℕ) (T d : ℝ) : ℂ :=
  (evenPart (averagedPolynomial Φ D p (T, d))).coeff (Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l))

private theorem sum_coeff_even_eq_of_totalDegree_le (F : MvPolynomial (Fin 2) ℂ) {a : ℕ} (ha : F.totalDegree ≤ a)
    (x y : ℝ) :
    (∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
        F.coeff (Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l)) * ((x ^ (2 * i) * y ^ (2 * l) : ℝ) : ℂ)) =
      ∑ i ∈ Finset.range (F.totalDegree + 1), ∑ l ∈ Finset.range (F.totalDegree + 1 - i),
        F.coeff (Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l)) * ((x ^ (2 * i) * y ^ (2 * l) : ℝ) : ℂ) := by
  have hdeg : ∀ i l : ℕ,
      ∑ j ∈ (Finsupp.single (0 : Fin 2) (2 * i) + Finsupp.single (1 : Fin 2) (2 * l)).support,
        (Finsupp.single (0 : Fin 2) (2 * i) + Finsupp.single (1 : Fin 2) (2 * l)) j = 2 * i + 2 * l := by
    intro i l
    rw [Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => Finsupp.notMem_support_iff.1 hj)]
    simp [Fin.sum_univ_two, Finsupp.single_apply]
  have hz : ∀ i l : ℕ, F.totalDegree < 2 * i + 2 * l →
      F.coeff (Finsupp.single (0 : Fin 2) (2 * i) + Finsupp.single (1 : Fin 2) (2 * l)) = 0 := fun i l h =>
    MvPolynomial.coeff_eq_zero_of_totalDegree_lt (by rw [hdeg]; exact h)
  have hinner : ∀ i ∈ Finset.range (F.totalDegree + 1),
      (∑ l ∈ Finset.range (a + 1 - i),
        F.coeff (Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l)) * ((x ^ (2 * i) * y ^ (2 * l) : ℝ) : ℂ)) =
      ∑ l ∈ Finset.range (F.totalDegree + 1 - i),
        F.coeff (Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l)) * ((x ^ (2 * i) * y ^ (2 * l) : ℝ) : ℂ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hsub : Finset.range (F.totalDegree + 1 - i) ⊆ Finset.range (a + 1 - i) :=
      Finset.range_subset_range.2 (by omega)
    symm
    apply Finset.sum_subset hsub
    intro l hl hl'
    rw [Finset.mem_range] at hl hl'
    rw [hz i l (by omega), zero_mul]
  have houter : ∀ i ∈ Finset.range (a + 1), i ∉ Finset.range (F.totalDegree + 1) →
      (∑ l ∈ Finset.range (a + 1 - i),
        F.coeff (Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l)) * ((x ^ (2 * i) * y ^ (2 * l) : ℝ) : ℂ)) =
      0 := by
    intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    exact Finset.sum_eq_zero fun l _ => by rw [hz i l (by omega), zero_mul]
  have hsub : Finset.range (F.totalDegree + 1) ⊆ Finset.range (a + 1) := Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub houter]
  exact Finset.sum_congr rfl hinner

section Topology

variable [TopologicalSpace P]

private theorem exists_forall_apply_eq_zero_of_hasCompactSupport (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦc : HasCompactSupport Φ) :
    ∃ R : ℝ, ∀ (M : Fin 2 → Fin 2 → ℂ) (p : P),
      R < (Matrix.trace (Matrix.of M * (Matrix.of M).conjTranspose)).re → Φ (M, p) = 0 := by
  have hφ : Continuous fun q : (Fin 2 → Fin 2 → ℂ) × P =>
      (Matrix.trace (Matrix.of q.1 * (Matrix.of q.1).conjTranspose)).re := by
    have hof : Continuous fun q : (Fin 2 → Fin 2 → ℂ) × P => Matrix.of q.1 := continuous_fst
    exact Complex.continuous_re.comp (hof.matrix_mul hof.matrix_conjTranspose).matrix_trace
  obtain ⟨R, hR⟩ := ((hΦc : IsCompact (tsupport Φ)).image hφ).bddAbove
  refine ⟨R, fun M p hM => ?_⟩
  by_contra hne
  have hmem : (M, p) ∈ tsupport Φ := subset_tsupport Φ hne
  exact absurd (hR ⟨(M, p), hmem, rfl⟩) (not_le.2 hM)

private theorem preparedInput_apply_eq_zero (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) {R : ℝ}
    (hR : ∀ (M : Fin 2 → Fin 2 → ℂ) (p : P),
      R < (Matrix.trace (Matrix.of M * (Matrix.of M).conjTranspose)).re → Φ (M, p) = 0)
    (M : Fin 2 → Fin 2 → ℂ) (p : P) (hM : R < (Matrix.trace (Matrix.of M * (Matrix.of M).conjTranspose)).re) :
    preparedInput Φ (M, p) = 0 := by
  have _ := ‹TopologicalSpace P›
  have h0 : ∀ ψ : ℝ, Φ (fun i j => Complex.exp (-(2 * ψ * Complex.I)) * M i j, p) = 0 := by
    intro ψ
    have hc : Complex.exp (-(2 * ψ * Complex.I)) * star (Complex.exp (-(2 * ψ * Complex.I))) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        show -(2 * (ψ : ℂ) * Complex.I) = ((-(2 * ψ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
      simp
    apply hR
    have hM' : Matrix.of (fun i j => Complex.exp (-(2 * ψ * Complex.I)) * M i j) =
        Complex.exp (-(2 * ψ * Complex.I)) • Matrix.of M := by
      ext i j
      simp [Matrix.smul_apply]
    rw [hM', Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul, ← mul_assoc, hc, one_mul]
    exact hM
  simp only [preparedInput, h0, intervalIntegral.integral_zero, mul_zero]

private theorem twistedAverage_eq_of_isBalancedDecomposition (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦ : Continuous Φ) (p : P) {g k₁ k₂ : GL (Fin 2) ℂ} (h : IsBalancedDecomposition g k₁ k₂) :
    twistedAverage Φ p g =
      unitaryAverage fun u =>
        parameterSlice Φ p (u⁻¹ * (k₁⁻¹ * g * k₂⁻¹ * (k₂ * conjEntries k₁)) * conjEntries u) := by
  obtain ⟨hk₁, -, -, -⟩ := h
  have hF : Continuous fun u : GL (Fin 2) ℂ =>
      parameterSlice Φ p (u⁻¹ * (k₁⁻¹ * g * k₂⁻¹ * (k₂ * conjEntries k₁)) * conjEntries u) := by
    have hc : Continuous fun u : GL (Fin 2) ℂ =>
        ((u⁻¹ * (k₁⁻¹ * g * k₂⁻¹ * (k₂ * conjEntries k₁)) * conjEntries u : GL (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) := by
      simp only [Units.val_mul, ChartInvariance.conjEntries_coe]
      exact (Units.continuous_coe_inv.mul continuous_const).mul
        (Units.continuous_val.matrix_map Complex.continuous_conj)
    unfold parameterSlice
    exact hΦ.comp (hc.prodMk continuous_const)
  have h0 : star ((k₁⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((k₁⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [ChartInvariance.inv_coe_of_unitary hk₁, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    rw [Matrix.star_eq_conjTranspose] at hk₁
    exact mul_eq_one_comm.mp hk₁
  have h1 :
      star ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [Units.val_one, star_one, mul_one]
  have key := unitaryAverage_translate _ hF k₁⁻¹ 1 h0 h1
  unfold twistedAverage
  rw [← key]
  congr 1
  funext k
  simp only [mul_one]
  rw [twistedConj_eq_twistedConj_inv_mul g k₁ k₂ k]

private theorem unitaryAverage_twisted_eq_scalarFreeAverage (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦ₀ : IsScalarInvariant Φ) (p : P) (M : GL (Fin 2) ℂ) :
    unitaryAverage (fun u => parameterSlice Φ p (u⁻¹ * M * conjEntries u)) =
      scalarFreeAverage fun u => parameterSlice Φ p (u⁻¹ * M * conjEntries u) := by
  have _ := ‹TopologicalSpace P›
  apply unitaryAverage_eq_scalarFreeAverage
  intro ψ η ξ₁ ξ₂
  show parameterSlice Φ p ((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * M * conjEntries (unitaryElt ψ η ξ₁ ξ₂)) =
    parameterSlice Φ p ((unitaryElt 0 η ξ₁ ξ₂)⁻¹ * M * conjEntries (unitaryElt 0 η ξ₁ ξ₂))
  rw [unitaryElt_eq_scalarElt_mul ψ η ξ₁ ξ₂, scalarElt_mul_twisted]
  have hs : ∀ (c : ℂ) (hc : c ≠ 0) (A : Matrix (Fin 2) (Fin 2) ℂ),
      ((scalarElt c hc : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * A = fun i j => c * A i j := by
    intro c hc A
    ext i j
    simp [scalarElt, Matrix.scalar_apply, Matrix.diagonal_mul]
  have hn : ‖(Complex.exp (ψ * Complex.I))⁻¹ * (starRingEnd ℂ) (Complex.exp (ψ * Complex.I))‖ = 1 := by
    rw [norm_mul, norm_inv, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, inv_one, one_mul]
  unfold parameterSlice
  rw [Units.val_mul, hs]
  exact hΦ₀ _ hn (Matrix.of.symm ((((unitaryElt 0 η ξ₁ ξ₂)⁻¹ * M * conjEntries (unitaryElt 0 η ξ₁ ξ₂) :
    GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), p)

private theorem scalarFreeAverage_finset_sum {ι : Type} (s : Finset ι) (F : ι → GL (Fin 2) ℂ → ℂ)
    (hF : ∀ i ∈ s, Continuous (F i)) :
    scalarFreeAverage (fun h => ∑ i ∈ s, F i h) = ∑ i ∈ s, scalarFreeAverage (F i) := by
  classical
  suffices h : (∀ i ∈ s, Continuous (F i)) →
      scalarFreeAverage (fun h => ∑ i ∈ s, F i h) = ∑ i ∈ s, scalarFreeAverage (F i) ∧
        Continuous (fun h => ∑ i ∈ s, F i h) from (h hF).1
  refine Finset.induction_on s ?_ ?_
  · intro _
    refine ⟨by simp [scalarFreeAverage], ?_⟩
    simp only [Finset.sum_empty]
    exact continuous_const
  · intro a s ha ih hF
    obtain ⟨ih1, ih2⟩ := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have ha' : Continuous (F a) := hF a (Finset.mem_insert_self a s)
    simp only [Finset.sum_insert ha]
    exact ⟨by rw [scalarFreeAverage_add _ _ ha' ih2, ih1], ha'.add ih2⟩

private theorem twistedAverage_eq_eval_averagedPolynomial (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ)
    (hΦ₀ : IsScalarInvariant Φ) (D : ℕ) (Q : (Fin 2 → Fin 2 → ℂ) × P → MvPolynomial (Fin 2 × Fin 2) ℂ)
    (hQd : ∀ q, (Q q).totalDegree ≤ D)
    (hQm : ∀ m, (fun q => (Q q).coeff m) ∈ translateSpan Φ)
    (hQe : ∀ q (u : GL (Fin 2) ℂ), IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      groupTranslate Φ u q = MvPolynomial.eval (entries u) (Q q))
    (p : P) {g k₁ k₂ : GL (Fin 2) ℂ} (h : IsBalancedDecomposition g k₁ k₂) :
    twistedAverage Φ p g =
      MvPolynomial.eval
        ![((((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
          ((((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)]
        (averagedPolynomial Φ D p (invFrobSq g, invAbsDet g)) := by
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ × ℝ, q = (invFrobSq g, invAbsDet g) := ⟨_, rfl⟩
  have hq : q ∈ normDetCone := by
    rw [hqdef]
    exact ⟨two_mul_invAbsDet_le_invFrobSq g, invAbsDet_pos g⟩
  have _ := hQm
  have hd : 0 ≤ q.2 := hq.2.le
  have hT : 2 * q.2 ≤ q.1 := hq.1
  obtain ⟨σ, hσdef⟩ : ∃ σ : GL (Fin 2) ℂ, σ = diagonalElt q hq := ⟨_, rfl⟩
  have hσc : (σ : Matrix (Fin 2) (Fin 2) ℂ) = singularDiagonal q.1 q.2 := by
    rw [hσdef]
    rfl
  have hdetT : ∀ φ : ℝ,
      Matrix.det (Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)]) ≠ 0 := by
    intro φ
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    show Complex.exp (-(φ * Complex.I)) * Complex.exp (φ * Complex.I) ≠ 0
    rw [TorusAverage.exp_neg_mul_exp]
    exact one_ne_zero
  obtain ⟨rot, hrot⟩ : ∃ rot : ℝ → GL (Fin 2) ℂ, ∀ φ : ℝ, ((rot φ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] :=
    ⟨fun φ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdetT φ), fun φ => rfl⟩
  have hunit : ∀ t : ℝ, (starRingEnd ℂ) (Complex.exp (t * Complex.I)) * Complex.exp (t * Complex.I) = 1 := by
    intro t
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow,
      Complex.ofReal_one]
  have hneg : ∀ φ : ℝ, Complex.exp (-(φ * Complex.I)) = Complex.exp ((-φ : ℝ) * Complex.I) := by
    intro φ
    rw [Complex.ofReal_neg, neg_mul]
  have hrotU : ∀ φ : ℝ,
      star ((rot φ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((rot φ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        1 := by
    intro φ
    rw [hrot, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [Pi.star_apply, Matrix.cons_val_zero, hneg]
      exact hunit _
    · simp only [Pi.star_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact hunit _
  have hrotD : ∀ φ : ℝ, Matrix.det ((rot φ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    intro φ
    rw [hrot, Matrix.det_diagonal, Fin.prod_univ_two]
    exact TorusAverage.exp_neg_mul_exp φ
  have hTc : Continuous fun φ : ℝ =>
      Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] := by
    have h1 : Continuous fun φ : ℝ => Complex.exp (-(φ * Complex.I)) := by fun_prop
    have h2 : Continuous fun φ : ℝ => Complex.exp (φ * Complex.I) := by fun_prop
    exact Continuous.matrix_diagonal (h1.matrixVecCons (h2.matrixVecCons continuous_const))
  have hmulU : ∀ a b : GL (Fin 2) ℂ, star (a : Matrix (Fin 2) (Fin 2) ℂ) * (a : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      star (b : Matrix (Fin 2) (Fin 2) ℂ) * (b : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      star ((a * b : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((a * b : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        1 := by
    intro a b ha hb
    simp only [Units.val_mul, star_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (a : Matrix (Fin 2) (Fin 2) ℂ)), ha, Matrix.one_mul, hb]
  have hHc : ∀ W : GL (Fin 2) ℂ, Continuous fun y : ℝ × GL (Fin 2) ℂ =>
      parameterSlice Φ p (y.2⁻¹ * (σ * (rot y.1 * W * rot y.1)) * conjEntries y.2) := by
    intro W
    have hm : Continuous fun y : ℝ × GL (Fin 2) ℂ =>
        ((y.2⁻¹ * (σ * (rot y.1 * W * rot y.1)) * conjEntries y.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      simp only [Units.val_mul, hrot, ChartInvariance.conjEntries_coe]
      exact ((Units.continuous_coe_inv.comp continuous_snd).mul (continuous_const.mul
        (((hTc.comp continuous_fst).mul continuous_const).mul (hTc.comp continuous_fst)))).mul
        ((Units.continuous_val.comp continuous_snd).matrix_map Complex.continuous_conj)
    unfold parameterSlice
    exact hΦ.comp (hm.prodMk continuous_const)
  have hHc' : ∀ W : GL (Fin 2) ℂ, Continuous fun y : GL (Fin 2) ℂ × ℝ =>
      parameterSlice Φ p (y.1⁻¹ * (σ * (rot y.2 * W * rot y.2)) * conjEntries y.1) := by
    intro W
    have hm : Continuous fun y : GL (Fin 2) ℂ × ℝ =>
        ((y.1⁻¹ * (σ * (rot y.2 * W * rot y.2)) * conjEntries y.1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      simp only [Units.val_mul, hrot, ChartInvariance.conjEntries_coe]
      exact ((Units.continuous_coe_inv.comp continuous_fst).mul (continuous_const.mul
        (((hTc.comp continuous_snd).mul continuous_const).mul (hTc.comp continuous_snd)))).mul
        ((Units.continuous_val.comp continuous_fst).matrix_map Complex.continuous_conj)
    unfold parameterSlice
    exact hΦ.comp (hm.prodMk continuous_const)
  have hsc : ∀ (M : GL (Fin 2) ℂ) (ψ η ξ₁ ξ₂ : ℝ),
      parameterSlice Φ p ((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * M * conjEntries (unitaryElt ψ η ξ₁ ξ₂)) =
        parameterSlice Φ p ((unitaryElt 0 η ξ₁ ξ₂)⁻¹ * M * conjEntries (unitaryElt 0 η ξ₁ ξ₂)) := by
    intro M ψ η ξ₁ ξ₂
    rw [unitaryElt_eq_scalarElt_mul ψ η ξ₁ ξ₂, scalarElt_mul_twisted]
    have hs : ∀ (c : ℂ) (hc : c ≠ 0) (X : GL (Fin 2) ℂ),
        ((scalarElt c hc * X : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
          fun i j => c * (X : Matrix (Fin 2) (Fin 2) ℂ) i j := by
      intro c hc X
      ext i j
      simp [scalarElt, Matrix.scalar_apply, Matrix.diagonal_mul]
    have hn : ‖(Complex.exp (ψ * Complex.I))⁻¹ * (starRingEnd ℂ) (Complex.exp (ψ * Complex.I))‖ = 1 := by
      rw [norm_mul, norm_inv, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, inv_one, one_mul]
    unfold parameterSlice
    rw [hs]
    exact hΦ₀ _ hn (Matrix.of.symm ((((unitaryElt 0 η ξ₁ ξ₂)⁻¹ * M * conjEntries (unitaryElt 0 η ξ₁ ξ₂) :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), p)
  obtain ⟨Qu, hQu⟩ : ∃ Qu : GL (Fin 2) ℂ → MvPolynomial (Fin 2 × Fin 2) ℂ, ∀ u, Qu u =
      rightSubst ((conjEntries u : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        (Q (Matrix.of.symm ((u⁻¹ * σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), p)) := ⟨_, fun u => rfl⟩
  have hQud : ∀ u, (Qu u).totalDegree ≤ D := by
    intro u
    rw [hQu]
    exact (totalDegree_rightSubst_le _ _).trans (hQd _)
  obtain ⟨Ff, hFdeg, hFspec⟩ : ∃ Ff : GL (Fin 2) ℂ → MvPolynomial (Fin 2) ℂ, (∀ u, (Ff u).totalDegree ≤ D) ∧
      ∀ (u : GL (Fin 2) ℂ) (W : Matrix (Fin 2) (Fin 2) ℂ), star W * W = 1 → Matrix.det W = 1 →
        (1 / (2 * Real.pi) : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
          MvPolynomial.eval (fun ij : Fin 2 × Fin 2 =>
            (Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] * W *
              Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)]) ij.1 ij.2) (Qu u) =
          MvPolynomial.eval ![((W 0 1).re : ℂ), ((W 0 1).im : ℂ)] (Ff u) := by
    choose Ff hFf using fun u : GL (Fin 2) ℂ =>
      TorusAverage.exists_mvPolynomial_eval_re_im_eq_integral_eval_torus_conj (Qu u)
    exact ⟨Ff, fun u => (hFf u).1.trans (hQud u), fun u => (hFf u).2⟩
  have hmem : ∀ u, Ff u ∈ MvPolynomial.restrictDegree (Fin 2) ℂ D := by
    intro u
    exact MvPolynomial.restrictTotalDegree_le_restrictDegree (Fin 2) ℂ D (by
      rw [MvPolynomial.mem_restrictTotalDegree]
      exact hFdeg u)
  have hpt : ∀ (W u : GL (Fin 2) ℂ) (φ : ℝ), star (W : Matrix (Fin 2) (Fin 2) ℂ) * (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      Matrix.det (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 → IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      parameterSlice Φ p (u⁻¹ * (σ * (rot φ * W * rot φ)) * conjEntries u) =
        MvPolynomial.eval (fun ij : Fin 2 × Fin 2 =>
          (Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] *
              (W : Matrix (Fin 2) (Fin 2) ℂ) *
            Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)]) ij.1 ij.2) (Qu u) := by
    intro W u φ hW hWd hu hud
    have hiso : IsIsometry (rot φ * W * rot φ * conjEntries u) :=
      hmulU _ _ (hmulU _ _ (hmulU _ _ (hrotU φ) hW) (hrotU φ)) (star_mul_self_conjEntries u hu)
    have hdet1 : Matrix.det ((rot φ * W * rot φ * conjEntries u : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      simp only [Units.val_mul, Matrix.det_mul, hrotD, hWd, det_conjEntries, hud, map_one, mul_one]
    have key := hQe (Matrix.of.symm ((u⁻¹ * σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), p) _ hiso hdet1
    have lhs : parameterSlice Φ p (u⁻¹ * (σ * (rot φ * W * rot φ)) * conjEntries u) =
        groupTranslate Φ (rot φ * W * rot φ * conjEntries u)
          (Matrix.of.symm ((u⁻¹ * σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), p) := by
      unfold parameterSlice groupTranslate
      simp only [Equiv.apply_symm_apply, Units.val_mul, Matrix.mul_assoc]
    rw [lhs, key]
    unfold entries
    rw [hQu, eval_rightSubst]
    simp only [Units.val_mul, hrot]
  have hval : ∀ (W u : GL (Fin 2) ℂ), star (W : Matrix (Fin 2) (Fin 2) ℂ) * (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      Matrix.det (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      (1 / (2 * Real.pi) : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
          parameterSlice Φ p (u⁻¹ * (σ * (rot φ * W * rot φ)) * conjEntries u) =
        MvPolynomial.eval ![((((W : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
          ((((W : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)] (Ff u) := by
    intro W u hW hWd hu hud
    have hI : (∫ φ in (0 : ℝ)..(2 * Real.pi), parameterSlice Φ p (u⁻¹ * (σ * (rot φ * W * rot φ)) * conjEntries u)) =
        ∫ φ in (0 : ℝ)..(2 * Real.pi), MvPolynomial.eval (fun ij : Fin 2 × Fin 2 =>
          (Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] *
              (W : Matrix (Fin 2) (Fin 2) ℂ) *
            Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)]) ij.1 ij.2) (Qu u) :=
      intervalIntegral.integral_congr fun φ _ => hpt W u φ hW hWd hu hud
    rw [hI]
    exact hFspec u (W : Matrix (Fin 2) (Fin 2) ℂ) hW hWd
  obtain ⟨V, hV⟩ : ∃ V : GL (Fin 2) ℂ → ↥(grid D) → ℂ, ∀ u x, V u x = (1 / (2 * Real.pi) : ℂ) *
      ∫ φ in (0 : ℝ)..(2 * Real.pi), parameterSlice Φ p (u⁻¹ * (σ * (rot φ *
        discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2) * rot φ)) * conjEntries u) :=
    ⟨_, fun u x => rfl⟩
  have hdisc : ∀ x : ↥(grid D),
      star ((discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2) : GL (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) *
          ((discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2) : GL (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
        Matrix.det ((discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2) : GL (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    intro x
    have hb := isBalancedDecomposition_diagonalElt_mul_discElt q hq _ _ (sq_add_sq_le_one_of_mem_grid D _ x.2)
    unfold IsBalancedDecomposition at hb
    refine ⟨hb.2.1, ?_⟩
    have h3 := hb.2.2.1
    rw [Units.val_one, Matrix.det_one] at h3
    exact h3.symm
  have hre : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * Complex.I).re = a := by
    intro a b
    simp
  have him : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by
    intro a b
    simp
  have hVval : ∀ (x : ↥(grid D)) (u : GL (Fin 2) ℂ), IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      V u x = MvPolynomial.eval ![(((x : ℝ × ℝ).1 : ℝ) : ℂ), (((x : ℝ × ℝ).2 : ℝ) : ℂ)] (Ff u) := by
    intro x u hu hud
    rw [hV, hval _ u (hdisc x).1 (hdisc x).2 hu hud, discElt_apply_zero_one, hre, him]
  have hVc : ∀ x : ↥(grid D), Continuous fun u : GL (Fin 2) ℂ => V u x := by
    intro x
    simp only [hV]
    exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (u : GL (Fin 2) ℂ) (φ : ℝ) => parameterSlice Φ p (u⁻¹ * (σ * (rot φ *
        discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2) * rot φ)) * conjEntries u))
      (hHc' (discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2))) 0 (2 * Real.pi))
  have hsfa : ∀ F G : GL (Fin 2) ℂ → ℂ,
      (∀ u, IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 → F u = G u) →
      scalarFreeAverage F = scalarFreeAverage G := by
    intro F G hFG
    unfold scalarFreeAverage
    congr 1
    refine intervalIntegral.integral_congr fun η _ => ?_
    refine intervalIntegral.integral_congr fun ξ₁ _ => ?_
    refine intervalIntegral.integral_congr fun ξ₂ _ => ?_
    show (Real.sin η * Real.cos η : ℂ) * F (unitaryElt 0 η ξ₁ ξ₂) =
      (Real.sin η * Real.cos η : ℂ) * G (unitaryElt 0 η ξ₁ ξ₂)
    rw [hFG _ (isIsometry_unitaryElt 0 η ξ₁ ξ₂) (det_unitaryElt_zero η ξ₁ ξ₂)]
  have hlin : ∀ (pt : Fin 2 → ℂ) (v : ↥(grid D) → ℂ), MvPolynomial.eval pt (reconstruct D v) =
      ∑ x, v x * MvPolynomial.eval pt (reconstruct D fun j => if x = j then 1 else 0) := by
    intro pt v
    have hl := LinearMap.pi_apply_eq_sum_univ ((MvPolynomial.aeval pt).toLinearMap ∘ₗ reconstruct D) v
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, smul_eq_mul] at hl
    exact hl
  obtain ⟨Pstar, hPdef⟩ : ∃ P' : MvPolynomial (Fin 2) ℂ,
      P' = reconstruct D fun x => scalarFreeAverage fun u => V u x := ⟨_, rfl⟩
  have hPmem : Pstar ∈ MvPolynomial.restrictDegree (Fin 2) ℂ D := by
    rw [hPdef]
    exact reconstruct_mem_restrictDegree D _
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have h1U :
      star ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [Units.val_one, star_one, one_mul]
  have hc1 : conjEntries (1 : GL (Fin 2) ℂ) = 1 := by
    unfold conjEntries
    exact map_one _
  have core : ∀ w : GL (Fin 2) ℂ, star (w : Matrix (Fin 2) (Fin 2) ℂ) * (w : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      Matrix.det (w : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      twistedAverage Φ p (σ * w) = MvPolynomial.eval ![((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
        ((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)] Pstar := by
    intro w hw hwd
    have hσw : ((σ * w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal q.1 q.2 *
          (w : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [Units.val_mul, Units.val_one, one_mul, hσc]
    have hF1 : invFrobSq (σ * w) = q.1 := by
      rw [invFrobSq_eq_of_coe_eq h1U hw hσw, re_trace_singularDiagonal_mul_conjTranspose _ _ hd hT]
    have hA1 : invAbsDet (σ * w) = q.2 := by
      rw [invAbsDet_eq_of_coe_eq h1U hw hσw, norm_det_singularDiagonal _ _ hd hT]
    have hbal : IsBalancedDecomposition (σ * w) 1 w := by
      unfold IsBalancedDecomposition
      refine ⟨h1U, hw, ?_, ?_⟩
      · rw [Units.val_one, Matrix.det_one, hwd]
      · rw [hF1, hA1]
        exact hσw
    have hconst : ∀ φ : ℝ, twistedAverage Φ p (σ * (rot φ * w * rot φ)) = twistedAverage Φ p (σ * w) := by
      intro φ
      obtain ⟨k₁', k₂', hbal', hw'⟩ := hbal.torus φ
      have e1 : k₁'⁻¹ * (σ * w) * k₂'⁻¹ = σ := by
        apply Units.ext
        have hb := hbal'
        unfold IsBalancedDecomposition at hb
        rw [coe_inv_mul_mul_inv_eq_singularDiagonal (σ * w) k₁' k₂' hb.2.2.2, hF1, hA1, hσc]
      rw [hc1, mul_one] at hw'
      have e2 : k₂' * conjEntries k₁' = rot φ * w * rot φ := by
        apply Units.ext
        rw [hw', Units.val_mul, Units.val_mul, hrot]
      rw [twistedAverage_eq_of_isBalancedDecomposition Φ hΦ p hbal', e1, e2]
      rfl
    have hfub : unitaryAverage (fun u => ∫ φ in (0 : ℝ)..(2 * Real.pi),
        parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) =
        ∫ φ in (0 : ℝ)..(2 * Real.pi), twistedAverage Φ p (σ * (rot φ * w * rot φ)) :=
      unitaryAverage_intervalIntegral 0 (2 * Real.pi)
        (fun φ u => parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) (hHc w)
    simp only [hconst, intervalIntegral.integral_const, sub_zero] at hfub
    have hfub' : unitaryAverage (fun u => ∫ φ in (0 : ℝ)..(2 * Real.pi),
        parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) =
        ((2 * Real.pi : ℝ) : ℂ) * twistedAverage Φ p (σ * w) := hfub
    have hstep : twistedAverage Φ p (σ * w) = (1 / (2 * Real.pi) : ℂ) * unitaryAverage (fun u =>
        ∫ φ in (0 : ℝ)..(2 * Real.pi), parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) := by
      rw [hfub', Complex.ofReal_mul, Complex.ofReal_ofNat, one_div, ← mul_assoc, inv_mul_cancel₀ h2π, one_mul]
    have hblind : unitaryAverage (fun u => ∫ φ in (0 : ℝ)..(2 * Real.pi),
        parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) =
        scalarFreeAverage (fun u => ∫ φ in (0 : ℝ)..(2 * Real.pi),
          parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) := by
      apply unitaryAverage_eq_scalarFreeAverage
      intro ψ η ξ₁ ξ₂
      refine intervalIntegral.integral_congr fun φ _ => ?_
      exact hsc (σ * (rot φ * w * rot φ)) ψ η ξ₁ ξ₂
    calc twistedAverage Φ p (σ * w)
        = (1 / (2 * Real.pi) : ℂ) * scalarFreeAverage (fun u => ∫ φ in (0 : ℝ)..(2 * Real.pi),
            parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) := by rw [hstep, hblind]
      _ = scalarFreeAverage (fun u => (1 / (2 * Real.pi) : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
            parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) :=
          (scalarFreeAverage_const_mul _ _).symm
      _ = scalarFreeAverage (fun u => ∑ x : ↥(grid D), V u x *
            MvPolynomial.eval ![((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
              ((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)]
              (reconstruct D fun j => if x = j then 1 else 0)) := by
          refine hsfa _ _ fun u hu hud => ?_
          rw [hval w u hw hwd hu hud, ← reconstruct_eval D (Ff u) (hmem u), hlin]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hVval x u hu hud]
      _ = ∑ x : ↥(grid D), scalarFreeAverage (fun u => V u x *
            MvPolynomial.eval ![((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
              ((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)]
              (reconstruct D fun j => if x = j then 1 else 0)) :=
          scalarFreeAverage_finset_sum Finset.univ (fun x u => V u x *
            MvPolynomial.eval ![((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
              ((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)]
              (reconstruct D fun j => if x = j then 1 else 0)) fun x _ => (hVc x).mul continuous_const
      _ = ∑ x : ↥(grid D), (scalarFreeAverage fun u => V u x) *
            MvPolynomial.eval ![((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
              ((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)]
              (reconstruct D fun j => if x = j then 1 else 0) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [mul_comm (scalarFreeAverage fun u => V u x), ← scalarFreeAverage_const_mul]
          congr 1
          funext u
          exact mul_comm _ _
      _ = MvPolynomial.eval ![((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
            ((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)] Pstar := by
          rw [hPdef, hlin]
  have hP : averagedPolynomial Φ D p q = Pstar := by
    unfold averagedPolynomial
    rw [dif_pos hq, ← hσdef]
    have hx : ∀ x : ↥(grid D),
        twistedAverage Φ p (σ * discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2)) =
        MvPolynomial.eval ![(((x : ℝ × ℝ).1 : ℝ) : ℂ), (((x : ℝ × ℝ).2 : ℝ) : ℂ)] Pstar := by
      intro x
      rw [core _ (hdisc x).1 (hdisc x).2, discElt_apply_zero_one, hre, him]
    simp only [hx]
    exact reconstruct_eval D Pstar hPmem
  have hq1 : q.1 = invFrobSq g := by
    rw [hqdef]
  have hq2 : q.2 = invAbsDet g := by
    rw [hqdef]
  have e0 : k₁⁻¹ * g * k₂⁻¹ = σ := by
    apply Units.ext
    have hb := h
    unfold IsBalancedDecomposition at hb
    rw [coe_inv_mul_mul_inv_eq_singularDiagonal g k₁ k₂ hb.2.2.2, hσc, hq1, hq2]
  rw [twistedAverage_eq_of_isBalancedDecomposition Φ hΦ p h, e0, ← hqdef, hP]
  exact core _ h.star_mul_self h.det_eq_one

private theorem totalDegree_averagedPolynomial_le (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ)
    (hΦ₀ : IsScalarInvariant Φ) (D : ℕ) (Q : (Fin 2 → Fin 2 → ℂ) × P → MvPolynomial (Fin 2 × Fin 2) ℂ)
    (hQd : ∀ q, (Q q).totalDegree ≤ D)
    (hQm : ∀ m, (fun q => (Q q).coeff m) ∈ translateSpan Φ)
    (hQe : ∀ q (u : GL (Fin 2) ℂ), IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      groupTranslate Φ u q = MvPolynomial.eval (entries u) (Q q))
    (p : P) (q : ℝ × ℝ) : (averagedPolynomial Φ D p q).totalDegree ≤ D := by
  by_cases hq : q ∈ normDetCone
  swap
  · unfold averagedPolynomial
    rw [dif_neg hq, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  have _ := hQm
  have hd : 0 ≤ q.2 := hq.2.le
  have hT : 2 * q.2 ≤ q.1 := hq.1
  obtain ⟨σ, hσdef⟩ : ∃ σ : GL (Fin 2) ℂ, σ = diagonalElt q hq := ⟨_, rfl⟩
  have hσc : (σ : Matrix (Fin 2) (Fin 2) ℂ) = singularDiagonal q.1 q.2 := by
    rw [hσdef]
    rfl
  have hdetT : ∀ φ : ℝ,
      Matrix.det (Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)]) ≠ 0 := by
    intro φ
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    show Complex.exp (-(φ * Complex.I)) * Complex.exp (φ * Complex.I) ≠ 0
    rw [TorusAverage.exp_neg_mul_exp]
    exact one_ne_zero
  obtain ⟨rot, hrot⟩ : ∃ rot : ℝ → GL (Fin 2) ℂ, ∀ φ : ℝ, ((rot φ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] :=
    ⟨fun φ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdetT φ), fun φ => rfl⟩
  have hunit : ∀ t : ℝ, (starRingEnd ℂ) (Complex.exp (t * Complex.I)) * Complex.exp (t * Complex.I) = 1 := by
    intro t
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow,
      Complex.ofReal_one]
  have hneg : ∀ φ : ℝ, Complex.exp (-(φ * Complex.I)) = Complex.exp ((-φ : ℝ) * Complex.I) := by
    intro φ
    rw [Complex.ofReal_neg, neg_mul]
  have hrotU : ∀ φ : ℝ,
      star ((rot φ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((rot φ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        1 := by
    intro φ
    rw [hrot, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [Pi.star_apply, Matrix.cons_val_zero, hneg]
      exact hunit _
    · simp only [Pi.star_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact hunit _
  have hrotD : ∀ φ : ℝ, Matrix.det ((rot φ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    intro φ
    rw [hrot, Matrix.det_diagonal, Fin.prod_univ_two]
    exact TorusAverage.exp_neg_mul_exp φ
  have hTc : Continuous fun φ : ℝ =>
      Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] := by
    have h1 : Continuous fun φ : ℝ => Complex.exp (-(φ * Complex.I)) := by fun_prop
    have h2 : Continuous fun φ : ℝ => Complex.exp (φ * Complex.I) := by fun_prop
    exact Continuous.matrix_diagonal (h1.matrixVecCons (h2.matrixVecCons continuous_const))
  have hmulU : ∀ a b : GL (Fin 2) ℂ, star (a : Matrix (Fin 2) (Fin 2) ℂ) * (a : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      star (b : Matrix (Fin 2) (Fin 2) ℂ) * (b : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      star ((a * b : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((a * b : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        1 := by
    intro a b ha hb
    simp only [Units.val_mul, star_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (a : Matrix (Fin 2) (Fin 2) ℂ)), ha, Matrix.one_mul, hb]
  have hHc : ∀ W : GL (Fin 2) ℂ, Continuous fun y : ℝ × GL (Fin 2) ℂ =>
      parameterSlice Φ p (y.2⁻¹ * (σ * (rot y.1 * W * rot y.1)) * conjEntries y.2) := by
    intro W
    have hm : Continuous fun y : ℝ × GL (Fin 2) ℂ =>
        ((y.2⁻¹ * (σ * (rot y.1 * W * rot y.1)) * conjEntries y.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      simp only [Units.val_mul, hrot, ChartInvariance.conjEntries_coe]
      exact ((Units.continuous_coe_inv.comp continuous_snd).mul (continuous_const.mul
        (((hTc.comp continuous_fst).mul continuous_const).mul (hTc.comp continuous_fst)))).mul
        ((Units.continuous_val.comp continuous_snd).matrix_map Complex.continuous_conj)
    unfold parameterSlice
    exact hΦ.comp (hm.prodMk continuous_const)
  have hHc' : ∀ W : GL (Fin 2) ℂ, Continuous fun y : GL (Fin 2) ℂ × ℝ =>
      parameterSlice Φ p (y.1⁻¹ * (σ * (rot y.2 * W * rot y.2)) * conjEntries y.1) := by
    intro W
    have hm : Continuous fun y : GL (Fin 2) ℂ × ℝ =>
        ((y.1⁻¹ * (σ * (rot y.2 * W * rot y.2)) * conjEntries y.1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      simp only [Units.val_mul, hrot, ChartInvariance.conjEntries_coe]
      exact ((Units.continuous_coe_inv.comp continuous_fst).mul (continuous_const.mul
        (((hTc.comp continuous_snd).mul continuous_const).mul (hTc.comp continuous_snd)))).mul
        ((Units.continuous_val.comp continuous_fst).matrix_map Complex.continuous_conj)
    unfold parameterSlice
    exact hΦ.comp (hm.prodMk continuous_const)
  have hsc : ∀ (M : GL (Fin 2) ℂ) (ψ η ξ₁ ξ₂ : ℝ),
      parameterSlice Φ p ((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * M * conjEntries (unitaryElt ψ η ξ₁ ξ₂)) =
        parameterSlice Φ p ((unitaryElt 0 η ξ₁ ξ₂)⁻¹ * M * conjEntries (unitaryElt 0 η ξ₁ ξ₂)) := by
    intro M ψ η ξ₁ ξ₂
    rw [unitaryElt_eq_scalarElt_mul ψ η ξ₁ ξ₂, scalarElt_mul_twisted]
    have hs : ∀ (c : ℂ) (hc : c ≠ 0) (X : GL (Fin 2) ℂ),
        ((scalarElt c hc * X : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
          fun i j => c * (X : Matrix (Fin 2) (Fin 2) ℂ) i j := by
      intro c hc X
      ext i j
      simp [scalarElt, Matrix.scalar_apply, Matrix.diagonal_mul]
    have hn : ‖(Complex.exp (ψ * Complex.I))⁻¹ * (starRingEnd ℂ) (Complex.exp (ψ * Complex.I))‖ = 1 := by
      rw [norm_mul, norm_inv, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, inv_one, one_mul]
    unfold parameterSlice
    rw [hs]
    exact hΦ₀ _ hn (Matrix.of.symm ((((unitaryElt 0 η ξ₁ ξ₂)⁻¹ * M * conjEntries (unitaryElt 0 η ξ₁ ξ₂) :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), p)
  obtain ⟨Qu, hQu⟩ : ∃ Qu : GL (Fin 2) ℂ → MvPolynomial (Fin 2 × Fin 2) ℂ, ∀ u, Qu u =
      rightSubst ((conjEntries u : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        (Q (Matrix.of.symm ((u⁻¹ * σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), p)) := ⟨_, fun u => rfl⟩
  have hQud : ∀ u, (Qu u).totalDegree ≤ D := by
    intro u
    rw [hQu]
    exact (totalDegree_rightSubst_le _ _).trans (hQd _)
  obtain ⟨Ff, hFdeg, hFspec⟩ : ∃ Ff : GL (Fin 2) ℂ → MvPolynomial (Fin 2) ℂ, (∀ u, (Ff u).totalDegree ≤ D) ∧
      ∀ (u : GL (Fin 2) ℂ) (W : Matrix (Fin 2) (Fin 2) ℂ), star W * W = 1 → Matrix.det W = 1 →
        (1 / (2 * Real.pi) : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
          MvPolynomial.eval (fun ij : Fin 2 × Fin 2 =>
            (Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] * W *
              Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)]) ij.1 ij.2) (Qu u) =
          MvPolynomial.eval ![((W 0 1).re : ℂ), ((W 0 1).im : ℂ)] (Ff u) := by
    choose Ff hFf using fun u : GL (Fin 2) ℂ =>
      TorusAverage.exists_mvPolynomial_eval_re_im_eq_integral_eval_torus_conj (Qu u)
    exact ⟨Ff, fun u => (hFf u).1.trans (hQud u), fun u => (hFf u).2⟩
  have hmem : ∀ u, Ff u ∈ MvPolynomial.restrictDegree (Fin 2) ℂ D := by
    intro u
    exact MvPolynomial.restrictTotalDegree_le_restrictDegree (Fin 2) ℂ D (by
      rw [MvPolynomial.mem_restrictTotalDegree]
      exact hFdeg u)
  have hpt : ∀ (W u : GL (Fin 2) ℂ) (φ : ℝ), star (W : Matrix (Fin 2) (Fin 2) ℂ) * (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      Matrix.det (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 → IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      parameterSlice Φ p (u⁻¹ * (σ * (rot φ * W * rot φ)) * conjEntries u) =
        MvPolynomial.eval (fun ij : Fin 2 × Fin 2 =>
          (Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] *
              (W : Matrix (Fin 2) (Fin 2) ℂ) *
            Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)]) ij.1 ij.2) (Qu u) := by
    intro W u φ hW hWd hu hud
    have hiso : IsIsometry (rot φ * W * rot φ * conjEntries u) :=
      hmulU _ _ (hmulU _ _ (hmulU _ _ (hrotU φ) hW) (hrotU φ)) (star_mul_self_conjEntries u hu)
    have hdet1 : Matrix.det ((rot φ * W * rot φ * conjEntries u : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      simp only [Units.val_mul, Matrix.det_mul, hrotD, hWd, det_conjEntries, hud, map_one, mul_one]
    have key := hQe (Matrix.of.symm ((u⁻¹ * σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), p) _ hiso hdet1
    have lhs : parameterSlice Φ p (u⁻¹ * (σ * (rot φ * W * rot φ)) * conjEntries u) =
        groupTranslate Φ (rot φ * W * rot φ * conjEntries u)
          (Matrix.of.symm ((u⁻¹ * σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), p) := by
      unfold parameterSlice groupTranslate
      simp only [Equiv.apply_symm_apply, Units.val_mul, Matrix.mul_assoc]
    rw [lhs, key]
    unfold entries
    rw [hQu, eval_rightSubst]
    simp only [Units.val_mul, hrot]
  have hval : ∀ (W u : GL (Fin 2) ℂ), star (W : Matrix (Fin 2) (Fin 2) ℂ) * (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      Matrix.det (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      (1 / (2 * Real.pi) : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
          parameterSlice Φ p (u⁻¹ * (σ * (rot φ * W * rot φ)) * conjEntries u) =
        MvPolynomial.eval ![((((W : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
          ((((W : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)] (Ff u) := by
    intro W u hW hWd hu hud
    have hI : (∫ φ in (0 : ℝ)..(2 * Real.pi), parameterSlice Φ p (u⁻¹ * (σ * (rot φ * W * rot φ)) * conjEntries u)) =
        ∫ φ in (0 : ℝ)..(2 * Real.pi), MvPolynomial.eval (fun ij : Fin 2 × Fin 2 =>
          (Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)] *
              (W : Matrix (Fin 2) (Fin 2) ℂ) *
            Matrix.diagonal ![Complex.exp (-(φ * Complex.I)), Complex.exp (φ * Complex.I)]) ij.1 ij.2) (Qu u) :=
      intervalIntegral.integral_congr fun φ _ => hpt W u φ hW hWd hu hud
    rw [hI]
    exact hFspec u (W : Matrix (Fin 2) (Fin 2) ℂ) hW hWd
  obtain ⟨V, hV⟩ : ∃ V : GL (Fin 2) ℂ → ↥(grid D) → ℂ, ∀ u x, V u x = (1 / (2 * Real.pi) : ℂ) *
      ∫ φ in (0 : ℝ)..(2 * Real.pi), parameterSlice Φ p (u⁻¹ * (σ * (rot φ *
        discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2) * rot φ)) * conjEntries u) :=
    ⟨_, fun u x => rfl⟩
  have hdisc : ∀ x : ↥(grid D),
      star ((discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2) : GL (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) *
          ((discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2) : GL (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
        Matrix.det ((discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2) : GL (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    intro x
    have hb := isBalancedDecomposition_diagonalElt_mul_discElt q hq _ _ (sq_add_sq_le_one_of_mem_grid D _ x.2)
    unfold IsBalancedDecomposition at hb
    refine ⟨hb.2.1, ?_⟩
    have h3 := hb.2.2.1
    rw [Units.val_one, Matrix.det_one] at h3
    exact h3.symm
  have hre : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * Complex.I).re = a := by
    intro a b
    simp
  have him : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by
    intro a b
    simp
  have hVval : ∀ (x : ↥(grid D)) (u : GL (Fin 2) ℂ), IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      V u x = MvPolynomial.eval ![(((x : ℝ × ℝ).1 : ℝ) : ℂ), (((x : ℝ × ℝ).2 : ℝ) : ℂ)] (Ff u) := by
    intro x u hu hud
    rw [hV, hval _ u (hdisc x).1 (hdisc x).2 hu hud, discElt_apply_zero_one, hre, him]
  have hVc : ∀ x : ↥(grid D), Continuous fun u : GL (Fin 2) ℂ => V u x := by
    intro x
    simp only [hV]
    exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (u : GL (Fin 2) ℂ) (φ : ℝ) => parameterSlice Φ p (u⁻¹ * (σ * (rot φ *
        discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2) * rot φ)) * conjEntries u))
      (hHc' (discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2))) 0 (2 * Real.pi))
  have hsfa : ∀ F G : GL (Fin 2) ℂ → ℂ,
      (∀ u, IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 → F u = G u) →
      scalarFreeAverage F = scalarFreeAverage G := by
    intro F G hFG
    unfold scalarFreeAverage
    congr 1
    refine intervalIntegral.integral_congr fun η _ => ?_
    refine intervalIntegral.integral_congr fun ξ₁ _ => ?_
    refine intervalIntegral.integral_congr fun ξ₂ _ => ?_
    show (Real.sin η * Real.cos η : ℂ) * F (unitaryElt 0 η ξ₁ ξ₂) =
      (Real.sin η * Real.cos η : ℂ) * G (unitaryElt 0 η ξ₁ ξ₂)
    rw [hFG _ (isIsometry_unitaryElt 0 η ξ₁ ξ₂) (det_unitaryElt_zero η ξ₁ ξ₂)]
  have hlin : ∀ (pt : Fin 2 → ℂ) (v : ↥(grid D) → ℂ), MvPolynomial.eval pt (reconstruct D v) =
      ∑ x, v x * MvPolynomial.eval pt (reconstruct D fun j => if x = j then 1 else 0) := by
    intro pt v
    have hl := LinearMap.pi_apply_eq_sum_univ ((MvPolynomial.aeval pt).toLinearMap ∘ₗ reconstruct D) v
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, smul_eq_mul] at hl
    exact hl
  obtain ⟨Pstar, hPdef⟩ : ∃ P' : MvPolynomial (Fin 2) ℂ,
      P' = reconstruct D fun x => scalarFreeAverage fun u => V u x := ⟨_, rfl⟩
  have hPmem : Pstar ∈ MvPolynomial.restrictDegree (Fin 2) ℂ D := by
    rw [hPdef]
    exact reconstruct_mem_restrictDegree D _
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have h1U :
      star ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [Units.val_one, star_one, one_mul]
  have hc1 : conjEntries (1 : GL (Fin 2) ℂ) = 1 := by
    unfold conjEntries
    exact map_one _
  have core : ∀ w : GL (Fin 2) ℂ, star (w : Matrix (Fin 2) (Fin 2) ℂ) * (w : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      Matrix.det (w : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      twistedAverage Φ p (σ * w) = MvPolynomial.eval ![((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
        ((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)] Pstar := by
    intro w hw hwd
    have hσw : ((σ * w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * singularDiagonal q.1 q.2 *
          (w : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [Units.val_mul, Units.val_one, one_mul, hσc]
    have hF1 : invFrobSq (σ * w) = q.1 := by
      rw [invFrobSq_eq_of_coe_eq h1U hw hσw, re_trace_singularDiagonal_mul_conjTranspose _ _ hd hT]
    have hA1 : invAbsDet (σ * w) = q.2 := by
      rw [invAbsDet_eq_of_coe_eq h1U hw hσw, norm_det_singularDiagonal _ _ hd hT]
    have hbal : IsBalancedDecomposition (σ * w) 1 w := by
      unfold IsBalancedDecomposition
      refine ⟨h1U, hw, ?_, ?_⟩
      · rw [Units.val_one, Matrix.det_one, hwd]
      · rw [hF1, hA1]
        exact hσw
    have hconst : ∀ φ : ℝ, twistedAverage Φ p (σ * (rot φ * w * rot φ)) = twistedAverage Φ p (σ * w) := by
      intro φ
      obtain ⟨k₁', k₂', hbal', hw'⟩ := hbal.torus φ
      have e1 : k₁'⁻¹ * (σ * w) * k₂'⁻¹ = σ := by
        apply Units.ext
        have hb := hbal'
        unfold IsBalancedDecomposition at hb
        rw [coe_inv_mul_mul_inv_eq_singularDiagonal (σ * w) k₁' k₂' hb.2.2.2, hF1, hA1, hσc]
      rw [hc1, mul_one] at hw'
      have e2 : k₂' * conjEntries k₁' = rot φ * w * rot φ := by
        apply Units.ext
        rw [hw', Units.val_mul, Units.val_mul, hrot]
      rw [twistedAverage_eq_of_isBalancedDecomposition Φ hΦ p hbal', e1, e2]
      rfl
    have hfub : unitaryAverage (fun u => ∫ φ in (0 : ℝ)..(2 * Real.pi),
        parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) =
        ∫ φ in (0 : ℝ)..(2 * Real.pi), twistedAverage Φ p (σ * (rot φ * w * rot φ)) :=
      unitaryAverage_intervalIntegral 0 (2 * Real.pi)
        (fun φ u => parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) (hHc w)
    simp only [hconst, intervalIntegral.integral_const, sub_zero] at hfub
    have hfub' : unitaryAverage (fun u => ∫ φ in (0 : ℝ)..(2 * Real.pi),
        parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) =
        ((2 * Real.pi : ℝ) : ℂ) * twistedAverage Φ p (σ * w) := hfub
    have hstep : twistedAverage Φ p (σ * w) = (1 / (2 * Real.pi) : ℂ) * unitaryAverage (fun u =>
        ∫ φ in (0 : ℝ)..(2 * Real.pi), parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) := by
      rw [hfub', Complex.ofReal_mul, Complex.ofReal_ofNat, one_div, ← mul_assoc, inv_mul_cancel₀ h2π, one_mul]
    have hblind : unitaryAverage (fun u => ∫ φ in (0 : ℝ)..(2 * Real.pi),
        parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) =
        scalarFreeAverage (fun u => ∫ φ in (0 : ℝ)..(2 * Real.pi),
          parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) := by
      apply unitaryAverage_eq_scalarFreeAverage
      intro ψ η ξ₁ ξ₂
      refine intervalIntegral.integral_congr fun φ _ => ?_
      exact hsc (σ * (rot φ * w * rot φ)) ψ η ξ₁ ξ₂
    calc twistedAverage Φ p (σ * w)
        = (1 / (2 * Real.pi) : ℂ) * scalarFreeAverage (fun u => ∫ φ in (0 : ℝ)..(2 * Real.pi),
            parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) := by rw [hstep, hblind]
      _ = scalarFreeAverage (fun u => (1 / (2 * Real.pi) : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
            parameterSlice Φ p (u⁻¹ * (σ * (rot φ * w * rot φ)) * conjEntries u)) :=
          (scalarFreeAverage_const_mul _ _).symm
      _ = scalarFreeAverage (fun u => ∑ x : ↥(grid D), V u x *
            MvPolynomial.eval ![((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
              ((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)]
              (reconstruct D fun j => if x = j then 1 else 0)) := by
          refine hsfa _ _ fun u hu hud => ?_
          rw [hval w u hw hwd hu hud, ← reconstruct_eval D (Ff u) (hmem u), hlin]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hVval x u hu hud]
      _ = ∑ x : ↥(grid D), scalarFreeAverage (fun u => V u x *
            MvPolynomial.eval ![((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
              ((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)]
              (reconstruct D fun j => if x = j then 1 else 0)) :=
          scalarFreeAverage_finset_sum Finset.univ (fun x u => V u x *
            MvPolynomial.eval ![((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
              ((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)]
              (reconstruct D fun j => if x = j then 1 else 0)) fun x _ => (hVc x).mul continuous_const
      _ = ∑ x : ↥(grid D), (scalarFreeAverage fun u => V u x) *
            MvPolynomial.eval ![((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
              ((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)]
              (reconstruct D fun j => if x = j then 1 else 0) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [mul_comm (scalarFreeAverage fun u => V u x), ← scalarFreeAverage_const_mul]
          congr 1
          funext u
          exact mul_comm _ _
      _ = MvPolynomial.eval ![((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
            ((((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)] Pstar := by
          rw [hPdef, hlin]
  have hP : averagedPolynomial Φ D p q = Pstar := by
    unfold averagedPolynomial
    rw [dif_pos hq, ← hσdef]
    have hx : ∀ x : ↥(grid D),
        twistedAverage Φ p (σ * discElt (x : ℝ × ℝ).1 (x : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ x.2)) =
        MvPolynomial.eval ![(((x : ℝ × ℝ).1 : ℝ) : ℂ), (((x : ℝ × ℝ).2 : ℝ) : ℂ)] Pstar := by
      intro x
      rw [core _ (hdisc x).1 (hdisc x).2, discElt_apply_zero_one, hre, him]
    simp only [hx]
    exact reconstruct_eval D Pstar hPmem
  rw [hP, MvPolynomial.totalDegree]
  refine Finset.sup_le fun n hn => ?_
  by_contra hlt
  have hDn : D < n.sum fun _ e => e := not_le.1 hlt
  have hlin2 : ∀ v : ↥(grid D) → ℂ, MvPolynomial.coeff n (reconstruct D v) =
      ∑ x, v x * MvPolynomial.coeff n (reconstruct D fun j => if x = j then 1 else 0) := by
    intro v
    have hl := LinearMap.pi_apply_eq_sum_univ ((MvPolynomial.lcoeff ℂ n) ∘ₗ reconstruct D) v
    simpa only [LinearMap.coe_comp, Function.comp_apply, MvPolynomial.lcoeff_apply, smul_eq_mul] using hl
  have hcoeff : MvPolynomial.coeff n Pstar = 0 := by
    rw [hPdef, hlin2]
    have hsum : ∑ x : ↥(grid D), (scalarFreeAverage fun u => V u x) *
          MvPolynomial.coeff n (reconstruct D fun j => if x = j then 1 else 0) =
        scalarFreeAverage fun u => ∑ x : ↥(grid D), V u x *
          MvPolynomial.coeff n (reconstruct D fun j => if x = j then 1 else 0) := by
      rw [scalarFreeAverage_finset_sum Finset.univ
        (fun x u => V u x * MvPolynomial.coeff n (reconstruct D fun j => if x = j then 1 else 0))
        fun x _ => (hVc x).mul continuous_const]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_comm (scalarFreeAverage fun u => V u x), ← scalarFreeAverage_const_mul]
      congr 1
      funext u
      exact mul_comm _ _
    rw [hsum]
    have hzero : ∀ u, IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
        ∑ x : ↥(grid D), V u x * MvPolynomial.coeff n (reconstruct D fun j => if x = j then 1 else 0) = 0 := by
      intro u hu hud
      have h0 : MvPolynomial.coeff n (reconstruct D fun x => V u x) = 0 := by
        have hfun : (fun x => V u x) = fun x : ↥(grid D) =>
            MvPolynomial.eval ![(((x : ℝ × ℝ).1 : ℝ) : ℂ), (((x : ℝ × ℝ).2 : ℝ) : ℂ)] (Ff u) :=
          funext fun x => hVval x u hu hud
        rw [hfun, reconstruct_eval D (Ff u) (hmem u)]
        exact MvPolynomial.coeff_eq_zero_of_totalDegree_lt ((hFdeg u).trans_lt hDn)
      rw [hlin2] at h0
      exact h0
    rw [hsfa _ (fun _ => (0 : ℂ)) hzero]
    have hz := scalarFreeAverage_const_mul 0 (fun _ : GL (Fin 2) ℂ => (0 : ℂ))
    simp only [zero_mul] at hz
    exact hz
  exact (MvPolynomial.mem_support_iff.1 hn) hcoeff

private theorem eval_neg_averagedPolynomial (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ)
    (hΦ₀ : IsScalarInvariant Φ) (D : ℕ) (Q : (Fin 2 → Fin 2 → ℂ) × P → MvPolynomial (Fin 2 × Fin 2) ℂ)
    (hQd : ∀ q, (Q q).totalDegree ≤ D)
    (hQm : ∀ m, (fun q => (Q q).coeff m) ∈ translateSpan Φ)
    (hQe : ∀ q (u : GL (Fin 2) ℂ), IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      groupTranslate Φ u q = MvPolynomial.eval (entries u) (Q q))
    (p : P) {g k₁ k₂ : GL (Fin 2) ℂ} (h : IsBalancedDecomposition g k₁ k₂) :
    MvPolynomial.eval
        ![-((((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
          -((((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)]
        (averagedPolynomial Φ D p (invFrobSq g, invAbsDet g)) =
      twistedAverage Φ p g := by
  obtain ⟨k₁', k₂', h', hneg⟩ := h.neg
  have hv := twistedAverage_eq_eval_averagedPolynomial Φ hΦ hΦ₀ D Q hQd hQm hQe p h'
  rw [hneg, Units.val_neg, Matrix.neg_apply, Complex.neg_re, Complex.neg_im, Complex.ofReal_neg,
    Complex.ofReal_neg] at hv
  exact hv.symm

private theorem twistedAverage_conjEntries_eq_eval (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ)
    (hΦ₀ : IsScalarInvariant Φ) (D : ℕ) (Q : (Fin 2 → Fin 2 → ℂ) × P → MvPolynomial (Fin 2 × Fin 2) ℂ)
    (hQd : ∀ q, (Q q).totalDegree ≤ D)
    (hQm : ∀ m, (fun q => (Q q).coeff m) ∈ translateSpan Φ)
    (hQe : ∀ q (u : GL (Fin 2) ℂ), IsIsometry u → Matrix.det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 →
      groupTranslate Φ u q = MvPolynomial.eval (entries u) (Q q))
    (p : P) {g k₁ k₂ : GL (Fin 2) ℂ} (h : IsBalancedDecomposition g k₁ k₂) :
    twistedAverage Φ p (conjEntries g) =
      MvPolynomial.eval
        ![((((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
          (((-(((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℝ) : ℂ))]
        (averagedPolynomial Φ D p (invFrobSq g, invAbsDet g)) := by
  have hv := twistedAverage_eq_eval_averagedPolynomial Φ hΦ hΦ₀ D Q hQd hQm hQe p h.conjEntries
  rw [conjEntries_mul_conjEntries_conjEntries, ChartInvariance.conjEntries_apply, Complex.conj_re, Complex.conj_im,
    invFrobSq_conjEntries, invAbsDet_conjEntries] at hv
  exact hv

private theorem continuous_twistedAverage_diagonalElt_mul (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ)
    (p : P) (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    Continuous fun x : ↥normDetCone => twistedAverage Φ p (diagonalElt (x : ℝ × ℝ) x.2 * discElt a b hab) := by
  have hA : Continuous fun x : ↥normDetCone =>
      ((diagonalElt (x : ℝ × ℝ) x.2 * discElt a b hab : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    show Continuous fun x : ↥normDetCone =>
      ((diagonalElt (x : ℝ × ℝ) x.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((discElt a b hab : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
    exact (Units.continuous_val.comp continuous_diagonalElt).matrix_mul continuous_const
  simpa only [twistedAverage, parameterSlice] using
    continuous_unitaryAverage_slice Φ hΦ p
      (fun x : ↥normDetCone => diagonalElt (x : ℝ × ℝ) x.2 * discElt a b hab) hA

private theorem continuousOn_expansionCoeff (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ) (D : ℕ) (p : P)
    (i l : ℕ) : ContinuousOn (fun q : ℝ × ℝ => expansionCoeff Φ D p i l q.1 q.2) normDetCone := by
  rw [continuousOn_iff_continuous_restrict]
  have hx : ∀ x : ↥normDetCone, (((x : ℝ × ℝ).1, (x : ℝ × ℝ).2) : ℝ × ℝ) ∈ normDetCone := fun x => x.2
  have hv : Continuous fun x : ↥normDetCone => fun g : ↥(grid D) =>
      twistedAverage Φ p (diagonalElt ((x : ℝ × ℝ).1, (x : ℝ × ℝ).2) (hx x) *
        discElt (g : ℝ × ℝ).1 (g : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ g.2)) :=
    continuous_pi fun g => continuous_twistedAverage_diagonalElt_mul Φ hΦ p _ _ _
  have hℓ₁ : Continuous ((MvPolynomial.lcoeff ℂ (Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l))).comp
      (reconstruct D)) :=
    LinearMap.continuous_of_finiteDimensional _
  have hℓ₂ : Continuous ((MvPolynomial.lcoeff ℂ (Finsupp.single 0 (2 * i) + Finsupp.single 1 (2 * l))).comp
      ((MvPolynomial.aeval (R := ℂ) fun j : Fin 2 => -(MvPolynomial.X j : MvPolynomial (Fin 2) ℂ)).toLinearMap.comp
        (reconstruct D))) :=
    LinearMap.continuous_of_finiteDimensional _
  refine ((continuous_const (y := (2 : ℂ)⁻¹)).mul ((hℓ₁.comp hv).add (hℓ₂.comp hv))).congr fun x => ?_
  simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, Set.restrict_apply, expansionCoeff, averagedPolynomial,
    dif_pos (hx x), evenPart, MvPolynomial.coeff_smul, MvPolynomial.coeff_add, smul_eq_mul, LinearMap.comp_apply,
    MvPolynomial.lcoeff_apply, AlgHom.toLinearMap_apply]

private theorem exists_isCompact_forall_expansionCoeff_eq_zero (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) {R : ℝ}
    (hR : ∀ (M : Fin 2 → Fin 2 → ℂ) (p : P),
      R < (Matrix.trace (Matrix.of M * (Matrix.of M).conjTranspose)).re → Φ (M, p) = 0) (D : ℕ) :
    ∃ K : Set (ℝ × ℝ), IsCompact K ∧
      ∀ (p : P) (i l : ℕ) (q : ℝ × ℝ), q ∉ K → expansionCoeff Φ D p i l q.1 q.2 = 0 := by
  have _ := ‹TopologicalSpace P›
  refine ⟨Set.Icc (0 : ℝ) (max R 0) ×ˢ Set.Icc (0 : ℝ) (max R 0), isCompact_Icc.prod isCompact_Icc, ?_⟩
  intro p i l q hqK
  by_cases hq : ((q.1, q.2) : ℝ × ℝ) ∈ normDetCone
  · have h1 : 2 * q.2 ≤ q.1 := hq.1
    have h2 : 0 < q.2 := hq.2
    have hq1 : R < q.1 := by
      by_contra hle
      rw [not_lt] at hle
      exact hqK ⟨⟨by linarith, by linarith [le_max_left R 0]⟩, ⟨h2.le, by linarith [le_max_left R 0]⟩⟩
    have hzero : ∀ g : ↥(grid D), twistedAverage Φ p (diagonalElt (q.1, q.2) hq *
        discElt (g : ℝ × ℝ).1 (g : ℝ × ℝ).2 (sq_add_sq_le_one_of_mem_grid D _ g.2)) = 0 := by
      intro g
      unfold twistedAverage
      refine (unitaryAverage_congr_of_isIsometry _ (fun _ => (0 : ℂ)) ?_).trans ?_
      · intro u hu
        simp only [parameterSlice]
        apply hR
        show R < invFrobSq (u⁻¹ * (diagonalElt (q.1, q.2) hq * discElt _ _ _) * conjEntries u)
        rw [ChartInvariance.invFrobSq_conj hu, invFrobSq_diagonalElt_mul_discElt]
        exact hq1
      · simp [unitaryAverage]
    simp only [expansionCoeff, averagedPolynomial, dif_pos hq, hzero]
    rw [show (fun _ : ↥(grid D) => (0 : ℂ)) = 0 from rfl, map_zero]
    simp only [evenPart, map_zero, add_zero, smul_zero, MvPolynomial.coeff_zero]
  · simp only [expansionCoeff, averagedPolynomial, dif_neg hq, evenPart, map_zero, add_zero, smul_zero,
      MvPolynomial.coeff_zero]

end Topology
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted.RightFiniteExpansion"

end TwistedAverageExpansion
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted.RightFiniteExpansion"

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted.RightFiniteExpansion"

private theorem exists_monomialExpansion_of_finiteDimensional_rightSpan
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
    (hΦr : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (Matrix.of q.1 * ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), q.2)))) :
    ∃ a : ℕ, ∃ C : P → ℕ → ℕ → ℝ → ℝ → ℂ, ∃ O : P → GL (Fin 2) ℂ → ℂ,
      (∀ p i l, ContinuousOn (fun q : ℝ × ℝ => C p i l q.1 q.2) normDetCone) ∧
      (∃ K : Set (ℝ × ℝ), IsCompact K ∧ ∀ p i l, ∀ q : ℝ × ℝ, q ∉ K → C p i l q.1 q.2 = 0) ∧
      (∀ p g, O p (conjEntries g) = - O p g) ∧
      ∀ p, ∀ g ∈ distinctSingularValues,
        unitaryAverage (fun k => parameterSlice Φ p (k⁻¹ * g * conjEntries k)) =
          (∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
              C p i l (invFrobSq g) (invAbsDet g) * ((monomialInput i l g : ℝ) : ℂ)) + O p g := by
  have _ := hΦU
  have hΦ : Continuous Φ := hΦs.continuous
  haveI : FiniteDimensional ℂ (RightFiniteExpansion.translateSpan Φ) := hΦr
  haveI := RightFiniteExpansion.finiteDimensional_translateSpan_preparedInput Φ hΦ
  have hΨ : Continuous (RightFiniteExpansion.preparedInput Φ) := RightFiniteExpansion.continuous_preparedInput Φ hΦ
  have hΨ₀ : RightFiniteExpansion.IsScalarInvariant (RightFiniteExpansion.preparedInput Φ) :=
    RightFiniteExpansion.isScalarInvariant_preparedInput Φ hΦ
  obtain ⟨D, hPA⟩ := RightFiniteExpansion.exists_isPolynomialAlong_self
    RightFiniteExpansion.isAveragingDevice_unitaryAverage TwistedAverageExpansion.isDetOneIsometryGroup
    (RightFiniteExpansion.preparedInput Φ) hΨ hΨ₀
  unfold RightFiniteExpansion.IsPolynomialAlong at hPA
  obtain ⟨-, Q, hQd, hQm, hQe⟩ := hPA
  obtain ⟨R, hR⟩ := TwistedAverageExpansion.exists_forall_apply_eq_zero_of_hasCompactSupport Φ hΦc
  have hRΨ := TwistedAverageExpansion.preparedInput_apply_eq_zero Φ hR
  refine ⟨D,
    fun p i l T d => TwistedAverageExpansion.expansionCoeff (RightFiniteExpansion.preparedInput Φ) D p i l T d,
    fun p g => TwistedAverageExpansion.oddPart (RightFiniteExpansion.preparedInput Φ) p g, ?_, ?_, ?_, ?_⟩
  · intro p i l
    exact TwistedAverageExpansion.continuousOn_expansionCoeff _ hΨ D p i l
  · exact TwistedAverageExpansion.exists_isCompact_forall_expansionCoeff_eq_zero _ hRΨ D
  · intro p g
    exact TwistedAverageExpansion.oddPart_conjEntries _ p g
  · intro p g hg
    rw [RightFiniteExpansion.unitaryAverage_twisted_preparedInput Φ hΦ p g]
    show TwistedAverageExpansion.twistedAverage (RightFiniteExpansion.preparedInput Φ) p g =
      (∑ i ∈ Finset.range (D + 1), ∑ l ∈ Finset.range (D + 1 - i),
        TwistedAverageExpansion.expansionCoeff (RightFiniteExpansion.preparedInput Φ) D p i l (invFrobSq g)
          (invAbsDet g) *
          ((monomialInput i l g : ℝ) : ℂ)) +
        TwistedAverageExpansion.oddPart (RightFiniteExpansion.preparedInput Φ) p g
    unfold TwistedAverageExpansion.expansionCoeff TwistedAverageExpansion.oddPart
    obtain ⟨k₁, k₂, hb⟩ := TwistedAverageExpansion.exists_isBalancedDecomposition g
    have hval := TwistedAverageExpansion.twistedAverage_eq_eval_averagedPolynomial _ hΨ hΨ₀ D Q hQd hQm hQe p hb
    have hvneg := TwistedAverageExpansion.eval_neg_averagedPolynomial _ hΨ hΨ₀ D Q hQd hQm hQe p hb
    have hvconj := TwistedAverageExpansion.twistedAverage_conjEntries_eq_eval _ hΨ hΨ₀ D Q hQd hQm hQe p hb
    have hvnegconj :=
      TwistedAverageExpansion.eval_neg_averagedPolynomial _ hΨ hΨ₀ D Q hQd hQm hQe p hb.conjEntries
    rw [TwistedAverageExpansion.conjEntries_mul_conjEntries_conjEntries, ChartInvariance.conjEntries_apply,
      Complex.conj_re, Complex.conj_im, TwistedAverageExpansion.invFrobSq_conjEntries,
      TwistedAverageExpansion.invAbsDet_conjEntries] at hvnegconj
    have hGeven := TwistedAverageExpansion.aeval_neg_evenPart
      (TwistedAverageExpansion.averagedPolynomial (RightFiniteExpansion.preparedInput Φ) D p
        (invFrobSq g, invAbsDet g))
    have hGdeg : (TwistedAverageExpansion.evenPart
        (TwistedAverageExpansion.averagedPolynomial (RightFiniteExpansion.preparedInput Φ) D p
          (invFrobSq g, invAbsDet g))).totalDegree ≤ D :=
      (TwistedAverageExpansion.totalDegree_evenPart_le _).trans
        (TwistedAverageExpansion.totalDegree_averagedPolynomial_le _ hΨ hΨ₀ D Q hQd hQm hQe p _)
    have hGab : MvPolynomial.eval
        ![((((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
          ((((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℂ)]
        (TwistedAverageExpansion.evenPart
          (TwistedAverageExpansion.averagedPolynomial (RightFiniteExpansion.preparedInput Φ) D p
            (invFrobSq g, invAbsDet g))) =
        TwistedAverageExpansion.twistedAverage (RightFiniteExpansion.preparedInput Φ) p g := by
      rw [TwistedAverageExpansion.eval_evenPart, ← hval, hvneg]
      ring
    have hGab' : MvPolynomial.eval
        ![((((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re : ℂ),
          ((-(((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im : ℝ) : ℂ)]
        (TwistedAverageExpansion.evenPart
          (TwistedAverageExpansion.averagedPolynomial (RightFiniteExpansion.preparedInput Φ) D p
            (invFrobSq g, invAbsDet g))) =
        TwistedAverageExpansion.twistedAverage (RightFiniteExpansion.preparedInput Φ) p (conjEntries g) := by
      rw [TwistedAverageExpansion.eval_evenPart, ← hvconj, hvnegconj]
      ring
    have hS4b := TorusAverage.eval_add_eval_neg_eq_two_mul_sum_coeff_even _ hGeven
      (((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re
      (((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im
    rw [hGab, hGab'] at hS4b
    have hb' := hb
    unfold TwistedAverageExpansion.IsBalancedDecomposition at hb'
    obtain ⟨hk₁, hk₂, hdet, hg4⟩ := hb'
    obtain ⟨hl0, hlu, -, hprod⟩ := singularValues_spec (invFrobSq g) (invAbsDet g) (invAbsDet_pos g).le
      (two_mul_invAbsDet_le_invFrobSq g)
    have hl : 0 < lowerSingularValue (invFrobSq g) (invAbsDet g) := by
      refine lt_of_le_of_ne hl0 fun h0 => ?_
      rw [← h0, mul_zero] at hprod
      exact (invAbsDet_pos g).ne hprod
    have hu : 0 < upperSingularValue (invFrobSq g) (invAbsDet g) := hl.trans_le hlu
    have hmono : ∀ i l : ℕ, monomialInput i l g =
        (((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re ^ (2 * i) *
          (((k₂ * conjEntries k₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im ^ (2 * l) :=
      fun i l => TorusAverage.monomialInput_eq_re_pow_mul_im_pow_of_eq_mul_diagonal_mul g k₁ k₂ _ _ hu hl hk₁ hk₂
        hdet hg4 hg i l
    simp only [hmono]
    rw [TwistedAverageExpansion.sum_coeff_even_eq_of_totalDegree_le _ hGdeg]
    linear_combination (1 / 2 : ℂ) * hS4b

private theorem invariants_twistedConj_unitary (k g : GL (Fin 2) ℂ)
    (hk : star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    invFrobSq (k⁻¹ * g * conjEntries k) = invFrobSq g ∧
      invTraceNorm (k⁻¹ * g * conjEntries k) = invTraceNorm g ∧
      invSecondRe (k⁻¹ * g * conjEntries k) = invSecondRe g ∧
      invAbsDet (k⁻¹ * g * conjEntries k) = invAbsDet g := by
  exact ⟨ChartInvariance.invFrobSq_conj hk g, ChartInvariance.invTraceNorm_conj k g,
    ChartInvariance.invSecondRe_conj hk g, ChartInvariance.invAbsDet_conj k g⟩

private theorem _root_.AutomorphicForm.GL2Twisted.twistedSplitTransform_eq_zero_of_odd (O : GL (Fin 2) ℂ → ℂ) (hO : ∀ g, O (conjEntries g) = - O g)
    (a₁ a₂ : ℝ) : twistedSplitTransform O a₁ a₂ = 0 :=
  OddInputs.twistedSplitTransform_eq_zero_of_odd O hO a₁ a₂

p2m_export "AutomorphicForm.GL2Twisted" "twistedSplitTransform_eq_zero_of_odd"
private theorem _root_.AutomorphicForm.GL2Twisted.twistedEllipticTransform_eq_zero_of_odd (O : GL (Fin 2) ℂ → ℂ) (hO : ∀ g, O (conjEntries g) = - O g)
    (r θ : ℝ) : twistedEllipticTransform O r θ = 0 :=
  OddInputs.twistedEllipticTransform_eq_zero_of_odd O hO r θ

p2m_export "AutomorphicForm.GL2Twisted" "twistedEllipticTransform_eq_zero_of_odd"
private theorem _root_.AutomorphicForm.GL2Twisted.integral_twistedSplitElt_eq_zero_of_odd (F : GL (Fin 2) ℂ → ℂ) (hF : ∀ g, F (conjEntries g) = - F g)
    (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) : ∫ v : ℂ, F (twistedSplitElt a₁ a₂ v h) = 0 :=
  OddInputs.integral_twistedSplitElt_eq_zero_of_odd F hF a₁ a₂ h

p2m_export "AutomorphicForm.GL2Twisted" "integral_twistedSplitElt_eq_zero_of_odd"
private theorem _root_.AutomorphicForm.GL2Twisted.integral_twistedEllipticElt_bracket_eq_zero_of_odd (F : GL (Fin 2) ℂ → ℂ)
    (hF : ∀ g, F (conjEntries g) = - F g) (r θ : ℝ) (hr : 0 < r) :
    (∫ ρ in Set.Ioi (0 : ℝ), ∫ u : ℂ,
        if hρ : 0 < ρ then
          (ρ : ℂ)⁻¹ * (F (twistedEllipticElt r θ ρ u hr hρ) + F (twistedEllipticElt r (-θ) ρ u hr hρ))
        else 0) = 0 :=
  OddInputs.integral_twistedEllipticElt_bracket_eq_zero_of_odd F hF r θ hr

p2m_export "AutomorphicForm.GL2Twisted" "integral_twistedEllipticElt_bracket_eq_zero_of_odd"
private theorem _root_.AutomorphicForm.GL2Twisted.unitaryAverage_const (z : ℂ) : unitaryAverage (fun _ => z) = z := by
  unfold unitaryAverage
  have hsc : ∫ η in (0 : ℝ)..(Real.pi / 2), ((Real.sin η : ℂ) * (Real.cos η : ℂ)) = (1 / 2 : ℂ) := by
    have h : ∫ η in (0 : ℝ)..(Real.pi / 2), ((Real.sin η * Real.cos η : ℝ) : ℂ) =
        ((∫ η in (0 : ℝ)..(Real.pi / 2), Real.sin η * Real.cos η : ℝ) : ℂ) := intervalIntegral.integral_ofReal
    rw [integral_sin_mul_cos₁, Real.sin_pi_div_two, Real.sin_zero] at h
    push_cast at h
    simpa using h
  have h2 : ∀ c : ℂ, (∫ _x in (0 : ℝ)..(2 * Real.pi), c) = ((2 * Real.pi : ℝ) : ℂ) * c := by
    intro c
    rw [intervalIntegral.integral_const, sub_zero]
    exact Complex.real_smul
  simp only [h2]
  have ha : (∫ η in (0 : ℝ)..(Real.pi / 2), ((2 * Real.pi : ℝ) : ℂ) *
        (((2 * Real.pi : ℝ) : ℂ) * ((Real.sin η * Real.cos η : ℂ) * z))) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ η in (0 : ℝ)..(Real.pi / 2),
        ((2 * Real.pi : ℝ) : ℂ) * ((Real.sin η * Real.cos η : ℂ) * z) :=
    intervalIntegral.integral_const_mul _ _
  have hb : (∫ η in (0 : ℝ)..(Real.pi / 2), ((2 * Real.pi : ℝ) : ℂ) * ((Real.sin η * Real.cos η : ℂ) * z)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ η in (0 : ℝ)..(Real.pi / 2), (Real.sin η * Real.cos η : ℂ) * z :=
    intervalIntegral.integral_const_mul _ _
  have hc : (∫ η in (0 : ℝ)..(Real.pi / 2), (Real.sin η * Real.cos η : ℂ) * z) =
      (∫ η in (0 : ℝ)..(Real.pi / 2), (Real.sin η * Real.cos η : ℂ)) * z :=
    intervalIntegral.integral_mul_const _ _
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [ha, hb, hc, hsc]
  push_cast
  field_simp
  ring1

p2m_export "AutomorphicForm.GL2Twisted" "unitaryAverage_const"
private theorem norm_ellipticFibreTerm_le (i l : ℕ) (T r θ : ℝ) (hr : 0 < r) (hT : 2 * r < T) :
    ‖ellipticFibreTerm i l T r θ‖ ≤ 4 * Real.pi ^ 2 / r := by
  set x : ℝ := 2 * r * Real.cos θ with hx
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hcos2 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hTx : 0 < T - x := by rw [hx]; nlinarith
  have hTp : 0 < T + 2 * r := by linarith
  have hTm : 0 < T - 2 * r := by linarith
  set κ : ℝ := (2 * r - T * Real.cos θ) / (T - x) with hκ
  have hκ1 : κ ≤ 1 := by
    rw [hκ, div_le_one hTx, hx]; nlinarith
  have hκ2 : -1 ≤ κ := by
    rw [hκ, le_div_iff₀ hTx, hx]; nlinarith
  have hκ' : (1 - κ) / 2 = (T - 2 * r) * (1 + Real.cos θ) / (2 * (T - x)) := by
    rw [hκ]; field_simp; rw [hx]; ring
  have harc : ellipticArcLength T r θ = Real.arccos κ := by
    simp only [ellipticArcLength, hκ, hx]
  have hψ0 : 0 ≤ Real.arccos κ := Real.arccos_nonneg κ
  have hψπ : Real.arccos κ ≤ Real.pi := Real.arccos_le_pi κ
  have hhalf : Real.sin (Real.arccos κ / 2) ^ 2 = (1 - κ) / 2 := by
    rw [Real.sin_sq_eq_half_sub, mul_div_cancel₀ _ (two_ne_zero' ℝ), Real.cos_arccos hκ2 hκ1]; ring
  have harc_nonneg : 0 ≤ fibreArcIntegral i l (ellipticArcLength T r θ) := by
    rw [harc]; exact fibreArcIntegral_nonneg i l hψ0
  have hW : fibreArcIntegral i l (ellipticArcLength T r θ) ≤ Real.pi * ((1 - κ) / 2) ^ l := by
    rw [harc]
    calc fibreArcIntegral i l (Real.arccos κ) ≤ Real.arccos κ * (Real.sin (Real.arccos κ / 2) ^ 2) ^ l :=
          fibreArcIntegral_le i l hψ0 hψπ
      _ = Real.arccos κ * ((1 - κ) / 2) ^ l := by rw [hhalf]
      _ ≤ Real.pi * ((1 - κ) / 2) ^ l := by
          apply mul_le_mul_of_nonneg_right hψπ
          apply pow_nonneg; linarith
  have hPnonneg : 0 ≤ fibreMonomialFactor i l T r x := by
    unfold fibreMonomialFactor; positivity
  have hkey : fibreMonomialFactor i l T r x * ((1 - κ) / 2) ^ l =
      ((T - x) / (T + 2 * r)) ^ i * ((1 + Real.cos θ) / 2) ^ l := by
    rw [hκ']; unfold fibreMonomialFactor
    rw [div_pow, div_mul_div_comm, div_pow, div_pow, div_mul_div_comm, div_eq_div_iff]
    · simp only [mul_pow]; ring
    · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hTp.ne') (pow_ne_zero _ hTm.ne'))
        (pow_ne_zero _ (mul_ne_zero two_ne_zero hTx.ne'))
    · exact mul_ne_zero (pow_ne_zero _ hTp.ne') (pow_ne_zero _ two_ne_zero)
  have hA : (T - x) / (T + 2 * r) ≤ 1 := by rw [div_le_one hTp, hx]; nlinarith
  have hB : (1 + Real.cos θ) / 2 ≤ 1 := by linarith
  have hA0 : 0 ≤ (T - x) / (T + 2 * r) := by positivity
  have hcos_nonneg : 0 ≤ (1 + Real.cos θ) / 2 := by linarith
  have hPW : fibreMonomialFactor i l T r x * fibreArcIntegral i l (ellipticArcLength T r θ) ≤ Real.pi := by
    calc fibreMonomialFactor i l T r x * fibreArcIntegral i l (ellipticArcLength T r θ)
        ≤ fibreMonomialFactor i l T r x * (Real.pi * ((1 - κ) / 2) ^ l) := mul_le_mul_of_nonneg_left hW hPnonneg
      _ = Real.pi * (fibreMonomialFactor i l T r x * ((1 - κ) / 2) ^ l) := by ring
      _ = Real.pi * (((T - x) / (T + 2 * r)) ^ i * ((1 + Real.cos θ) / 2) ^ l) := by rw [hkey]
      _ ≤ Real.pi * (1 * 1) := by
          apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
          exact mul_le_mul (pow_le_one₀ hA0 hA) (pow_le_one₀ hcos_nonneg hB) (pow_nonneg hcos_nonneg l) zero_le_one
      _ = Real.pi := by ring
  have hPW0 : 0 ≤ fibreMonomialFactor i l T r x * fibreArcIntegral i l (ellipticArcLength T r θ) :=
    mul_nonneg hPnonneg harc_nonneg
  have hpre : |4 * Real.pi * Real.sin θ / r| ≤ 4 * Real.pi / r := by
    rw [abs_div, abs_of_pos hr, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi)]
    apply div_le_div_of_nonneg_right _ hr.le
    calc 4 * Real.pi * |Real.sin θ| ≤ 4 * Real.pi * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (by positivity)
      _ = 4 * Real.pi := mul_one _
  unfold ellipticFibreTerm
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, ← hx,
    abs_of_nonneg hPW0]
  calc |4 * Real.pi * Real.sin θ / r| *
        (fibreMonomialFactor i l T r x * fibreArcIntegral i l (ellipticArcLength T r θ))
      ≤ (4 * Real.pi / r) * Real.pi := mul_le_mul hpre hPW hPW0 (by positivity)
    _ = 4 * Real.pi ^ 2 / r := by ring

private theorem integral_twistedSplitElt_congr_of_eqOn_distinctSingularValues
    (F G : GL (Fin 2) ℂ → ℂ) (hFG : Set.EqOn F G distinctSingularValues)
    (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) :
    ∫ v : ℂ, F (twistedSplitElt a₁ a₂ v h) = ∫ v : ℂ, G (twistedSplitElt a₁ a₂ v h) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.Measure.ae_ne (volume : MeasureTheory.Measure ℂ) (0 : ℂ)] with v hv
  exact hFG (twistedSplitElt_mem_distinctSingularValues a₁ a₂ v h hv)

private theorem integral_twistedEllipticElt_bracket_congr_of_eqOn_distinctSingularValues
    (F G : GL (Fin 2) ℂ → ℂ) (hFG : Set.EqOn F G distinctSingularValues) (r θ : ℝ) (hr : 0 < r) :
    (∫ ρ in Set.Ioi (0 : ℝ), ∫ u : ℂ,
        if hρ : 0 < ρ then
          (ρ : ℂ)⁻¹ * (F (twistedEllipticElt r θ ρ u hr hρ) + F (twistedEllipticElt r (-θ) ρ u hr hρ))
        else 0) =
      ∫ ρ in Set.Ioi (0 : ℝ), ∫ u : ℂ,
        if hρ : 0 < ρ then
          (ρ : ℂ)⁻¹ * (G (twistedEllipticElt r θ ρ u hr hρ) + G (twistedEllipticElt r (-θ) ρ u hr hρ))
        else 0 := by
  congr 1
  ext ρ
  by_cases hρ : 0 < ρ
  · simp only [dif_pos hρ]
    exact two_sheets_congr_aux F G hFG r θ ρ hr hρ _
  · simp only [dif_neg hρ]

private theorem _root_.AutomorphicForm.GL2Twisted.norm_monomialInput_twistedSplitElt_le_one (i l : ℕ) (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    ‖monomialInput i l (twistedSplitElt a₁ a₂ v h)‖ ≤ 1 :=
  MonomialBounds.norm_monomialInput_twistedSplitElt_le_one i l a₁ a₂ v h

p2m_export "AutomorphicForm.GL2Twisted" "norm_monomialInput_twistedSplitElt_le_one"
private theorem _root_.AutomorphicForm.GL2Twisted.norm_monomialInput_twistedEllipticElt_le_one (i l : ℕ) (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    ‖monomialInput i l (twistedEllipticElt r θ ρ u hr hρ)‖ ≤ 1 :=
  MonomialBounds.norm_monomialInput_twistedEllipticElt_le_one i l r θ ρ u hr hρ

p2m_export "AutomorphicForm.GL2Twisted" "norm_monomialInput_twistedEllipticElt_le_one"
private theorem _root_.AutomorphicForm.GL2Twisted.measurable_monomialInput_twistedSplitElt (i l : ℕ) (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) :
    Measurable fun v : ℂ => monomialInput i l (twistedSplitElt a₁ a₂ v h) :=
  MonomialBounds.measurable_monomialInput_twistedSplitElt i l a₁ a₂ h

p2m_export "AutomorphicForm.GL2Twisted" "measurable_monomialInput_twistedSplitElt"
private theorem _root_.AutomorphicForm.GL2Twisted.measurable_monomialInput_twistedEllipticElt (i l : ℕ) (r θ : ℝ) (hr : 0 < r) :
    Measurable fun p : ℝ × ℂ =>
      if hρ : 0 < p.1 then monomialInput i l (twistedEllipticElt r θ p.1 p.2 hr hρ) else 0 :=
  MonomialBounds.measurable_monomialInput_twistedEllipticElt i l r θ hr

p2m_export "AutomorphicForm.GL2Twisted" "measurable_monomialInput_twistedEllipticElt"
private theorem _root_.AutomorphicForm.GL2Twisted.integral_twistedEllipticElt_two_sheets_eq_zero_of_odd (F : GL (Fin 2) ℂ → ℂ)
    (hF : ∀ g, F (conjEntries g) = -F g) (r θ ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (c : ℂ) :
    ∫ u : ℂ, c * (F (twistedEllipticElt r θ ρ u hr hρ) + F (twistedEllipticElt r (-θ) ρ u hr hρ)) = 0 :=
  OddInputs.integral_twistedEllipticElt_two_sheets_eq_zero_of_odd F hF r θ ρ hr hρ c

p2m_export "AutomorphicForm.GL2Twisted" "integral_twistedEllipticElt_two_sheets_eq_zero_of_odd"
private theorem integral_twistedEllipticElt_two_sheets_congr_of_eqOn_distinctSingularValues
    (F G : GL (Fin 2) ℂ → ℂ) (hFG : Set.EqOn F G distinctSingularValues) (r θ ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ)
    (c : ℂ) :
    ∫ u : ℂ, c * (F (twistedEllipticElt r θ ρ u hr hρ) + F (twistedEllipticElt r (-θ) ρ u hr hρ)) =
      ∫ u : ℂ, c * (G (twistedEllipticElt r θ ρ u hr hρ) + G (twistedEllipticElt r (-θ) ρ u hr hρ)) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_gap_ne_zero θ ρ hρ] with u hu
  have hinv : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ.ne'
  have hq := Complex.normSq_nonneg u
  have hc := Real.cos_le_one θ
  have h0 : 0 ≤ ρ ^ 2 * Complex.normSq u ^ 2 + (2 * ρ ^ 2 - 2 * Real.cos θ) * Complex.normSq u
      + (ρ ^ 2 + ρ⁻¹ ^ 2 - 2) := by
    nlinarith [sq_nonneg (ρ * (Complex.normSq u + 1) - ρ⁻¹), mul_nonneg hq (sub_nonneg.mpr hc)]
  have hg := lt_of_le_of_ne h0 (Ne.symm hu)
  have hneg : 0 < ρ ^ 2 * Complex.normSq u ^ 2 + (2 * ρ ^ 2 - 2 * Real.cos (-θ)) * Complex.normSq u
      + (ρ ^ 2 + ρ⁻¹ ^ 2 - 2) := by rwa [Real.cos_neg]
  rw [hFG (twistedEllipticElt_mem_distinctSingularValues r θ ρ u hr hρ hg),
    hFG (twistedEllipticElt_mem_distinctSingularValues r (-θ) ρ u hr hρ hneg)]

private abbrev sliceAt {P : Type} (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (p : P) : GL (Fin 2) ℂ → ℂ :=
  fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)

private theorem twistedSplitTransform_slice_eq_sum {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (p : P)
    (a : ℕ) (C : P → ℕ → ℕ → ℝ → ℝ → ℂ) (O : P → GL (Fin 2) ℂ → ℂ)
    (hC : ∀ p i l, ContinuousOn (fun q : ℝ × ℝ => C p i l q.1 q.2) normDetCone)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (hCK : ∀ p i l, ∀ q : ℝ × ℝ, q ∉ K → C p i l q.1 q.2 = 0)
    (hO : ∀ p g, O p (conjEntries g) = - O p g)
    (hexp : ∀ g ∈ distinctSingularValues,
      unitaryAverage (fun k => parameterSlice Φ p (k⁻¹ * g * conjEntries k)) =
        (∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
          C p i l (invFrobSq g) (invAbsDet g) * ((monomialInput i l g : ℝ) : ℂ)) + O p g)
    (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) :
    twistedSplitTransform (sliceAt Φ p) a₁ a₂ =
      ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
        splitFibreSide i l (levelProfile (C p i l) (Real.sqrt a₁ * Real.sqrt a₂)) a₁ a₂ := by
  have h12 : 0 < a₁ ∧ 0 < a₂ := ⟨ha₁, ha₂⟩
  set d₀ : ℝ := Real.sqrt a₁ * Real.sqrt a₂ with hd₀
  have hlevel_ge : ∀ v : ℂ, 2 * d₀ ≤ invFrobSq (twistedSplitElt a₁ a₂ v h12) := by
    intro v
    rw [invFrobSq_twistedSplitElt]
    nlinarith [sq_nonneg (Real.sqrt a₁ - Real.sqrt a₂), Real.sq_sqrt ha₁.le, Real.sq_sqrt ha₂.le,
      Complex.normSq_nonneg v]
  have hd₀pos : 0 < d₀ := by positivity
  have hcoef : ∀ i l (v : ℂ),
      C p i l (invFrobSq (twistedSplitElt a₁ a₂ v h12)) (invAbsDet (twistedSplitElt a₁ a₂ v h12)) =
        levelProfile (C p i l) d₀ (invFrobSq (twistedSplitElt a₁ a₂ v h12)) := by
    intro i l v
    rw [levelProfile_of_le (C p i l) (hlevel_ge v), invAbsDet_twistedSplitElt]
  have hlevel : Continuous fun v : ℂ => invFrobSq (twistedSplitElt a₁ a₂ v h12) := by
    simp only [invFrobSq_twistedSplitElt]; fun_prop
  have hprof_int : ∀ i l, MeasureTheory.Integrable fun v : ℂ =>
      levelProfile (C p i l) d₀ (invFrobSq (twistedSplitElt a₁ a₂ v h12)) := by
    intro i l
    have hcont : Continuous fun v : ℂ => levelProfile (C p i l) d₀ (invFrobSq (twistedSplitElt a₁ a₂ v h12)) :=
      (continuous_levelProfile (C p i l) hd₀pos (hC p i l)).comp hlevel
    refine hcont.integrable_of_hasCompactSupport ?_
    obtain ⟨M, hM⟩ :=
      (hasCompactSupport_levelProfile (C p i l) d₀ hK (hCK p i l)).isCompact.isBounded.subset_closedBall 0
    refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) (Real.sqrt (max 0 M))) (isCompact_closedBall _ _) ?_
    intro v hv
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hle := hM hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, invFrobSq_twistedSplitElt] at hle
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    have hv' : Real.sqrt (max 0 M) < ‖v‖ := lt_of_not_ge hv
    have hsq : max 0 M < Complex.normSq v := by
      rw [Complex.normSq_eq_norm_sq]
      calc max 0 M = Real.sqrt (max 0 M) ^ 2 := (Real.sq_sqrt (le_max_left _ _)).symm
        _ < ‖v‖ ^ 2 := by gcongr
    have habs := le_abs_self (a₁ + a₂ + Complex.normSq v)
    linarith [le_max_right 0 M]
  have hterm_int : ∀ i l, MeasureTheory.Integrable fun v : ℂ =>
      C p i l (invFrobSq (twistedSplitElt a₁ a₂ v h12)) (invAbsDet (twistedSplitElt a₁ a₂ v h12)) *
        ((monomialInput i l (twistedSplitElt a₁ a₂ v h12) : ℝ) : ℂ) := by
    intro i l
    have hbdd := (hprof_int i l).bdd_mul (c := 1)
      (Complex.continuous_ofReal.measurable.comp
        (measurable_monomialInput_twistedSplitElt i l a₁ a₂ h12)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by
        simp only [Function.comp_apply, Complex.norm_real]
        exact norm_monomialInput_twistedSplitElt_le_one i l a₁ a₂ v h12)
    refine hbdd.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [Function.comp_apply]
    rw [hcoef i l v]
    ring
  have hsum_int : MeasureTheory.Integrable fun v : ℂ => ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
      C p i l (invFrobSq (twistedSplitElt a₁ a₂ v h12)) (invAbsDet (twistedSplitElt a₁ a₂ v h12)) *
        ((monomialInput i l (twistedSplitElt a₁ a₂ v h12) : ℝ) : ℂ) :=
    MeasureTheory.integrable_finsetSum _ fun i _ => MeasureTheory.integrable_finsetSum _ fun l _ => hterm_int i l
  have havg_int := integrable_unitaryAverage_slice_split Φ hΦs.continuous hΦc p a₁ a₂ h12
  have hodd_int : MeasureTheory.Integrable fun v : ℂ => O p (twistedSplitElt a₁ a₂ v h12) := by
    refine (havg_int.sub hsum_int).congr ?_
    filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume : MeasureTheory.Measure ℂ) (0 : ℂ)] with v hv
    have hmem := twistedSplitElt_mem_distinctSingularValues a₁ a₂ v h12 hv
    have := hexp _ hmem
    simp only [parameterSlice] at this
    simp only [Pi.sub_apply]
    rw [this]
    ring
  have hterm : ∀ i l, (∫ v : ℂ, C p i l (invFrobSq (twistedSplitElt a₁ a₂ v h12))
        (invAbsDet (twistedSplitElt a₁ a₂ v h12)) * ((monomialInput i l (twistedSplitElt a₁ a₂ v h12) : ℝ) : ℂ)) =
      splitFibreSide i l (levelProfile (C p i l) d₀) a₁ a₂ := by
    intro i l
    have hfibreSides := (twistedTransforms_monomialInput_eq_fibreSides i l (levelProfile (C p i l) d₀)
      (continuous_levelProfile (C p i l) hd₀pos (hC p i l))
      (hasCompactSupport_levelProfile (C p i l) d₀ hK (hCK p i l))
      a₁ a₂ 1 (Real.pi / 2) ha₁ ha₂ one_pos ⟨by positivity, by linarith [Real.pi_pos]⟩).1
    rw [← hfibreSides]
    unfold twistedSplitTransform
    rw [dif_pos h12]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only []
    rw [ChartInvariance.average_conj_invariant, hcoef i l v]
  unfold twistedSplitTransform
  rw [dif_pos h12]
  have hseam := integral_twistedSplitElt_congr_of_eqOn_distinctSingularValues
    (fun g => unitaryAverage fun k => sliceAt Φ p (k⁻¹ * g * conjEntries k))
    (fun g => (∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
      C p i l (invFrobSq g) (invAbsDet g) * ((monomialInput i l g : ℝ) : ℂ)) + O p g)
    (fun g hg => hexp g hg) a₁ a₂ h12
  rw [hseam, MeasureTheory.integral_add hsum_int hodd_int,
    integral_twistedSplitElt_eq_zero_of_odd (O p) (hO p) a₁ a₂ h12, add_zero,
    MeasureTheory.integral_finsetSum _ fun i _ => MeasureTheory.integrable_finsetSum _ fun l _ => hterm_int i l]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun l _ => hterm_int i l]
  exact Finset.sum_congr rfl fun l _ => hterm i l

private theorem two_r_le_invFrobSq_twistedEllipticElt (r θ' ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    2 * r ≤ invFrobSq (twistedEllipticElt r θ' ρ u hr hρ) := by
  rw [invFrobSq_twistedEllipticElt]
  have hinv : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ.ne'
  have hX : 2 ≤ ρ ^ 2 + ρ⁻¹ ^ 2 + Complex.normSq u ^ 2 * ρ ^ 2 + 2 * Complex.normSq u * ρ ^ 2
      - 2 * Complex.normSq u * Real.cos θ' := by
    have h2 : ρ * (Complex.normSq u + 1) * ρ⁻¹ = Complex.normSq u + 1 := by
      rw [mul_comm ρ, mul_assoc, hinv, mul_one]
    nlinarith [sq_nonneg (ρ * (Complex.normSq u + 1) - ρ⁻¹),
      mul_nonneg (Complex.normSq_nonneg u) (sub_nonneg.mpr (Real.cos_le_one θ')), h2, hinv]
  have := mul_le_mul_of_nonneg_left hX hr.le
  linarith

private theorem invFrobSq_twistedEllipticElt_neg (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    invFrobSq (twistedEllipticElt r (-θ) ρ u hr hρ) = invFrobSq (twistedEllipticElt r θ ρ u hr hρ) := by
  rw [invFrobSq_twistedEllipticElt, invFrobSq_twistedEllipticElt, Real.cos_neg]

private theorem lt_invFrobSq_twistedEllipticElt_of_normSq_lt (r θ' ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ)
    (hθ : Real.cos θ' < 1) (R : ℝ) (hu : (R / r - 2) / (2 * (1 - Real.cos θ')) < Complex.normSq u) :
    R < invFrobSq (twistedEllipticElt r θ' ρ u hr hρ) := by
  by_contra hle
  exact absurd (normSq_le_of_invFrobSq_twistedEllipticElt_le r θ' ρ u hr hρ hθ R (not_lt.1 hle)) (not_le.2 hu)

private theorem disc_of_level (r θ : ℝ) (hθ : Real.cos θ < 1) (L : ℝ) :
    ∃ s : ℝ, ∀ (ρ : ℝ) (hρ : 0 < ρ) (u : ℂ), u ∉ Metric.closedBall (0 : ℂ) s →
      ∀ hr : 0 < r, L < invFrobSq (twistedEllipticElt r θ ρ u hr hρ) ∧
        L < invFrobSq (twistedEllipticElt r (-θ) ρ u hr hρ) := by
  set B : ℝ := (L / r - 2) / (2 * (1 - Real.cos θ)) with hB
  refine ⟨Real.sqrt (max 0 B), fun ρ hρ u hu hr => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hu
  have hu' : Real.sqrt (max 0 B) < ‖u‖ := lt_of_not_ge hu
  have hsq : max 0 B < Complex.normSq u := by
    rw [Complex.normSq_eq_norm_sq]
    calc max 0 B = Real.sqrt (max 0 B) ^ 2 := (Real.sq_sqrt (le_max_left _ _)).symm
      _ < ‖u‖ ^ 2 := by gcongr
  have h1 := lt_invFrobSq_twistedEllipticElt_of_normSq_lt r θ ρ u hr hρ hθ L (lt_of_le_of_lt (le_max_right 0 B) hsq)
  exact ⟨h1, by rwa [invFrobSq_twistedEllipticElt_neg]⟩

private theorem integrable_unitaryAverage_slice_elliptic {P : Type} [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (p : P)
    (r θ' ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (hθ : Real.cos θ' < 1) :
    MeasureTheory.Integrable fun u : ℂ => unitaryAverage fun k =>
      Φ (Matrix.of.symm ((k⁻¹ * twistedEllipticElt r θ' ρ u hr hρ * conjEntries k : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ), p) := by
  obtain ⟨R, hR⟩ := exists_forall_slice_eq_zero_of_lt_invFrobSq Φ hΦc
  have hcont := continuous_unitaryAverage_slice Φ hΦ p (fun u => twistedEllipticElt r θ' ρ u hr hρ)
    (continuous_twistedEllipticElt_coe r θ' ρ hr hρ)
  refine hcont.integrable_of_hasCompactSupport ?_
  obtain ⟨s, hs⟩ := disc_of_level r θ' hθ R
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) s) (isCompact_closedBall _ _) ?_
  intro u hu
  apply unitaryAverage_eq_zero_of_forall
  intro ψ η ξ₁ ξ₂
  apply hR
  rw [ChartInvariance.invFrobSq_conj (ChartInvariance.unitaryElt_unitary ψ η ξ₁ ξ₂)]
  exact (hs ρ hρ u hu hr).1

private theorem integrable_profile_elliptic (c : ℝ → ℂ) (hc : Continuous c) (hcs : HasCompactSupport c)
    (r θ' ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (hθ : Real.cos θ' < 1) :
    MeasureTheory.Integrable fun u : ℂ => c (invFrobSq (twistedEllipticElt r θ' ρ u hr hρ)) := by
  have hlevel : Continuous fun u : ℂ => invFrobSq (twistedEllipticElt r θ' ρ u hr hρ) := by
    simp only [invFrobSq_twistedEllipticElt]; fun_prop
  refine (hc.comp hlevel).integrable_of_hasCompactSupport ?_
  obtain ⟨L, hL⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  obtain ⟨s, hs⟩ := disc_of_level r θ' hθ L
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) s) (isCompact_closedBall _ _) ?_
  intro u hu
  simp only [Function.comp_apply]
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hle := hL hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hle
  have hgt := (hs ρ hρ u hu hr).1
  linarith [le_abs_self (invFrobSq (twistedEllipticElt r θ' ρ u hr hρ))]

private theorem integrable_term_elliptic (i l : ℕ) (c : ℝ → ℂ) (hc : Continuous c) (hcs : HasCompactSupport c)
    (r θ' ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (hθ : Real.cos θ' < 1) :
    MeasureTheory.Integrable fun u : ℂ => c (invFrobSq (twistedEllipticElt r θ' ρ u hr hρ)) *
      ((monomialInput i l (twistedEllipticElt r θ' ρ u hr hρ) : ℝ) : ℂ) := by
  have hmeas : Measurable fun u : ℂ => monomialInput i l (twistedEllipticElt r θ' ρ u hr hρ) := by
    have h := (measurable_monomialInput_twistedEllipticElt i l r θ' hr).comp (measurable_prodMk_left (x := ρ))
    simp only [Function.comp_def] at h
    simpa only [dif_pos hρ] using h
  have hbdd := (integrable_profile_elliptic c hc hcs r θ' ρ hr hρ hθ).bdd_mul (c := 1)
    (Complex.continuous_ofReal.measurable.comp hmeas).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by
      simp only [Function.comp_apply, Complex.norm_real]
      exact norm_monomialInput_twistedEllipticElt_le_one i l r θ' ρ u hr hρ)
  refine hbdd.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Function.comp_apply]
  ring

private noncomputable def termBracket (i l : ℕ) (c : ℝ → ℂ) (r θ : ℝ) (hr : 0 < r) : ℝ × ℂ → ℂ := fun q =>
  if hρ : 0 < q.1 then
    (q.1 : ℂ)⁻¹ *
      (c (invFrobSq (twistedEllipticElt r θ q.1 q.2 hr hρ)) *
          ((monomialInput i l (twistedEllipticElt r θ q.1 q.2 hr hρ) : ℝ) : ℂ) +
        c (invFrobSq (twistedEllipticElt r (-θ) q.1 q.2 hr hρ)) *
          ((monomialInput i l (twistedEllipticElt r (-θ) q.1 q.2 hr hρ) : ℝ) : ℂ))
  else 0

private theorem measurable_termBracket (i l : ℕ) (c : ℝ → ℂ) (hc : Continuous c) (r θ : ℝ) (hr : 0 < r) :
    Measurable (termBracket i l c r θ hr) := by
  have hm₁ := measurable_monomialInput_twistedEllipticElt i l r θ hr
  have hm₂ := measurable_monomialInput_twistedEllipticElt i l r (-θ) hr
  have hcm := hc.measurable
  have hns : Measurable Complex.normSq := Complex.continuous_normSq.measurable
  have hinv : Measurable fun q : ℝ × ℂ => ((q.1 : ℝ) : ℂ)⁻¹ :=
    (Complex.measurable_ofReal.comp measurable_fst).inv
  have heq : termBracket i l c r θ hr = fun q : ℝ × ℂ => ((q.1 : ℝ) : ℂ)⁻¹ *
      (c (r * (q.1 ^ 2 + q.1⁻¹ ^ 2 + Complex.normSq q.2 ^ 2 * q.1 ^ 2 + 2 * Complex.normSq q.2 * q.1 ^ 2
            - 2 * Complex.normSq q.2 * Real.cos θ)) *
          (((if hρ : 0 < q.1 then monomialInput i l (twistedEllipticElt r θ q.1 q.2 hr hρ) else 0 : ℝ)) : ℂ) +
        c (r * (q.1 ^ 2 + q.1⁻¹ ^ 2 + Complex.normSq q.2 ^ 2 * q.1 ^ 2 + 2 * Complex.normSq q.2 * q.1 ^ 2
            - 2 * Complex.normSq q.2 * Real.cos (-θ))) *
          (((if hρ : 0 < q.1 then monomialInput i l (twistedEllipticElt r (-θ) q.1 q.2 hr hρ) else 0 : ℝ)) : ℂ)) := by
    funext q
    unfold termBracket
    by_cases hρ : 0 < q.1
    · simp only [dif_pos hρ, invFrobSq_twistedEllipticElt]
    · simp only [dif_neg hρ]
      simp
  rw [heq]
  fun_prop

private theorem integrableOn_termBracket_integral (i l : ℕ) (c : ℝ → ℂ) (hc : Continuous c) (hcs : HasCompactSupport c)
    (r θ : ℝ) (hr : 0 < r) (hθ : Real.cos θ < 1) :
    MeasureTheory.IntegrableOn (fun ρ : ℝ => ∫ u : ℂ, termBracket i l c r θ hr (ρ, u)) (Set.Ioi (0 : ℝ)) := by
  obtain ⟨Mc, hMc⟩ := hc.bounded_above_of_compact_support hcs
  have hMc0 : 0 ≤ Mc := (norm_nonneg _).trans (hMc 0)
  obtain ⟨L, hL⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  have hc0 : ∀ T : ℝ, L < T → c T = 0 := by
    intro T hT
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hL hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith [le_abs_self T]
  obtain ⟨s, hs⟩ := disc_of_level r θ hθ L
  obtain ⟨ρ₀, ρ₁, hρ₀, hIcc⟩ := exists_Icc_of_invFrobSq_twistedEllipticElt_le r θ hr hθ L
  have hvanish : ∀ (ρ : ℝ) (u : ℂ), u ∉ Metric.closedBall (0 : ℂ) s → termBracket i l c r θ hr (ρ, u) = 0 := by
    intro ρ u hu
    unfold termBracket
    by_cases hρ : 0 < ρ
    · simp only [dif_pos hρ]
      obtain ⟨h1, h2⟩ := hs ρ hρ u hu hr
      rw [hc0 _ h1, hc0 _ h2]
      simp
    · simp only [dif_neg hρ]
  have hmeasρ : MeasureTheory.AEStronglyMeasurable (fun ρ : ℝ => ∫ u : ℂ, termBracket i l c r θ hr (ρ, u))
      MeasureTheory.volume :=
    (measurable_termBracket i l c hc r θ hr).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hbox : MeasureTheory.IntegrableOn (fun ρ : ℝ => ∫ u : ℂ, termBracket i l c r θ hr (ρ, u))
      (Set.Icc ρ₀ ρ₁) := by
    refine MeasureTheory.Measure.integrableOn_of_bounded (by simp) hmeasρ
      (M := ρ₀⁻¹ * (Mc + Mc) * MeasureTheory.volume.real (Metric.closedBall (0 : ℂ) s)) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun ρ hρI => ?_
    have hρ : 0 < ρ := lt_of_lt_of_le hρ₀ hρI.1
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.closedBall (0 : ℂ) s)
      (fun u hu => hvanish ρ u hu)]
    refine MeasureTheory.norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top fun u _ => ?_
    unfold termBracket
    simp only [dif_pos hρ]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    have hinv : ρ⁻¹ ≤ ρ₀⁻¹ := inv_anti₀ hρ₀ hρI.1
    have hone : ∀ θ'' : ℝ, ‖c (invFrobSq (twistedEllipticElt r θ'' ρ u hr hρ)) *
        ((monomialInput i l (twistedEllipticElt r θ'' ρ u hr hρ) : ℝ) : ℂ)‖ ≤ Mc := by
      intro θ''
      rw [norm_mul, Complex.norm_real]
      calc _ ≤ Mc * 1 := mul_le_mul (hMc _) (norm_monomialInput_twistedEllipticElt_le_one i l r θ'' ρ u hr hρ)
            (norm_nonneg _) hMc0
        _ = Mc := mul_one Mc
    have hsum := (norm_add_le _ _).trans (add_le_add (hone θ) (hone (-θ)))
    exact mul_le_mul hinv hsum (norm_nonneg _) (inv_nonneg.2 hρ₀.le)
  refine hbox.of_forall_diff_eq_zero measurableSet_Ioi fun ρ hρd => ?_
  obtain ⟨hρ, hnot⟩ := hρd
  have hρ' : 0 < ρ := hρ
  have hzero : ∀ u : ℂ, termBracket i l c r θ hr (ρ, u) = 0 := by
    intro u
    unfold termBracket
    simp only [dif_pos hρ']
    have h1 : L < invFrobSq (twistedEllipticElt r θ ρ u hr hρ') := by
      by_contra hle
      exact hnot (hIcc ρ u hρ' (not_lt.1 hle))
    have h2 : L < invFrobSq (twistedEllipticElt r (-θ) ρ u hr hρ') := by
      rwa [invFrobSq_twistedEllipticElt_neg]
    rw [hc0 _ h1, hc0 _ h2]
    simp
  simp only [hzero, MeasureTheory.integral_zero]

private theorem twistedEllipticTransform_slice_eq_sum {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (p : P)
    (a : ℕ) (C : P → ℕ → ℕ → ℝ → ℝ → ℂ) (O : P → GL (Fin 2) ℂ → ℂ)
    (hC : ∀ p i l, ContinuousOn (fun q : ℝ × ℝ => C p i l q.1 q.2) normDetCone)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (hCK : ∀ p i l, ∀ q : ℝ × ℝ, q ∉ K → C p i l q.1 q.2 = 0)
    (hO : ∀ p g, O p (conjEntries g) = - O p g)
    (hexp : ∀ g ∈ distinctSingularValues,
      unitaryAverage (fun k => parameterSlice Φ p (k⁻¹ * g * conjEntries k)) =
        (∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
          C p i l (invFrobSq g) (invAbsDet g) * ((monomialInput i l g : ℝ) : ℂ)) + O p g)
    (r θ : ℝ) (hr : 0 < r) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    twistedEllipticTransform (sliceAt Φ p) r θ =
      ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
        ellipticFibreSide i l (levelProfile (C p i l) r) r θ := by
  have hcos : Real.cos θ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2.le hθ.1
    rwa [Real.cos_zero] at this
  have hcos' : Real.cos (-θ) < 1 := by rwa [Real.cos_neg]
  have hcoef : ∀ (i l : ℕ) (θ' ρ : ℝ) (u : ℂ) (hρ : 0 < ρ),
      C p i l (invFrobSq (twistedEllipticElt r θ' ρ u hr hρ)) (invAbsDet (twistedEllipticElt r θ' ρ u hr hρ)) =
        levelProfile (C p i l) r (invFrobSq (twistedEllipticElt r θ' ρ u hr hρ)) := by
    intro i l θ' ρ u hρ
    rw [levelProfile_of_le (C p i l) (two_r_le_invFrobSq_twistedEllipticElt r θ' ρ u hr hρ),
      invAbsDet_twistedEllipticElt]
  have hprof_cont : ∀ i l : ℕ, Continuous (levelProfile (C p i l) r) := fun i l =>
    continuous_levelProfile (C p i l) hr (hC p i l)
  have hprof_supp : ∀ i l : ℕ, HasCompactSupport (levelProfile (C p i l) r) := fun i l =>
    hasCompactSupport_levelProfile (C p i l) r hK (hCK p i l)
  have hterm_int : ∀ (i l : ℕ) (θ' : ℝ), Real.cos θ' < 1 → ∀ (ρ : ℝ) (hρ : 0 < ρ),
      MeasureTheory.Integrable fun u : ℂ => levelProfile (C p i l) r (invFrobSq (twistedEllipticElt r θ' ρ u hr hρ)) *
        ((monomialInput i l (twistedEllipticElt r θ' ρ u hr hρ) : ℝ) : ℂ) :=
    fun i l θ' hθ' ρ hρ => integrable_term_elliptic i l _ (hprof_cont i l) (hprof_supp i l) r θ' ρ hr hρ hθ'
  have hsum_int : ∀ θ' : ℝ, Real.cos θ' < 1 → ∀ (ρ : ℝ) (hρ : 0 < ρ),
      MeasureTheory.Integrable fun u : ℂ => ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
        C p i l (invFrobSq (twistedEllipticElt r θ' ρ u hr hρ)) (invAbsDet (twistedEllipticElt r θ' ρ u hr hρ)) *
          ((monomialInput i l (twistedEllipticElt r θ' ρ u hr hρ) : ℝ) : ℂ) := by
    intro θ' hθ' ρ hρ
    refine MeasureTheory.integrable_finsetSum _ fun i _ => MeasureTheory.integrable_finsetSum _ fun l _ => ?_
    refine (hterm_int i l θ' hθ' ρ hρ).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only []
    rw [hcoef i l θ' ρ u hρ]
  have hodd_int : ∀ θ' : ℝ, Real.cos θ' < 1 → ∀ (ρ : ℝ) (hρ : 0 < ρ),
      MeasureTheory.Integrable fun u : ℂ => O p (twistedEllipticElt r θ' ρ u hr hρ) := by
    intro θ' hθ' ρ hρ
    have havg := integrable_unitaryAverage_slice_elliptic Φ hΦs.continuous hΦc p r θ' ρ hr hρ hθ'
    refine (havg.sub (hsum_int θ' hθ' ρ hρ)).congr ?_
    filter_upwards [ae_gap_ne_zero θ' ρ hρ] with u hu
    have h0 : 0 ≤ ρ ^ 2 * Complex.normSq u ^ 2 + (2 * ρ ^ 2 - 2 * Real.cos θ') * Complex.normSq u
        + (ρ ^ 2 + ρ⁻¹ ^ 2 - 2) := by
      have hinv : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ.ne'
      nlinarith [sq_nonneg (ρ * (Complex.normSq u + 1) - ρ⁻¹),
        mul_nonneg (Complex.normSq_nonneg u) (sub_nonneg.mpr (Real.cos_le_one θ'))]
    have hmem := twistedEllipticElt_mem_distinctSingularValues r θ' ρ u hr hρ (lt_of_le_of_ne h0 (Ne.symm hu))
    have := hexp _ hmem
    simp only [parameterSlice] at this
    simp only [Pi.sub_apply]
    rw [this]
    ring
  have hterm : ∀ i l : ℕ, (4 * Real.sin θ ^ 2 : ℂ) *
        ∫ ρ in Set.Ioi (0 : ℝ), ∫ u : ℂ, termBracket i l (levelProfile (C p i l) r) r θ hr (ρ, u) =
      ellipticFibreSide i l (levelProfile (C p i l) r) r θ := by
    intro i l
    have hfibreSides := (twistedTransforms_monomialInput_eq_fibreSides i l (levelProfile (C p i l) r) (hprof_cont i l)
      (hprof_supp i l) 1 1 r θ one_pos one_pos hr hθ).2
    rw [← hfibreSides]
    unfold twistedEllipticTransform
    rw [dif_pos hr]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [termBracket]
    by_cases hρ : 0 < ρ
    · simp only [dif_pos hρ]
      rw [ChartInvariance.average_conj_invariant, ChartInvariance.average_conj_invariant]
    · simp only [dif_neg hρ]
  unfold twistedEllipticTransform
  rw [dif_pos hr]
  have hseam := integral_twistedEllipticElt_bracket_congr_of_eqOn_distinctSingularValues
    (fun g => unitaryAverage fun k => sliceAt Φ p (k⁻¹ * g * conjEntries k))
    (fun g => (∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
      C p i l (invFrobSq g) (invAbsDet g) * ((monomialInput i l g : ℝ) : ℂ)) + O p g)
    (fun g hg => hexp g hg) r θ hr
  rw [hseam]
  have hinner : ∀ ρ : ℝ, (∫ u : ℂ, if hρ : 0 < ρ then (ρ : ℂ)⁻¹ *
        (((∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
            C p i l (invFrobSq (twistedEllipticElt r θ ρ u hr hρ)) (invAbsDet (twistedEllipticElt r θ ρ u hr hρ)) *
              ((monomialInput i l (twistedEllipticElt r θ ρ u hr hρ) : ℝ) : ℂ)) +
            O p (twistedEllipticElt r θ ρ u hr hρ)) +
          ((∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
            C p i l (invFrobSq (twistedEllipticElt r (-θ) ρ u hr hρ))
                (invAbsDet (twistedEllipticElt r (-θ) ρ u hr hρ)) *
              ((monomialInput i l (twistedEllipticElt r (-θ) ρ u hr hρ) : ℝ) : ℂ)) +
            O p (twistedEllipticElt r (-θ) ρ u hr hρ))) else 0) =
      ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
        ∫ u : ℂ, termBracket i l (levelProfile (C p i l) r) r θ hr (ρ, u) := by
    intro ρ
    by_cases hρ : 0 < ρ
    · simp only [dif_pos hρ, termBracket]
      have hpt : ∀ u : ℂ, (ρ : ℂ)⁻¹ *
          (((∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
              C p i l (invFrobSq (twistedEllipticElt r θ ρ u hr hρ)) (invAbsDet (twistedEllipticElt r θ ρ u hr hρ)) *
                ((monomialInput i l (twistedEllipticElt r θ ρ u hr hρ) : ℝ) : ℂ)) +
              O p (twistedEllipticElt r θ ρ u hr hρ)) +
            ((∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
              C p i l (invFrobSq (twistedEllipticElt r (-θ) ρ u hr hρ))
                  (invAbsDet (twistedEllipticElt r (-θ) ρ u hr hρ)) *
                ((monomialInput i l (twistedEllipticElt r (-θ) ρ u hr hρ) : ℝ) : ℂ)) +
              O p (twistedEllipticElt r (-θ) ρ u hr hρ))) =
          (∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i), (ρ : ℂ)⁻¹ *
            (levelProfile (C p i l) r (invFrobSq (twistedEllipticElt r θ ρ u hr hρ)) *
                ((monomialInput i l (twistedEllipticElt r θ ρ u hr hρ) : ℝ) : ℂ) +
              levelProfile (C p i l) r (invFrobSq (twistedEllipticElt r (-θ) ρ u hr hρ)) *
                ((monomialInput i l (twistedEllipticElt r (-θ) ρ u hr hρ) : ℝ) : ℂ))) +
            (ρ : ℂ)⁻¹ * (O p (twistedEllipticElt r θ ρ u hr hρ) + O p (twistedEllipticElt r (-θ) ρ u hr hρ)) := by
        intro u
        simp only [fun i l => hcoef i l θ ρ u hρ, fun i l => hcoef i l (-θ) ρ u hρ]
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
        ring
      simp_rw [hpt]
      have hT : ∀ i l : ℕ, MeasureTheory.Integrable fun u : ℂ =>
          (ρ : ℂ)⁻¹ * (levelProfile (C p i l) r (invFrobSq (twistedEllipticElt r θ ρ u hr hρ)) *
              ((monomialInput i l (twistedEllipticElt r θ ρ u hr hρ) : ℝ) : ℂ) +
            levelProfile (C p i l) r (invFrobSq (twistedEllipticElt r (-θ) ρ u hr hρ)) *
              ((monomialInput i l (twistedEllipticElt r (-θ) ρ u hr hρ) : ℝ) : ℂ)) := by
        intro i l
        have h := ((hterm_int i l θ hcos ρ hρ).add (hterm_int i l (-θ) hcos' ρ hρ)).const_mul ((ρ : ℂ)⁻¹)
        simpa only [Pi.add_apply] using h
      have hS : MeasureTheory.Integrable fun u : ℂ => ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
          (ρ : ℂ)⁻¹ * (levelProfile (C p i l) r (invFrobSq (twistedEllipticElt r θ ρ u hr hρ)) *
              ((monomialInput i l (twistedEllipticElt r θ ρ u hr hρ) : ℝ) : ℂ) +
            levelProfile (C p i l) r (invFrobSq (twistedEllipticElt r (-θ) ρ u hr hρ)) *
              ((monomialInput i l (twistedEllipticElt r (-θ) ρ u hr hρ) : ℝ) : ℂ)) :=
        MeasureTheory.integrable_finsetSum _ fun i _ => MeasureTheory.integrable_finsetSum _ fun l _ => hT i l
      have hOdd : MeasureTheory.Integrable fun u : ℂ => (ρ : ℂ)⁻¹ *
          (O p (twistedEllipticElt r θ ρ u hr hρ) + O p (twistedEllipticElt r (-θ) ρ u hr hρ)) := by
        have h := ((hodd_int θ hcos ρ hρ).add (hodd_int (-θ) hcos' ρ hρ)).const_mul ((ρ : ℂ)⁻¹)
        simpa only [Pi.add_apply] using h
      rw [MeasureTheory.integral_add hS hOdd,
        integral_twistedEllipticElt_two_sheets_eq_zero_of_odd (O p) (hO p) r θ ρ hr hρ _, add_zero,
        MeasureTheory.integral_finsetSum _ fun i _ => MeasureTheory.integrable_finsetSum _ fun l _ => hT i l]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MeasureTheory.integral_finsetSum _ fun l _ => hT i l]
    · simp only [dif_neg hρ, termBracket, MeasureTheory.integral_zero, Finset.sum_const_zero]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun ρ _ => hinner ρ]
  have hsliceInt : ∀ i l : ℕ, MeasureTheory.IntegrableOn
      (fun ρ : ℝ => ∫ u : ℂ, termBracket i l (levelProfile (C p i l) r) r θ hr (ρ, u)) (Set.Ioi (0 : ℝ)) :=
    fun i l => integrableOn_termBracket_integral i l _ (hprof_cont i l) (hprof_supp i l) r θ hr hcos
  rw [MeasureTheory.integral_finsetSum _ fun i _ => MeasureTheory.integrable_finsetSum _ fun l _ => hsliceInt i l,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun l _ => hsliceInt i l, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => hterm i l

section
open MeasureTheory

private theorem continuous_fibreArcIntegral (i l : ℕ) : Continuous (fibreArcIntegral i l) := by
  unfold fibreArcIntegral
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun ψ : ℝ => Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l)) volume a b :=
    fun a b => (by fun_prop :
      Continuous fun ψ : ℝ => Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l)).intervalIntegrable a b
  have hprim := intervalIntegral.continuous_primitive hint 0
  have hsplit : ∀ Ψ : ℝ, (∫ ψ in (-(Ψ / 2))..(Ψ / 2), Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l)) =
      (∫ ψ in (0 : ℝ)..(Ψ / 2), Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l)) -
        ∫ ψ in (0 : ℝ)..(-(Ψ / 2)), Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l) := by
    intro Ψ
    rw [intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
  simp_rw [hsplit]
  exact (hprim.comp (by fun_prop)).sub (hprim.comp (by fun_prop))

private theorem measurable_ellipticFibreTerm_pair (i l : ℕ) (r : ℝ) :
    Measurable fun q : ℝ × ℝ => ellipticFibreTerm i l q.2 r q.1 := by
  have hF : Measurable (fibreArcIntegral i l) := (continuous_fibreArcIntegral i l).measurable
  have hacos : Measurable Real.arccos := Real.continuous_arccos.measurable
  unfold ellipticFibreTerm fibreMonomialFactor ellipticArcLength
  fun_prop

private theorem measurable_splitFibreTerm_pair (i l : ℕ) (r : ℝ) :
    Measurable fun q : ℝ × ℝ => splitFibreTerm i l q.1 (r * Real.exp q.2) (r * Real.exp (-q.2)) := by
  unfold splitFibreTerm fibreMonomialFactor
  fun_prop

private theorem exists_bound_chebyshevU_cos (k : ℕ) :
    ∃ MU : ℝ, 0 ≤ MU ∧ ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      ‖(((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)‖ ≤ MU := by
  have hcont : Continuous fun θ : ℝ => (Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) :=
    (Chebyshev.U ℝ ((k : ℤ) - 2)).continuous.comp Real.continuous_cos
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun θ hθ => ?_⟩
  rw [Complex.norm_real]
  exact (hM θ hθ).trans (le_max_left _ _)

private theorem integrable_swap1 (i l k : ℕ) (c : ℝ → ℂ) (hc : Continuous c) (hcs : HasCompactSupport c) {r : ℝ}
    (hr : 0 < r) :
    Integrable (fun q : ℝ × ℝ => c q.2 * ellipticFibreTerm i l q.2 r q.1 *
        (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos q.1) : ℝ) : ℂ))
      ((volume.restrict (Set.Ioo (0 : ℝ) Real.pi)).prod (volume.restrict (Set.Ioi (2 * r)))) := by
  obtain ⟨Mc, hMc⟩ := hc.bounded_above_of_compact_support hcs
  obtain ⟨MU, hMU0, hMU⟩ := exists_bound_chebyshevU_cos k
  obtain ⟨L, hL⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hmeas : Measurable fun q : ℝ × ℝ => c q.2 * ellipticFibreTerm i l q.2 r q.1 *
      (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos q.1) : ℝ) : ℂ) := by
    have h1 := measurable_ellipticFibreTerm_pair i l r
    have h2 : Measurable fun θ : ℝ => (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) :=
      (Complex.continuous_ofReal.comp
        ((Chebyshev.U ℝ ((k : ℤ) - 2)).continuous.comp Real.continuous_cos)).measurable
    have h3 := hc.measurable
    fun_prop
  have hbox : IntegrableOn (fun q : ℝ × ℝ => c q.2 * ellipticFibreTerm i l q.2 r q.1 *
      (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos q.1) : ℝ) : ℂ))
      (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Ioc (2 * r) L) volume := by
    refine Measure.integrableOn_of_bounded ?_ hmeas.aestronglyMeasurable (M := Mc * (4 * Real.pi ^ 2 / r) * MU) ?_
    · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · refine ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioc) fun q hq => ?_
      obtain ⟨hθ, hT⟩ := hq
      have hMc0 : 0 ≤ Mc := (norm_nonneg _).trans (hMc 0)
      rw [norm_mul, norm_mul]
      have hterm := norm_ellipticFibreTerm_le i l q.2 r q.1 hr hT.1
      have hU := hMU q.1 ⟨hθ.1.le, hθ.2.le⟩
      gcongr
      exact hMc _
  refine hbox.of_forall_diff_eq_zero (measurableSet_Ioo.prod measurableSet_Ioi) fun q hq => ?_
  obtain ⟨⟨hθ, hT⟩, hnot⟩ := hq
  have hTL : L < q.2 := by
    by_contra hle
    exact hnot ⟨hθ, hT, not_lt.1 hle⟩
  have hc0 : c q.2 = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hL hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith [le_abs_self q.2]
  simp [hc0]

private theorem integrableOn_ellipticFibreSide_mul' (i l k : ℕ) (c : ℝ → ℂ) (hc : Continuous c) (hcs :
    HasCompactSupport c)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn
      (fun θ : ℝ => ellipticFibreSide i l c r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))
      (Set.Ioo (0 : ℝ) Real.pi) := by
  have h := (integrable_swap1 i l k c hc hcs hr).integral_prod_left
  refine h.congr (Filter.Eventually.of_forall fun θ => ?_)
  simp only [ellipticFibreSide]
  exact (integral_mul_const _ _)

private def levelRegion (r : ℝ) : Set (ℝ × ℝ) := {q | r * Real.exp q.2 + r * Real.exp (-q.2) < q.1}

private theorem measurableSet_levelRegion (r : ℝ) : MeasurableSet (levelRegion r) :=
  measurableSet_lt (by fun_prop) measurable_fst

private noncomputable def swap2Integrand (i l k : ℕ) (c : ℝ → ℂ) (r : ℝ) : ℝ × ℝ → ℂ :=
  (levelRegion r).indicator fun q => c q.1 * ((Real.exp (-(((k : ℝ) - 1) * |q.2|)) : ℝ) : ℂ) *
    splitFibreTerm i l q.1 (r * Real.exp q.2) (r * Real.exp (-q.2))

private theorem measurable_swap2Integrand (i l k : ℕ) (c : ℝ → ℂ) (hc : Continuous c) (r : ℝ) :
    Measurable (swap2Integrand i l k c r) := by
  unfold swap2Integrand
  refine Measurable.indicator ?_ (measurableSet_levelRegion r)
  have h1 := measurable_splitFibreTerm_pair i l r
  have h2 := hc.measurable
  fun_prop

private theorem integrable_swap2 (i l k : ℕ) (hk : 1 ≤ k) (c : ℝ → ℂ) (hc : Continuous c) (hcs : HasCompactSupport c)
    {r : ℝ} (hr : 0 < r) :
    Integrable (swap2Integrand i l k c r) ((volume.restrict (Set.Ioi (2 * r))).prod volume) := by
  obtain ⟨Mc, hMc⟩ := hc.bounded_above_of_compact_support hcs
  obtain ⟨L, hL⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  have hMc0 : 0 ≤ Mc := (norm_nonneg _).trans (hMc 0)
  set A : ℝ := Real.arcosh (max 1 (L / (2 * r))) with hA
  have hmeas := measurable_swap2Integrand i l k c hc r
  have hprod :=
    Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (Set.Ioi (2 * r)) Set.univ
  rw [Measure.restrict_univ] at hprod
  rw [hprod, ← Measure.volume_eq_prod]
  have hbox : IntegrableOn (swap2Integrand i l k c r) (Set.Ioc (2 * r) L ×ˢ Set.Icc (-A) A) volume := by
    refine Measure.integrableOn_of_bounded ?_ hmeas.aestronglyMeasurable (M := Mc * 1 * Real.pi) ?_
    · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, Real.volume_Icc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Icc) fun q _ => ?_
      unfold swap2Integrand
      by_cases hq : q ∈ levelRegion r
      · rw [Set.indicator_of_mem hq, norm_mul, norm_mul]
        have hsplit := norm_splitFibreTerm_le i l (T := q.1) (by positivity) (by positivity) hq
        have hexp : ‖((Real.exp (-(((k : ℝ) - 1) * |q.2|)) : ℝ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          have hk' : (1 : ℝ) ≤ k := Nat.one_le_cast.2 hk
          exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (by linarith) (abs_nonneg _)))
        gcongr
        exact hMc _
      · rw [Set.indicator_of_notMem hq, norm_zero]
        positivity
  refine hbox.of_forall_diff_eq_zero (measurableSet_Ioi.prod MeasurableSet.univ) fun q hq => ?_
  obtain ⟨⟨hT, -⟩, hnot⟩ := hq
  unfold swap2Integrand
  by_cases hreg : q ∈ levelRegion r
  · rw [Set.indicator_of_mem hreg]
    by_cases hTL : q.1 ≤ L
    · exfalso
      apply hnot
      refine ⟨⟨hT, hTL⟩, ?_⟩
      have hreg' : r * Real.exp q.2 + r * Real.exp (-q.2) < q.1 := hreg
      have hmem := (exp_add_exp_neg_lt_iff_mem_Ioo_arcosh r q.1 q.2 hr hT.le).1 hreg'
      have hmono : Real.arcosh (q.1 / (2 * r)) ≤ A := by
        have hx : 0 < q.1 / (2 * r) := div_pos (by linarith [Set.mem_Ioi.1 hT]) (by positivity)
        refine (Real.arcosh_le_arcosh hx (lt_of_lt_of_le one_pos (le_max_left _ _))).2 ?_
        exact le_trans (div_le_div_of_nonneg_right hTL (by positivity)) (le_max_right _ _)
      exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    · have hc0 : c q.1 = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have := hL hmem
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
        exact hTL (le_trans (le_abs_self _) this)
      simp [hc0]
  · rw [Set.indicator_of_notMem hreg]

private theorem swap2_inner_eq (i l k : ℕ) (c : ℝ → ℂ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (∫ T in Set.Ioi (2 * r), swap2Integrand i l k c r (T, t)) =
      (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreSide i l c (r * Real.exp t) (r * Real.exp (-t)) := by
  unfold swap2Integrand splitFibreSide
  have hind : ∀ T : ℝ, (levelRegion r).indicator (fun q : ℝ × ℝ =>
        c q.1 * ((Real.exp (-(((k : ℝ) - 1) * |q.2|)) : ℝ) : ℂ) *
          splitFibreTerm i l q.1 (r * Real.exp q.2) (r * Real.exp (-q.2))) (T, t) =
      (Set.Ioi (r * Real.exp t + r * Real.exp (-t))).indicator (fun T =>
        c T * ((Real.exp (-(((k : ℝ) - 1) * |t|)) : ℝ) : ℂ) *
          splitFibreTerm i l T (r * Real.exp t) (r * Real.exp (-t))) T := by
    intro T
    by_cases h : r * Real.exp t + r * Real.exp (-t) < T
    · rw [Set.indicator_of_mem (show (T, t) ∈ levelRegion r from h), Set.indicator_of_mem (Set.mem_Ioi.2 h)]
    · rw [Set.indicator_of_notMem (show (T, t) ∉ levelRegion r from h),
        Set.indicator_of_notMem (by simpa using h)]
  simp_rw [hind]
  have hsub : Set.Ioi (r * Real.exp t + r * Real.exp (-t)) ⊆ Set.Ioi (2 * r) := by
    apply Set.Ioi_subset_Ioi
    have : r * Real.exp t + r * Real.exp (-t) = 2 * r * Real.cosh t := by rw [Real.cosh_eq]; ring
    rw [this]
    nlinarith [Real.one_le_cosh t]
  rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.2 hsub]
  have hseam : (∫ T in Set.Ioi (r * Real.exp t + r * Real.exp (-t)),
      ((Real.exp (-(((k : ℝ) - 1) * |t|)) : ℝ) : ℂ) *
        (c T * splitFibreTerm i l T (r * Real.exp t) (r * Real.exp (-t)))) =
        ((Real.exp (-(((k : ℝ) - 1) * |t|)) : ℝ) : ℂ) * ∫ T in Set.Ioi (r * Real.exp t + r * Real.exp (-t)),
          c T * splitFibreTerm i l T (r * Real.exp t) (r * Real.exp (-t)) :=
    integral_const_mul _ _
  rw [← hseam]
  refine integral_congr_ae (Filter.Eventually.of_forall fun T => ?_)
  simp only []
  ring

private theorem integrable_exp_mul_splitFibreSide (i l k : ℕ) (hk : 2 ≤ k) (c : ℝ → ℂ) (hc : Continuous c)
    (hcs : HasCompactSupport c) {r : ℝ} (hr : 0 < r) :
    Integrable fun t : ℝ => (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) *
      splitFibreSide i l c (r * Real.exp t) (r * Real.exp (-t)) := by
  have h := (integrable_swap2 i l k (by omega) c hc hcs hr).integral_prod_right
  exact h.congr (Filter.Eventually.of_forall fun t => swap2_inner_eq i l k c hr t)

private theorem swap1_inner_eq (i l k : ℕ) (hk : i + l + 2 ≤ k) (c : ℝ → ℂ) {r : ℝ} (hr : 0 < r) {T : ℝ}
    (hT : 2 * r < T) :
    (∫ θ in Set.Ioo (0 : ℝ) Real.pi, c T * ellipticFibreTerm i l T r θ *
        (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
      (2 * Real.pi / r : ℂ) * ∫ t : ℝ, swap2Integrand i l k c r (T, t) := by
  have hpairing_shift := ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing_of_add_two_le i l k hk r T hr hT.le
  have hA : 0 ≤ Real.arcosh (T / (2 * r)) :=
    Real.arcosh_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  have h1 : (∫ θ in Set.Ioo (0 : ℝ) Real.pi, c T * (ellipticFibreTerm i l T r θ *
        (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))) =
      c T * ∫ θ in Set.Ioo (0 : ℝ) Real.pi, ellipticFibreTerm i l T r θ *
        (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) := integral_const_mul _ _
  have h2 : (∫ θ in Set.Ioo (0 : ℝ) Real.pi, ellipticFibreTerm i l T r θ *
        (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
      ∫ θ in (0 : ℝ)..Real.pi, ellipticFibreTerm i l T r θ *
        (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
  have h3 : (∫ t in (-Real.arcosh (T / (2 * r)))..Real.arcosh (T / (2 * r)),
        (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreTerm i l T (r * Real.exp t) (r * Real.exp (-t))) =
      ∫ t : ℝ, (Set.Ioo (-Real.arcosh (T / (2 * r))) (Real.arcosh (T / (2 * r)))).indicator (fun t =>
        (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreTerm i l T (r * Real.exp t) (r * Real.exp (-t))) t := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
      integral_indicator measurableSet_Ioo]
  have h4 : ∀ t : ℝ, swap2Integrand i l k c r (T, t) = c T *
      (Set.Ioo (-Real.arcosh (T / (2 * r))) (Real.arcosh (T / (2 * r)))).indicator (fun t =>
        (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreTerm i l T (r * Real.exp t) (r * Real.exp (-t))) t := by
    intro t
    unfold swap2Integrand
    have hiff : (T, t) ∈ levelRegion r ↔ t ∈ Set.Ioo (-Real.arcosh (T / (2 * r))) (Real.arcosh (T / (2 * r))) :=
      exp_add_exp_neg_lt_iff_mem_Ioo_arcosh r T t hr hT.le
    by_cases h : (T, t) ∈ levelRegion r
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.1 h)]
      push_cast
      ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hiff.2 h')), mul_zero]
  have h5 : (∫ t : ℝ, swap2Integrand i l k c r (T, t)) = c T * ∫ t : ℝ,
      (Set.Ioo (-Real.arcosh (T / (2 * r))) (Real.arcosh (T / (2 * r)))).indicator (fun t =>
        (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreTerm i l T (r * Real.exp t) (r * Real.exp (-t))) t := by
    simp_rw [h4]
    exact integral_const_mul _ _
  calc (∫ θ in Set.Ioo (0 : ℝ) Real.pi, c T * ellipticFibreTerm i l T r θ *
          (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))
      = ∫ θ in Set.Ioo (0 : ℝ) Real.pi, c T * (ellipticFibreTerm i l T r θ *
          (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        simp only []
        ring
    _ = c T * ((2 * Real.pi / r : ℂ) * ∫ t : ℝ,
          (Set.Ioo (-Real.arcosh (T / (2 * r))) (Real.arcosh (T / (2 * r)))).indicator (fun t =>
            (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) *
              splitFibreTerm i l T (r * Real.exp t) (r * Real.exp (-t))) t) := by
        rw [h1, h2, hpairing_shift, h3]
    _ = (2 * Real.pi / r : ℂ) * ∫ t : ℝ, swap2Integrand i l k c r (T, t) := by
        rw [h5]
        ring

private theorem integrableOn_ellipticFibreSide_mul (i l k : ℕ) (c : ℝ → ℂ) (hc : Continuous c) (hcs :
    HasCompactSupport c)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn
      (fun θ : ℝ => ellipticFibreSide i l c r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))
      (Set.Ioo (0 : ℝ) Real.pi) :=
  integrableOn_ellipticFibreSide_mul' i l k c hc hcs hr

private theorem pairing_term_eq {i l k : ℕ} (hk : i + l + 2 ≤ k) (c : ℝ → ℂ) (hc : Continuous c)
    (hcs : HasCompactSupport c) {r : ℝ} (hr : 0 < r) :
    (∫ θ in Set.Ioo (0 : ℝ) Real.pi,
        ellipticFibreSide i l c r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
      (2 * Real.pi / r : ℂ) *
        ∫ t : ℝ, (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) *
          splitFibreSide i l c (r * Real.exp t) (r * Real.exp (-t)) := by
  have hfactor : ∀ θ : ℝ, ellipticFibreSide i l c r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) =
      ∫ T in Set.Ioi (2 * r), c T * ellipticFibreTerm i l T r θ *
        (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) := by
    intro θ
    unfold ellipticFibreSide
    exact (integral_mul_const _ _).symm
  simp_rw [hfactor]
  have hswap1 := integral_integral_swap (μ := volume.restrict (Set.Ioo (0 : ℝ) Real.pi))
    (ν := volume.restrict (Set.Ioi (2 * r)))
    (f := fun θ T => c T * ellipticFibreTerm i l T r θ *
      (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))
    (integrable_swap1 i l k c hc hcs hr)
  rw [hswap1]
  have hinner_swap : (∫ T in Set.Ioi (2 * r), ∫ θ in Set.Ioo (0 : ℝ) Real.pi, c T * ellipticFibreTerm i l T r θ *
        (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
      ∫ T in Set.Ioi (2 * r), (2 * Real.pi / r : ℂ) * ∫ t : ℝ, swap2Integrand i l k c r (T, t) :=
    setIntegral_congr_fun measurableSet_Ioi fun T hT => swap1_inner_eq i l k hk c hr hT
  rw [hinner_swap]
  have hidentify : (∫ T in Set.Ioi (2 * r), (2 * Real.pi / r : ℂ) * ∫ t : ℝ, swap2Integrand i l k c r (T, t)) =
      (2 * Real.pi / r : ℂ) * ∫ T in Set.Ioi (2 * r), ∫ t : ℝ, swap2Integrand i l k c r (T, t) :=
    integral_const_mul _ _
  rw [hidentify]
  congr 1
  have hswap2 := integral_integral_swap (μ := volume.restrict (Set.Ioi (2 * r))) (ν := (volume : Measure ℝ))
    (f := fun T t => swap2Integrand i l k c r (T, t)) (integrable_swap2 i l k (by omega) c hc hcs hr)
  rw [hswap2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => swap2_inner_eq i l k c hr t)

private theorem twistedSplitTransform_neg_neg (φ : GL (Fin 2) ℂ → ℂ) (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (_ha₂ : 0 < a₂) :
    twistedSplitTransform φ (-a₁) (-a₂) = 0 := by
  unfold twistedSplitTransform
  rw [dif_neg]
  rintro ⟨h, -⟩
  linarith

private theorem pairing_eq_zero_of_expansions
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
    (hΦr : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (Matrix.of q.1 * ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), q.2)))) :
    ∃ N : ℕ, ∀ p : P, ∀ k > N, ∀ r > 0,
      discreteSeriesPairing k
        (fun a₁ a₂ => twistedSplitTransform (sliceAt Φ p) a₁ a₂)
        (fun r' θ => twistedEllipticTransform (sliceAt Φ p) r' θ) r = 0 := by
  obtain ⟨a, C, O, hC, ⟨K, hK, hCK⟩, hO, hexp⟩ :=
    exists_monomialExpansion_of_finiteDimensional_rightSpan P Φ hΦs hΦc hΦU hΦr
  refine ⟨2 * a + 1, fun p k hk r hr => ?_⟩
  have hk2 : 2 ≤ k := by omega
  set c : ℕ → ℕ → ℝ → ℂ := fun i l => levelProfile (C p i l) r with hc_def
  have hc_cont : ∀ i l, Continuous (c i l) := fun i l => continuous_levelProfile (C p i l) hr (hC p i l)
  have hc_supp : ∀ i l, HasCompactSupport (c i l) := fun i l =>
    hasCompactSupport_levelProfile (C p i l) r hK (hCK p i l)
  have hH : ∀ t : ℝ, twistedSplitTransform (sliceAt Φ p) (r * Real.exp t) (r * Real.exp (-t)) =
      ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
        splitFibreSide i l (c i l) (r * Real.exp t) (r * Real.exp (-t)) := by
    intro t
    rw [twistedSplitTransform_slice_eq_sum Φ hΦs hΦc p a C O hC K hK hCK hO (hexp p) _ _ (by positivity)
      (by positivity), sqrt_mul_sqrt_exp_neg r t hr]
  have hHneg : ∀ t : ℝ,
      twistedSplitTransform (sliceAt Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t))) = 0 := fun t =>
    twistedSplitTransform_neg_neg _ _ _ (by positivity) (by positivity)
  have hE : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, twistedEllipticTransform (sliceAt Φ p) r θ =
      ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i), ellipticFibreSide i l (c i l) r θ :=
    fun θ hθ => twistedEllipticTransform_slice_eq_sum Φ hΦs hΦc p a C O hC K hK hCK hO (hexp p) r θ hr hθ
  unfold discreteSeriesPairing
  have hθside : (∫ θ in (0 : ℝ)..Real.pi, twistedEllipticTransform (sliceAt Φ p) r θ *
        (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
      ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i), ∫ θ in Set.Ioo (0 : ℝ) Real.pi,
        ellipticFibreSide i l (c i l) r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (g := fun θ =>
      ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
        ellipticFibreSide i l (c i l) r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))]
    · rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        exact MeasureTheory.integral_finsetSum _ fun l _ =>
          integrableOn_ellipticFibreSide_mul i l k (c i l) (hc_cont i l) (hc_supp i l) hr
      · intro i _
        exact MeasureTheory.integrable_finsetSum _ fun l _ =>
          integrableOn_ellipticFibreSide_mul i l k (c i l) (hc_cont i l) (hc_supp i l) hr
    · intro θ hθ
      simp only [hE θ hθ, Finset.sum_mul]
  have htside : (∫ t : ℝ, (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) *
        (twistedSplitTransform (sliceAt Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
          (-1 : ℂ) ^ k * twistedSplitTransform (sliceAt Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t))))) =
      ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i), ∫ t : ℝ,
        (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) *
          splitFibreSide i l (c i l) (r * Real.exp t) (r * Real.exp (-t)) := by
    have hpt : ∀ t : ℝ, (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) *
        (twistedSplitTransform (sliceAt Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
          (-1 : ℂ) ^ k * twistedSplitTransform (sliceAt Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) =
        ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1 - i),
          (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) *
            splitFibreSide i l (c i l) (r * Real.exp t) (r * Real.exp (-t)) := by
      intro t
      rw [hH t, hHneg t, mul_zero, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    simp_rw [hpt]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact MeasureTheory.integral_finsetSum _ fun l _ =>
        integrable_exp_mul_splitFibreSide i l k hk2 (c i l) (hc_cont i l) (hc_supp i l) hr
    · intro i _
      exact MeasureTheory.integrable_finsetSum _ fun l _ =>
        integrable_exp_mul_splitFibreSide i l k hk2 (c i l) (hc_cont i l) (hc_supp i l) hr
  rw [hθside, htside, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun l hl => ?_
  have hil : i + l + 2 ≤ k := by
    have hi' := Finset.mem_range.1 hi
    have hl' := Finset.mem_range.1 hl
    omega
  rw [pairing_term_eq hil (c i l) (hc_cont i l) (hc_supp i l) hr, sub_self]

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted.RightFiniteExpansion"

private theorem exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
    (hΦr : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (Matrix.of q.1 * ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), q.2))))
    (hΦl : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of q.1), q.2)))) :
    ∃ N : ℕ, ∀ p : P, ∀ k > N, ∀ r > 0,
      discreteSeriesPairing k
        (fun a₁ a₂ =>
          twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) a₁ a₂)
        (fun r' θ =>
          twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r' θ)
        r = 0 := by
  have _ := hΦl
  exact pairing_eq_zero_of_expansions P Φ hΦs hΦc hΦU hΦr

end AutomorphicForm.GL2Twisted
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted.RightFiniteExpansion P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm.GL2Twisted.RightFiniteExpansion P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.AutomorphicForm"

theorem solution
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
    (hΦr : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (Matrix.of q.1 * ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), q.2))))
    (hΦl : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of q.1), q.2)))) :
    ∃ N : ℕ, ∀ p : P, ∀ k > N, ∀ r > 0,
      discreteSeriesPairing k
        (fun a₁ a₂ =>
          twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) a₁ a₂)
        (fun r' θ =>
          twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r' θ)
        r = 0 := by
  exact
    exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero
      P Φ hΦs hΦc hΦU hΦr hΦl

end S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero (solution)
