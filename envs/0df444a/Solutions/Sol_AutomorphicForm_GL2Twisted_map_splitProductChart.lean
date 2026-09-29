-- Prove2me | solution 1 for AutomorphicForm.GL2Twisted.map_splitProductChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/87f6295b-347c-50a6-b918-93cca134d544

import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.NoncommRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Twisted_map_splitProductChart
set_option autoImplicit false
open MeasureTheory
p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_GL2Twisted_map_splitProductChart.AutomorphicForm AutomorphicForm.GL2Twisted P2MW.S_AutomorphicForm_GL2Twisted_map_splitProductChart.AutomorphicForm.GL2Twisted"

namespace AutomorphicForm
namespace GL2Twisted
p2m_export "AutomorphicForm.GL2Twisted" "unitaryElt twistedSplitElt"
p2m_open "AutomorphicForm.GL2Twisted AutomorphicForm"

private noncomputable def splitChart : (Fin 2 → Fin 2 → ℂ) → Fin 2 → Fin 2 → ℂ := fun p =>
  Matrix.of.symm
  (((if h : 0 < (p 1 0).re ∧ 0 < (p 1 0).im then
  twistedSplitElt ((p 1 0).re ^ 2) ((p 1 0).im ^ 2) ((p 1 0).re * p 1 1) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ *
  unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im
  else 1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))

private def splitGuard : Set (Fin 2 → Fin 2 → ℂ) := {p : Fin 2 → Fin 2 → ℂ | 0 < (p 1 0).re ∧ 0 < (p 1 0).im}

private def splitDom : Set (Fin 2 → Fin 2 → ℂ) :=
  {p : Fin 2 → Fin 2 → ℂ |
  0 < (p 1 0).re ∧ 0 < (p 1 0).im ∧
  0 < (p 0 0).re ∧ (p 0 0).re < Real.pi ∧ 0 < (p 0 0).im ∧ (p 0 0).im < Real.pi / 2 ∧
  0 < (p 0 1).re ∧ (p 0 1).re < 2 * Real.pi ∧ 0 < (p 0 1).im ∧ (p 0 1).im < 2 * Real.pi}

private def splitClosedBox : Set (Fin 2 → Fin 2 → ℂ) :=
  {p : Fin 2 → Fin 2 → ℂ |
    0 < (p 1 0).re ∧ 0 < (p 1 0).im ∧
    0 ≤ (p 0 0).re ∧ (p 0 0).re ≤ Real.pi ∧ 0 ≤ (p 0 0).im ∧ (p 0 0).im ≤ Real.pi / 2 ∧
    0 ≤ (p 0 1).re ∧ (p 0 1).re ≤ 2 * Real.pi ∧ 0 ≤ (p 0 1).im ∧ (p 0 1).im ≤ 2 * Real.pi}

private def splitLocus : Set (Fin 2 → Fin 2 → ℂ) := {m : Fin 2 → Fin 2 → ℂ | m 0 0 * m 1 1 - m 0 1 * m 1 0 ≠ 0}

private def splitWalls : Set (Fin 2 → Fin 2 → ℂ) :=
    (splitGuard ∩ {p | (p 0 0).re = 0}) ∪
    (splitGuard ∩ {p | (p 0 0).re = Real.pi}) ∪
    (splitGuard ∩ {p | (p 0 0).im = 0}) ∪
    (splitGuard ∩ {p | (p 0 0).im = Real.pi / 2}) ∪
    (splitGuard ∩ {p | (p 0 1).re = 0}) ∪
    (splitGuard ∩ {p | (p 0 1).re = 2 * Real.pi}) ∪
    (splitGuard ∩ {p | (p 0 1).im = 0}) ∪
    (splitGuard ∩ {p | (p 0 1).im = 2 * Real.pi})

private noncomputable def splitDensity (p : Fin 2 → Fin 2 → ℂ) : ℝ :=
  2 * (p 1 0).re ^ 3 * (p 1 0).im ^ 3 * Real.sin (p 0 0).im * Real.cos (p 0 0).im

private theorem continuous_slot_re (i j : Fin 2) : Continuous fun p : Fin 2 → Fin 2 → ℂ => (p i j).re := by
  first
    | fun_prop
    | exact Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply i))

private theorem continuous_slot_im (i j : Fin 2) : Continuous fun p : Fin 2 → Fin 2 → ℂ => (p i j).im := by
  first
    | fun_prop
    | exact Complex.continuous_im.comp ((continuous_apply j).comp (continuous_apply i))

private theorem isOpen_splitGuard : IsOpen splitGuard := by
  unfold splitGuard
  simp only [Set.setOf_and]
  exact (isOpen_lt continuous_const (continuous_slot_re 1 0)).inter
    (isOpen_lt continuous_const (continuous_slot_im 1 0))

private theorem isOpen_splitDom : IsOpen splitDom := by
  unfold splitDom
  simp only [Set.setOf_and]
  exact (isOpen_lt continuous_const (continuous_slot_re 1 0)).inter
    ((isOpen_lt continuous_const (continuous_slot_im 1 0)).inter
      ((isOpen_lt continuous_const (continuous_slot_re 0 0)).inter
        ((isOpen_lt (continuous_slot_re 0 0) continuous_const).inter
          ((isOpen_lt continuous_const (continuous_slot_im 0 0)).inter
            ((isOpen_lt (continuous_slot_im 0 0) continuous_const).inter
              ((isOpen_lt continuous_const (continuous_slot_re 0 1)).inter
                ((isOpen_lt (continuous_slot_re 0 1) continuous_const).inter
                  ((isOpen_lt continuous_const (continuous_slot_im 0 1)).inter
                    (isOpen_lt (continuous_slot_im 0 1) continuous_const)))))))))

private theorem measurableSet_splitDom : MeasurableSet splitDom := isOpen_splitDom.measurableSet

private theorem splitDom_subset_guard : splitDom ⊆ splitGuard := fun _ hp => ⟨hp.1, hp.2.1⟩

private theorem splitWalls_subset_guard : splitWalls ⊆ splitGuard := by
  rintro p (((((((h | h) | h) | h) | h) | h) | h) | h) <;> exact h.1

private theorem splitClosedBox_subset : splitClosedBox ⊆ splitDom ∪ splitWalls := by
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  have hg : p ∈ splitGuard := ⟨h1, h2⟩
  unfold splitWalls
  rcases h3.eq_or_lt with e3 | l3
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hg, e3.symm⟩)))))))
  rcases h4.eq_or_lt with e4 | l4
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hg, e4⟩)))))))
  rcases h5.eq_or_lt with e5 | l5
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hg, e5.symm⟩))))))
  rcases h6.eq_or_lt with e6 | l6
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hg, e6⟩)))))
  rcases h7.eq_or_lt with e7 | l7
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨hg, e7.symm⟩))))
  rcases h8.eq_or_lt with e8 | l8
  · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨hg, e8⟩)))
  rcases h9.eq_or_lt with e9 | l9
  · exact Or.inr (Or.inl (Or.inr ⟨hg, e9.symm⟩))
  rcases h10.eq_or_lt with e10 | l10
  · exact Or.inr (Or.inr ⟨hg, e10⟩)
  exact Or.inl ⟨h1, h2, l3, l4, l5, l6, l7, l8, l9, l10⟩

private theorem exists_angle_pair_of_unit (a : ℂ) (b : ℝ) (hb : 0 ≤ b) (h : Complex.normSq a + b ^ 2 = 1) :
    ∃ η ξ₁ : ℝ, 0 ≤ η ∧ η ≤ Real.pi / 2 ∧ 0 ≤ ξ₁ ∧ ξ₁ ≤ 2 * Real.pi ∧
      a = Real.cos η * Complex.exp (-(ξ₁ * Complex.I)) ∧ b = Real.sin η := by
  have hb1 : b ≤ 1 := by nlinarith [Complex.normSq_nonneg a]
  have hsq : 1 - b ^ 2 = ‖a‖ ^ 2 := by
    first
      | (rw [Complex.sq_norm]; linarith)
      | (rw [Complex.normSq_eq_norm_sq] at h; linarith)
  have hcos : Real.cos (Real.arcsin b) = ‖a‖ := by
    rw [Real.cos_arcsin, hsq, Real.sqrt_sq (norm_nonneg a)]
  have hsin : Real.sin (Real.arcsin b) = b := Real.sin_arcsin (by linarith) hb1
  have hpolar : (‖a‖ : ℂ) * Complex.exp (Complex.arg a * Complex.I) = a := Complex.norm_mul_exp_arg_mul_I a
  by_cases harg : Complex.arg a ≤ 0
  · refine ⟨Real.arcsin b, -Complex.arg a, Real.arcsin_nonneg.mpr hb, Real.arcsin_le_pi_div_two b,
      neg_nonneg.mpr harg, ?_, ?_, hsin.symm⟩
    · linarith [Complex.neg_pi_lt_arg a, Real.pi_pos]
    · have hexp : Complex.exp (-((-Complex.arg a : ℝ) * Complex.I)) = Complex.exp (Complex.arg a * Complex.I) := by
        congr 1
        first
          | (push_cast; ring)
          | (push_cast; done)
      rw [hexp, hcos]
      exact hpolar.symm
  · refine ⟨Real.arcsin b, 2 * Real.pi - Complex.arg a, Real.arcsin_nonneg.mpr hb, Real.arcsin_le_pi_div_two b,
      ?_, ?_, ?_, hsin.symm⟩
    · linarith [Complex.arg_le_pi a, Real.pi_pos]
    · have harg2 : 0 < Complex.arg a := not_le.mp harg
      linarith
    · have hexp : Complex.exp (-((2 * Real.pi - Complex.arg a : ℝ) * Complex.I)) =
          Complex.exp (Complex.arg a * Complex.I) := by
        have harg' : -((2 * Real.pi - Complex.arg a : ℝ) * Complex.I) =
            Complex.arg a * Complex.I + -(2 * Real.pi * Complex.I) := by
          first
            | (push_cast; ring)
            | (push_cast; done)
        rw [harg', Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]
      rw [hexp, hcos]
      exact hpolar.symm

private theorem exists_half_phase (z : ℂ) (α : ℝ) :
    ∃ ψ : ℝ, 0 ≤ ψ ∧ ψ < Real.pi ∧
      Complex.exp (2 * ψ * Complex.I) * z = (‖z‖ : ℂ) * Complex.exp (-(α / 2 * Complex.I)) := by
  have hfract := Int.fract_nonneg (((-(α / 2) - Complex.arg z) / (2 * Real.pi)))
  have hfract1 := Int.fract_lt_one (((-(α / 2) - Complex.arg z) / (2 * Real.pi)))
  refine ⟨Real.pi * Int.fract ((-(α / 2) - Complex.arg z) / (2 * Real.pi)), mul_nonneg Real.pi_pos.le hfract,
    (mul_lt_iff_lt_one_right Real.pi_pos).mpr hfract1, ?_⟩
  have hreal : 2 * (Real.pi * Int.fract ((-(α / 2) - Complex.arg z) / (2 * Real.pi))) =
      (-(α / 2) - Complex.arg z) - (⌊(-(α / 2) - Complex.arg z) / (2 * Real.pi)⌋ : ℤ) * (2 * Real.pi) := by
    have hπ : (2 * Real.pi) ≠ 0 := by positivity
    first
      | rw [← Int.self_sub_floor]
      | rw [Int.fract]
      | unfold Int.fract
    first
      | (field_simp; done)
      | (field_simp; ring)
  have hexp : Complex.exp (2 * ((Real.pi * Int.fract ((-(α / 2) - Complex.arg z) / (2 * Real.pi)) : ℝ) : ℂ) *
      Complex.I) = Complex.exp (((-(α / 2) - Complex.arg z : ℝ) : ℂ) * Complex.I) := by
    have hcast : (2 : ℂ) * ((Real.pi * Int.fract ((-(α / 2) - Complex.arg z) / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I =
        ((-(α / 2) - Complex.arg z : ℝ) : ℂ) * Complex.I +
          -(((⌊(-(α / 2) - Complex.arg z) / (2 * Real.pi)⌋ : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
      have hc := congrArg (fun x : ℝ => (x : ℂ)) hreal
      push_cast at hc ⊢
      linear_combination hc * Complex.I
    rw [hcast, Complex.exp_add, Complex.exp_neg, Complex.exp_int_mul_two_pi_mul_I, inv_one, mul_one]
  rw [hexp]
  have hz : (‖z‖ : ℂ) * Complex.exp (Complex.arg z * Complex.I) = z := Complex.norm_mul_exp_arg_mul_I z
  have harg : ((-(α / 2) - Complex.arg z : ℝ) : ℂ) * Complex.I + Complex.arg z * Complex.I = -(α / 2 * Complex.I) := by
    first
      | (push_cast; ring)
      | (push_cast; done)
  calc Complex.exp (((-(α / 2) - Complex.arg z : ℝ) : ℂ) * Complex.I) * z
      = Complex.exp (((-(α / 2) - Complex.arg z : ℝ) : ℂ) * Complex.I) *
          ((‖z‖ : ℂ) * Complex.exp (Complex.arg z * Complex.I)) := by rw [hz]
    _ = (‖z‖ : ℂ) * Complex.exp (((-(α / 2) - Complex.arg z : ℝ) : ℂ) * Complex.I + Complex.arg z * Complex.I) := by
          rw [Complex.exp_add]
          ring
    _ = (‖z‖ : ℂ) * Complex.exp (-(α / 2 * Complex.I)) := by rw [harg]

private theorem conj_exp_mul_I (t : ℝ) : (starRingEnd ℂ) (Complex.exp (t * Complex.I)) = Complex.exp (-(t *
    Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

private theorem conj_exp_neg_mul_I (t : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(t * Complex.I))) = Complex.exp (t * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]

private theorem val_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
          Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
        Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
          Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))] := by
  first
    | rfl
    | (simp only [unitaryElt, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]; done)
    | (simp [unitaryElt]; done)

private theorem val_unitaryElt_mul_conjTranspose (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose = 1 := by
  have hψ : Complex.exp (ψ * Complex.I) * Complex.exp (-(ψ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hξ₁ : Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hξ₂ : Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hcs : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq η
  rw [val_unitaryElt, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_mul, map_neg, Complex.conj_ofReal, conj_exp_mul_I,
      conj_exp_neg_mul_I]
    linear_combination (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) * (Real.cos η : ℂ) ^ 2 +
      Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) * (Real.sin η : ℂ) ^ 2) * hψ + ((Real.cos η :
      ℂ) ^ 2) * hξ₁ + ((Real.sin η : ℂ) ^ 2) * hξ₂ + (1) * hcs
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_mul, map_neg, Complex.conj_ofReal, conj_exp_mul_I,
      conj_exp_neg_mul_I]
    linear_combination (0 : ℂ) * hψ
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_mul, map_neg, Complex.conj_ofReal, conj_exp_mul_I,
      conj_exp_neg_mul_I]
    linear_combination (0 : ℂ) * hψ
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_mul, map_neg, Complex.conj_ofReal, conj_exp_mul_I,
      conj_exp_neg_mul_I]
    linear_combination (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) * (Real.cos η : ℂ) ^ 2 +
      Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) * (Real.sin η : ℂ) ^ 2) * hψ + ((Real.cos η :
      ℂ) ^ 2) * hξ₁ + ((Real.sin η : ℂ) ^ 2) * hξ₂ + (1) * hcs

private theorem val_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    ((twistedSplitElt a₁ a₂ v h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![(Real.sqrt a₁ : ℂ), v; 0,
        (Real.sqrt a₂ : ℂ)] := by
  first
    | rfl
    | (simp only [twistedSplitElt, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]; done)
    | (simp [twistedSplitElt]; done)

private theorem of_splitChart (p : Fin 2 → Fin 2 → ℂ) (hp : p ∈ splitGuard) :
    Matrix.of (splitChart p) =
      !![((p 1 0).re : ℂ), ((p 1 0).re : ℂ) * p 1 1; 0, ((p 1 0).im : ℂ)] *
        ((unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hp' : 0 < (p 1 0).re ∧ 0 < (p 1 0).im := hp
  unfold splitChart
  rw [dif_pos hp', Equiv.apply_symm_apply, Units.val_mul, val_twistedSplitElt, Real.sqrt_sq hp'.1.le,
    Real.sqrt_sq hp'.2.le]

private theorem splitChart_mem_locus (p : Fin 2 → Fin 2 → ℂ) (hp : p ∈ splitGuard) : splitChart p ∈ splitLocus := by
  have hp' : 0 < (p 1 0).re ∧ 0 < (p 1 0).im := hp
  have hof := of_splitChart p hp
  have h00 : splitChart p 0 0 = (Matrix.of (splitChart p)) 0 0 := rfl
  have h01 : splitChart p 0 1 = (Matrix.of (splitChart p)) 0 1 := rfl
  have h10 : splitChart p 1 0 = (Matrix.of (splitChart p)) 1 0 := rfl
  have h11 : splitChart p 1 1 = (Matrix.of (splitChart p)) 1 1 := rfl
  show splitChart p 0 0 * splitChart p 1 1 - splitChart p 0 1 * splitChart p 1 0 ≠ 0
  rw [h00, h01, h10, h11, hof, val_unitaryElt]
  set ψ := (p 0 0).re
  set η := (p 0 0).im
  set ξ₁ := (p 0 1).re
  set ξ₂ := (p 0 1).im
  have hP1 : Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hP2 : Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hcs : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq η
  have hb₁ : ((p 1 0).re : ℂ) ≠ 0 := by exact_mod_cast hp'.1.ne'
  have hb₂ : ((p 1 0).im : ℂ) ≠ 0 := by exact_mod_cast hp'.2.ne'
  have hE : Complex.exp (ψ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  intro h
  apply mul_ne_zero (mul_ne_zero hb₁ hb₂) (mul_ne_zero hE hE)
  linear_combination h -
    (Complex.exp (ψ * Complex.I)^2*((p 1 0).re : ℂ)*((p 1 0).im : ℂ)*(Real.cos η : ℂ)^2) * hP1 -
    (Complex.exp (ψ * Complex.I)^2*((p 1 0).re : ℂ)*((p 1 0).im : ℂ)*(Real.sin η : ℂ)^2) * hP2 -
    (Complex.exp (ψ * Complex.I)^2*((p 1 0).re : ℂ)*((p 1 0).im : ℂ)) * hcs

private theorem exists_second_phase (x : ℂ) (σ : ℝ) (hx : ‖x‖ = σ) :
    ∃ ξ : ℝ, 0 ≤ ξ ∧ ξ ≤ 2 * Real.pi ∧ x = -(σ * Complex.exp (-(ξ * Complex.I))) := by
  refine ⟨Real.pi - Complex.arg x, by linarith [Complex.arg_le_pi x], by linarith [Complex.neg_pi_lt_arg x], ?_⟩
  have hpolar : (‖x‖ : ℂ) * Complex.exp (Complex.arg x * Complex.I) = x := Complex.norm_mul_exp_arg_mul_I x
  have hexp : Complex.exp (-(((Real.pi - Complex.arg x : ℝ) : ℂ) * Complex.I)) =
      -Complex.exp (Complex.arg x * Complex.I) := by
    have h : -(((Real.pi - Complex.arg x : ℝ) : ℂ) * Complex.I) =
        Complex.arg x * Complex.I - Real.pi * Complex.I := by
      push_cast
      ring
    rw [h, Complex.exp_sub, Complex.exp_pi_mul_I, div_neg, div_one]
  rw [hexp, ← hx, mul_neg, neg_neg, hpolar]

private theorem exists_det_phase (z : ℂ) :
    ∃ ψ : ℝ, 0 ≤ ψ ∧ ψ ≤ Real.pi ∧
      z = (‖z‖ : ℂ) * (Complex.exp (ψ * Complex.I) * Complex.exp (ψ * Complex.I)) := by
  obtain ⟨ψ₀, hψ₀, hψ₀π, h⟩ := exists_half_phase z 0
  have h' : Complex.exp (2 * ψ₀ * Complex.I) * z = (‖z‖ : ℂ) := by
    simpa using h
  refine ⟨Real.pi - ψ₀, by linarith, by linarith, ?_⟩
  have hE2 : Complex.exp (((Real.pi - ψ₀ : ℝ) : ℂ) * Complex.I) * Complex.exp (((Real.pi - ψ₀ : ℝ) : ℂ) * Complex.I) *
      Complex.exp (2 * ψ₀ * Complex.I) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_two_pi_mul_I]
    congr 1
    push_cast
    ring
  linear_combination (Complex.exp (((Real.pi - ψ₀ : ℝ) : ℂ) * Complex.I) *
    Complex.exp (((Real.pi - ψ₀ : ℝ) : ℂ) * Complex.I)) * h' - z * hE2

private theorem normSq_dephased_row (m : Fin 2 → Fin 2 → ℂ) (ψ : ℝ) (h10 : m 1 0 ≠ 0) :
    Complex.normSq (m 1 1 /
        (Complex.exp (ψ * Complex.I) * (Real.sqrt (Complex.normSq (m 1 0) + Complex.normSq (m 1 1)) : ℂ))) +
      ‖m 1 0 / (Complex.exp (ψ * Complex.I) * (Real.sqrt (Complex.normSq (m 1 0) + Complex.normSq (m 1 1)) : ℂ))‖ ^ 2 =
        1 := by
  have hpos : 0 < Complex.normSq (m 1 0) + Complex.normSq (m 1 1) :=
    add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr h10) (Complex.normSq_nonneg _)
  have hE : Complex.normSq (Complex.exp (ψ * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hs : Complex.normSq ((Real.sqrt (Complex.normSq (m 1 0) + Complex.normSq (m 1 1)) : ℂ)) =
      Complex.normSq (m 1 0) + Complex.normSq (m 1 1) := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt hpos.le]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_div, Complex.normSq_div, Complex.normSq_mul, hE, hs, one_mul,
    ← add_div, add_comm (Complex.normSq (m 1 1)), div_self hpos.ne']

private theorem exists_closedBox_preimage (m : Fin 2 → Fin 2 → ℂ) (hm : m ∈ splitLocus) (h10 : m 1 0 ≠ 0)
    (h11 : m 1 1 ≠ 0) : ∃ p ∈ splitClosedBox, splitChart p = m := by
  have hdne : m 0 0 * m 1 1 - m 0 1 * m 1 0 ≠ 0 := hm
  have hpos : 0 < Complex.normSq (m 1 0) + Complex.normSq (m 1 1) :=
    add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr h10) (Complex.normSq_nonneg _)
  obtain ⟨ψ, hψ0, hψπ, hd⟩ := exists_det_phase (m 0 0 * m 1 1 - m 0 1 * m 1 0)
  have hb₂pos : 0 < Real.sqrt (Complex.normSq (m 1 0) + Complex.normSq (m 1 1)) := Real.sqrt_pos.mpr hpos
  obtain ⟨η, ξ₁, hη0, hηπ, hξ₁0, hξ₁π, hy, hsin⟩ :=
    exists_angle_pair_of_unit _ _ (norm_nonneg _) (normSq_dephased_row m ψ h10)
  obtain ⟨ξ₂, hξ₂0, hξ₂π, hx⟩ := exists_second_phase _ _ hsin
  set b₂ : ℝ := Real.sqrt (Complex.normSq (m 1 0) + Complex.normSq (m 1 1)) with hb₂def
  have hb₂c : (b₂ : ℂ) ≠ 0 := by exact_mod_cast hb₂pos.ne'
  have hE : Complex.exp (ψ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hEb : Complex.exp (ψ * Complex.I) * (b₂ : ℂ) ≠ 0 := mul_ne_zero hE hb₂c
  have hm11 : m 1 1 =
      Complex.exp (ψ * Complex.I) * (b₂ : ℂ) * ((Real.cos η : ℂ) * Complex.exp (-(ξ₁ * Complex.I))) := by
    rw [div_eq_iff hEb] at hy
    linear_combination hy
  have hm10 : m 1 0 =
      -(Complex.exp (ψ * Complex.I) * (b₂ : ℂ) * ((Real.sin η : ℂ) * Complex.exp (-(ξ₂ * Complex.I)))) := by
    rw [div_eq_iff hEb] at hx
    linear_combination hx
  have hFE : Complex.exp (-(ψ * Complex.I)) * Complex.exp (ψ * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hP1 : Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hP2 : Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hcs : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq η
  have hdet : m 0 0 * m 1 1 - m 0 1 * m 1 0 =
      (‖m 0 0 * m 1 1 - m 0 1 * m 1 0‖ : ℂ) * (Complex.exp (ψ * Complex.I) * Complex.exp (ψ * Complex.I)) := hd
  have hb₁pos : 0 < ‖m 0 0 * m 1 1 - m 0 1 * m 1 0‖ / b₂ := div_pos (norm_pos_iff.mpr hdne) hb₂pos
  have hb₁c : ((‖m 0 0 * m 1 1 - m 0 1 * m 1 0‖ / b₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb₁pos.ne'
  set K : Matrix (Fin 2) (Fin 2) ℂ :=
    !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
        Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
      Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
        Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))] with hK
  have hKK : K.conjTranspose * K = 1 := by
    have h := val_unitaryElt_mul_conjTranspose ψ η ξ₁ ξ₂
    rw [val_unitaryElt] at h
    exact mul_eq_one_comm.mp h
  obtain ⟨v, hv⟩ : ∃ v : ℂ,
      ((‖m 0 0 * m 1 1 - m 0 1 * m 1 0‖ / b₂ : ℝ) : ℂ) * v = (Matrix.of m * K.conjTranspose) 0 1 :=
    ⟨(Matrix.of m * K.conjTranspose) 0 1 / ((‖m 0 0 * m 1 1 - m 0 1 * m 1 0‖ / b₂ : ℝ) : ℂ), mul_div_cancel₀ _ hb₁c⟩
  set W : Fin 2 → Fin 2 → ℂ := ![![⟨ψ, η⟩, ⟨ξ₁, ξ₂⟩], ![⟨‖m 0 0 * m 1 1 - m 0 1 * m 1 0‖ / b₂, b₂⟩, v]] with hW
  have hWguard : W ∈ splitGuard := ⟨hb₁pos, hb₂pos⟩
  refine ⟨W, ⟨hb₁pos, hb₂pos, hψ0, hψπ, hη0, hηπ, hξ₁0, hξ₁π, hξ₂0, hξ₂π⟩, ?_⟩
  apply Matrix.of.injective
  rw [of_splitChart W hWguard]
  show !![((‖m 0 0 * m 1 1 - m 0 1 * m 1 0‖ / b₂ : ℝ) : ℂ), ((‖m 0 0 * m 1 1 - m 0 1 * m 1 0‖ / b₂ : ℝ) : ℂ) * v; 0,
      (b₂ : ℂ)] * ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.of m
  rw [val_unitaryElt, ← hK]
  have hB : !![((‖m 0 0 * m 1 1 - m 0 1 * m 1 0‖ / b₂ : ℝ) : ℂ),
        ((‖m 0 0 * m 1 1 - m 0 1 * m 1 0‖ / b₂ : ℝ) : ℂ) * v; 0, (b₂ : ℂ)] = Matrix.of m * K.conjTranspose := by
    ext i j
    fin_cases i <;> fin_cases j
    · rw [hK]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
        Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_mul,
        map_neg, Complex.conj_ofReal, conj_exp_mul_I, conj_exp_neg_mul_I]
      rw [Complex.ofReal_div, div_eq_iff hb₂c]
      symm
      apply mul_left_cancel₀ hE
      linear_combination
        (-Complex.exp (-(ψ * Complex.I))*m 0 0) * hm11 +
        (Complex.exp (-(ψ * Complex.I))*m 0 1) * hm10 +
        (Complex.exp (-(ψ * Complex.I))) * hdet +
        (Complex.exp (ψ * Complex.I)*(‖m 0 0 * m 1 1 - m 0 1 * m 1 0‖ : ℂ)) * hFE
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      exact hv
    · rw [hK]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
        Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_mul,
        map_neg, Complex.conj_ofReal, conj_exp_mul_I, conj_exp_neg_mul_I]
      symm
      linear_combination
        (Complex.exp (-(ψ * Complex.I))*Complex.exp (-(ξ₂ * Complex.I))*(Real.sin η : ℂ)) * hm11 +
        (Complex.exp (-(ψ * Complex.I))*Complex.exp (-(ξ₁ * Complex.I))*(Real.cos η : ℂ)) * hm10
    · rw [hK]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
        Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_mul,
        map_neg, Complex.conj_ofReal, conj_exp_mul_I, conj_exp_neg_mul_I]
      symm
      linear_combination
        (Complex.exp (-(ψ * Complex.I))*Complex.exp (ξ₁ * Complex.I)*(Real.cos η : ℂ)) * hm11 +
        (-Complex.exp (-(ψ * Complex.I))*Complex.exp (ξ₂ * Complex.I)*(Real.sin η : ℂ)) * hm10 +
        (Complex.exp (ξ₁ * Complex.I)*Complex.exp (-(ξ₁ * Complex.I))*(b₂ : ℂ)*(Real.cos η : ℂ)^2
          + Complex.exp (ξ₂ * Complex.I)*Complex.exp (-(ξ₂ * Complex.I))*(b₂ : ℂ)*(Real.sin η : ℂ)^2) * hFE +
        ((b₂ : ℂ)*(Real.cos η : ℂ)^2) * hP1 +
        ((b₂ : ℂ)*(Real.sin η : ℂ)^2) * hP2 +
        ((b₂ : ℂ)) * hcs
  rw [hB, Matrix.mul_assoc, hKK, Matrix.mul_one]

private theorem image_dom_subset_locus : splitChart '' splitDom ⊆ splitLocus := by
  rintro _ ⟨p, hp, rfl⟩
  exact splitChart_mem_locus p (splitDom_subset_guard hp)

private theorem locus_subset_image_union :
    splitLocus ⊆ splitChart '' splitDom ∪
      (splitChart '' splitWalls ∪ ({m : Fin 2 → Fin 2 → ℂ | m 1 0 ∈ ({0} : Set ℂ)} ∪
        {m : Fin 2 → Fin 2 → ℂ | m 1 1 ∈ ({0} : Set ℂ)})) := by
  intro m hm
  by_cases h10 : m 1 0 = 0
  · exact Or.inr (Or.inr (Or.inl h10))
  by_cases h11 : m 1 1 = 0
  · exact Or.inr (Or.inr (Or.inr h11))
  obtain ⟨p, hp, hpm⟩ := exists_closedBox_preimage m hm h10 h11
  rcases splitClosedBox_subset hp with hdom | hwall
  · exact Or.inl ⟨p, hdom, hpm⟩
  · exact Or.inr (Or.inl ⟨p, hwall, hpm⟩)

private theorem volume_row_isAddHaarMeasure : (volume : Measure (Fin 2 → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

private theorem volume_array_isAddHaarMeasure : (volume : Measure (Fin 2 → Fin 2 → ℂ)).IsAddHaarMeasure := by
  haveI := volume_row_isAddHaarMeasure
  exact Measure.pi.isAddHaarMeasure _

private theorem map_chart_eq (f : (Fin 2 → Fin 2 → ℂ) → Fin 2 → Fin 2 → ℂ) (D : Set (Fin 2 → Fin 2 → ℂ))
    (hD : MeasurableSet D) (hdiff : ∀ p ∈ D, DifferentiableAt ℝ f p) (hinj : Set.InjOn f D)
    (δ : (Fin 2 → Fin 2 → ℂ) → ℝ) (hδ : ∀ p ∈ D, |(fderiv ℝ f p).det| = δ p) (R : Set (Fin 2 → Fin 2 → ℂ))
    (hR : f '' D =ᵐ[volume] R) :
    Measure.map f ((volume.restrict D).withDensity fun p => ENNReal.ofReal (δ p)) = volume.restrict R := by
  haveI := volume_array_isAddHaarMeasure
  have h1 : ((volume.restrict D).withDensity fun p => ENNReal.ofReal (δ p)) =
      (volume.restrict D).withDensity fun p => ENNReal.ofReal |(fderiv ℝ f p).det| := by
    refine withDensity_congr_ae ((ae_restrict_iff' hD).2 (Filter.Eventually.of_forall fun p hp => ?_))
    show ENNReal.ofReal (δ p) = ENNReal.ofReal |(fderiv ℝ f p).det|
    rw [hδ p hp]
  rw [h1, map_withDensity_abs_det_fderiv_eq_addHaar volume hD.nullMeasurableSet
    (fun p hp => (hdiff p hp).hasFDerivAt.hasFDerivWithinAt) hinj]
  exact Measure.restrict_congr_set hR

private theorem ae_eq_of_subset_of_subset_union (S R W : Set (Fin 2 → Fin 2 → ℂ)) (h₁ : S ⊆ R) (h₂ : R ⊆ S ∪ W)
    (hW : volume W = 0) : S =ᵐ[volume] R := by
  rw [ae_eq_set]
  refine ⟨measure_mono_null (fun m hm => (hm.2 (h₁ hm.1)).elim) measure_empty, ?_⟩
  exact measure_mono_null (fun m hm => Or.resolve_left (h₂ hm.1) hm.2) hW

private theorem volume_image_eq_zero_of_differentiableOn (f : (Fin 2 → Fin 2 → ℂ) → Fin 2 → Fin 2 → ℂ)
    (s : Set (Fin 2 → Fin 2 → ℂ)) (hf : DifferentiableOn ℝ f s) (hs : volume s = 0) : volume (f '' s) = 0 := by
  haveI := volume_array_isAddHaarMeasure
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hf hs

private theorem volume_line_re_eq_zero (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h : {z : ℂ | z.re = c} = Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ Set.univ) := by
    ext z
    simp [Complex.measurableEquivRealProd]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_singleton, zero_mul]

private theorem volume_line_im_eq_zero (c : ℝ) : volume {z : ℂ | z.im = c} = 0 := by
  have h : {z : ℂ | z.im = c} = Complex.measurableEquivRealProd ⁻¹' (Set.univ ×ˢ {c}) := by
    ext z
    simp [Complex.measurableEquivRealProd]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_singleton, mul_zero]

private theorem volume_slot_mem_eq_zero (i j : Fin 2) (s : Set ℂ) (hs : volume s = 0) :
    volume {p : Fin 2 → Fin 2 → ℂ | p i j ∈ s} = 0 := by
  have hrow : (volume : Measure (Fin 2 → ℂ)) {q : Fin 2 → ℂ | q j ∈ s} = 0 :=
    Measure.pi_eval_preimage_null (μ := fun _ : Fin 2 => (volume : Measure ℂ)) (i := j) hs
  exact Measure.pi_eval_preimage_null (μ := fun _ : Fin 2 => (volume : Measure (Fin 2 → ℂ))) (i := i) hrow

private theorem volume_slot_re_eq_zero (i j : Fin 2) (c : ℝ) : volume {p : Fin 2 → Fin 2 → ℂ | (p i j).re = c} = 0 :=
  volume_slot_mem_eq_zero i j {z : ℂ | z.re = c} (volume_line_re_eq_zero c)

private theorem volume_slot_im_eq_zero (i j : Fin 2) (c : ℝ) : volume {p : Fin 2 → Fin 2 → ℂ | (p i j).im = c} = 0 :=
  volume_slot_mem_eq_zero i j {z : ℂ | z.im = c} (volume_line_im_eq_zero c)

private theorem volume_splitWalls_eq_zero : volume splitWalls = 0 := by
  unfold splitWalls
  refine measure_union_null (measure_union_null (measure_union_null (measure_union_null
    (measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact measure_mono_null Set.inter_subset_right (volume_slot_re_eq_zero 0 0 0)
  · exact measure_mono_null Set.inter_subset_right (volume_slot_re_eq_zero 0 0 Real.pi)
  · exact measure_mono_null Set.inter_subset_right (volume_slot_im_eq_zero 0 0 0)
  · exact measure_mono_null Set.inter_subset_right (volume_slot_im_eq_zero 0 0 (Real.pi / 2))
  · exact measure_mono_null Set.inter_subset_right (volume_slot_re_eq_zero 0 1 0)
  · exact measure_mono_null Set.inter_subset_right (volume_slot_re_eq_zero 0 1 (2 * Real.pi))
  · exact measure_mono_null Set.inter_subset_right (volume_slot_im_eq_zero 0 1 0)
  · exact measure_mono_null Set.inter_subset_right (volume_slot_im_eq_zero 0 1 (2 * Real.pi))

private theorem volume_image_splitWalls_eq_zero (hdiff : ∀ p ∈ splitGuard, DifferentiableAt ℝ splitChart p) :
    volume (splitChart '' splitWalls) = 0 :=
  volume_image_eq_zero_of_differentiableOn _ _
    (fun p hp => (hdiff p (splitWalls_subset_guard hp)).differentiableWithinAt) volume_splitWalls_eq_zero

private theorem volume_exceptional_eq_zero (hdiff : ∀ p ∈ splitGuard, DifferentiableAt ℝ splitChart p) :
    volume (splitChart '' splitWalls ∪ ({m : Fin 2 → Fin 2 → ℂ | m 1 0 ∈ ({0} : Set ℂ)} ∪
      {m : Fin 2 → Fin 2 → ℂ | m 1 1 ∈ ({0} : Set ℂ)})) = 0 :=
  measure_union_null (volume_image_splitWalls_eq_zero hdiff)
    (measure_union_null (volume_slot_mem_eq_zero 1 0 _ (measure_singleton 0))
      (volume_slot_mem_eq_zero 1 1 _ (measure_singleton 0)))

private theorem image_dom_ae_eq_locus (hdiff : ∀ p ∈ splitGuard, DifferentiableAt ℝ splitChart p) :
    splitChart '' splitDom =ᵐ[volume] splitLocus :=
  ae_eq_of_subset_of_subset_union _ _ _ image_dom_subset_locus locus_subset_image_union
    (volume_exceptional_eq_zero hdiff)

private theorem map_splitChart_eq (hdiff : ∀ p ∈ splitGuard, DifferentiableAt ℝ splitChart p)
    (hinj : Set.InjOn splitChart splitDom) (hdet : ∀ p ∈ splitDom, |(fderiv ℝ splitChart p).det| = splitDensity p) :
    Measure.map splitChart ((volume.restrict splitDom).withDensity fun p => ENNReal.ofReal (splitDensity p)) =
      volume.restrict splitLocus :=
  map_chart_eq splitChart splitDom measurableSet_splitDom (fun p hp => hdiff p (splitDom_subset_guard hp)) hinj
    splitDensity hdet splitLocus (image_dom_ae_eq_locus hdiff)

private theorem det_of_fin_four (a b c d e f g h i j k l m n o q : ℝ) :
    Matrix.det !![a, b, c, d; e, f, g, h; i, j, k, l; m, n, o, q] =
      a * (f * (k * q - l * o) - g * (j * q - l * n) + h * (j * o - k * n)) - b * (e * (k * q - l * o) - g * (i *
        q - l * m) + h * (i * o - k * m)) + c * (e * (j * q - l * n) - f * (i * q - l * m) + h * (i * n - j * m)) -
        d * (e * (j * o - k * n) - f * (i * o - k * m) + g * (i * n - j * m)) := by
  have h1 : (1 : Fin 4).succAbove 2 = 3 := by decide
  have h2 : (2 : Fin 4).succAbove 2 = 3 := by decide
  have h3 : (3 : Fin 4).succAbove 2 = 2 := by decide
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, h1, h2, h3]
  ring

private noncomputable def splitTable (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 8) (Fin 8) ℝ :=
  !![0,
      -((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * ((p 1 1).re) - ((p 1 0).re) * (Real.cos (p 0
        1).re) * (Real.sin (p 0 1).im) * ((p 1 1).im) - ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re)
        * ((p 1 1).im) + ((p 1 0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * ((p 1 1).re),
      ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) *
        ((p 1 1).im) - ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * ((p 1 1).re) - ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) * ((p 1 1).re) - ((p 1 0).re) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * ((p 1 1).im),
      -((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) *
        ((p 1 1).im) + ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * ((p 1 1).re) + ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) * ((p 1 1).re) + ((p 1 0).re) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * ((p 1 1).im),
      1,
      0,
      0,
      0;
      ((p 1 0).re),
      -((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * ((p 1 1).im) + ((p 1 0).re) * (Real.cos (p 0
        1).re) * (Real.sin (p 0 1).im) * ((p 1 1).re) + ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re)
        * ((p 1 1).re) + ((p 1 0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * ((p 1 1).im),
      -((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) *
        ((p 1 1).re) - ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * ((p 1 1).im) - ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) * ((p 1 1).im) + ((p 1 0).re) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * ((p 1 1).re) - ((p 1 0).re) *
        (Real.sin (p 0 0).im) ^ 2 + ((p 1 0).re),
      ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) *
        ((p 1 1).re) + ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * ((p 1 1).im) + ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) * ((p 1 1).im) - ((p 1 0).re) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * ((p 1 1).re) + ((p 1 0).re) *
        (Real.sin (p 0 0).im) ^ 2,
      0,
      0,
      0,
      0;
      -((p 1 0).re) * ((p 1 1).im),
      ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) - ((p 1 0).re) * (Real.sin (p 0 1).re) * (Real.sin
        (p 0 1).im),
      ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) +
        ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im)
        - ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 * ((p 1 1).im) + ((p 1 0).re) * ((p 1 1).im),
      -((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) -
        ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im)
        + ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 * ((p 1 1).im),
      ((p 1 1).re),
      0,
      ((p 1 0).re),
      0;
      ((p 1 0).re) * ((p 1 1).re),
      ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.sin (p 0 1).im) + ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.sin
        (p 0 1).re),
      -((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) +
        ((p 1 0).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)
        + ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 * ((p 1 1).re) - ((p 1 0).re) * ((p 1 1).re),
      ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) -
        ((p 1 0).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)
        - ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 * ((p 1 1).re),
      ((p 1 1).im),
      0,
      0,
      ((p 1 0).re);
      0,
      -((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) + ((p 1 0).im) * (Real.sin (p 0 1).re) *
        (Real.sin (p 0 1).im),
      -((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) -
        ((p 1 0).im) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im),
      ((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) +
        ((p 1 0).im) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im),
      0,
      0,
      0,
      0;
      0,
      ((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.sin (p 0 1).im) + ((p 1 0).im) * (Real.cos (p 0 1).im) * (Real.sin
        (p 0 1).re),
      -((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) +
        ((p 1 0).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im),
      ((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) -
        ((p 1 0).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im),
      0,
      0,
      0,
      0;
      0,
      0,
      0,
      0,
      0,
      1,
      0,
      0;
      ((p 1 0).im),
      0,
      ((p 1 0).im) * (Real.sin (p 0 0).im) ^ 2 - ((p 1 0).im),
      -((p 1 0).im) * (Real.sin (p 0 0).im) ^ 2,
      0,
      0,
      0,
      0]

private noncomputable def splitTriBlock (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,
      0,
      0,
      0;
      ((p 1 1).re),
      0,
      ((p 1 0).re),
      0;
      ((p 1 1).im),
      0,
      0,
      ((p 1 0).re);
      0,
      1,
      0,
      0]

private noncomputable def splitAngBlock (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![((p 1 0).re),
      -((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * ((p 1 1).im) + ((p 1 0).re) * (Real.cos (p 0
        1).re) * (Real.sin (p 0 1).im) * ((p 1 1).re) + ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re)
        * ((p 1 1).re) + ((p 1 0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * ((p 1 1).im),
      -((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) *
        ((p 1 1).re) - ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * ((p 1 1).im) - ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) * ((p 1 1).im) + ((p 1 0).re) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * ((p 1 1).re) - ((p 1 0).re) *
        (Real.sin (p 0 0).im) ^ 2 + ((p 1 0).re),
      ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) *
        ((p 1 1).re) + ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * ((p 1 1).im) + ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) * ((p 1 1).im) - ((p 1 0).re) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * ((p 1 1).re) + ((p 1 0).re) *
        (Real.sin (p 0 0).im) ^ 2;
      0,
      -((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) + ((p 1 0).im) * (Real.sin (p 0 1).re) *
        (Real.sin (p 0 1).im),
      -((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) -
        ((p 1 0).im) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im),
      ((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) +
        ((p 1 0).im) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im);
      0,
      ((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.sin (p 0 1).im) + ((p 1 0).im) * (Real.cos (p 0 1).im) * (Real.sin
        (p 0 1).re),
      -((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) +
        ((p 1 0).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im),
      ((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) -
        ((p 1 0).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im);
      ((p 1 0).im),
      0,
      ((p 1 0).im) * (Real.sin (p 0 0).im) ^ 2 - ((p 1 0).im),
      -((p 1 0).im) * (Real.sin (p 0 0).im) ^ 2]

private noncomputable def splitMixedBlock (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,
      -((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * ((p 1 1).re) - ((p 1 0).re) * (Real.cos (p 0
        1).re) * (Real.sin (p 0 1).im) * ((p 1 1).im) - ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re)
        * ((p 1 1).im) + ((p 1 0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * ((p 1 1).re),
      ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) *
        ((p 1 1).im) - ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * ((p 1 1).re) - ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) * ((p 1 1).re) - ((p 1 0).re) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * ((p 1 1).im),
      -((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) *
        ((p 1 1).im) + ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * ((p 1 1).re) + ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) * ((p 1 1).re) + ((p 1 0).re) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * ((p 1 1).im);
      -((p 1 0).re) * ((p 1 1).im),
      ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) - ((p 1 0).re) * (Real.sin (p 0 1).re) * (Real.sin
        (p 0 1).im),
      ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) +
        ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im)
        - ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 * ((p 1 1).im) + ((p 1 0).re) * ((p 1 1).im),
      -((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) -
        ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im)
        + ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 * ((p 1 1).im);
      ((p 1 0).re) * ((p 1 1).re),
      ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.sin (p 0 1).im) + ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.sin
        (p 0 1).re),
      -((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) +
        ((p 1 0).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)
        + ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 * ((p 1 1).re) - ((p 1 0).re) * ((p 1 1).re),
      ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) -
        ((p 1 0).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)
        - ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 * ((p 1 1).re);
      0,
      0,
      0,
      0]

private noncomputable def splitReindex : Fin 4 ⊕ Fin 4 ≃ Fin 8 :=
  Equiv.ofBijective (Sum.elim ![0, 2, 3, 6] ![1, 4, 5, 7]) (by decide)

private def splitColPerm : Equiv.Perm (Fin 4 ⊕ Fin 4) :=
  Equiv.swap (Sum.inl 0 : Fin 4 ⊕ Fin 4) (Sum.inr 0 : Fin 4 ⊕ Fin 4) * Equiv.swap (Sum.inl 0 : Fin 4 ⊕ Fin 4)
    (Sum.inr 1 : Fin 4 ⊕ Fin 4) * Equiv.swap (Sum.inl 1 : Fin 4 ⊕ Fin 4) (Sum.inr 2 : Fin 4 ⊕ Fin 4) * Equiv.swap
    (Sum.inl 2 : Fin 4 ⊕ Fin 4) (Sum.inr 3 : Fin 4 ⊕ Fin 4) * Equiv.swap (Sum.inl 2 : Fin 4 ⊕ Fin 4) (Sum.inl 3 : Fin
    4 ⊕ Fin 4)

private theorem splitTable_reindex (p : Fin 2 → Fin 2 → ℂ) :
    ((splitTable p).submatrix splitReindex splitReindex).submatrix id splitColPerm =
      Matrix.fromBlocks (splitTriBlock p) (splitMixedBlock p) 0 (splitAngBlock p) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | simp [splitTable, splitTriBlock, splitMixedBlock, splitAngBlock, splitReindex, splitColPerm, Matrix.fromBlocks,
          Equiv.swap_apply_def, Matrix.submatrix_apply]

private theorem det_splitTriBlock (p : Fin 2 → Fin 2 → ℂ) (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1)
    (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2 = 1)
    (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1) :
    (splitTriBlock p).det = ((p 1 0).re) ^ 2 := by
  rw [splitTriBlock, det_of_fin_four]
  ring1

private theorem det_splitAngBlock (p : Fin 2 → Fin 2 → ℂ) (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1)
    (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2 = 1)
    (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1) :
    (splitAngBlock p).det = -2 * ((p 1 0).re) * ((p 1 0).im) ^ 3 * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) :=
      by
  rw [splitAngBlock, det_of_fin_four]
  linear_combination (-2 * ((p 1 0).re) * ((p 1 0).im) ^ 3 * (Real.cos (p 0 1).im) ^ 2 * (Real.cos (p 0 0).im) *
    (Real.sin (p 0 0).im) - 2 * ((p 1 0).re) * ((p 1 0).im) ^ 3 * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) ^ 2 *
    (Real.sin (p 0 0).im)) * hξ₁ + (-2 * ((p 1 0).re) * ((p 1 0).im) ^ 3 * (Real.cos (p 0 0).im) * (Real.sin (p 0
    0).im)) * hξ₂

private theorem det_splitTable (p : Fin 2 → Fin 2 → ℂ) :
    (splitTable p).det = 2 * (p 1 0).re ^ 3 * (p 1 0).im ^ 3 * Real.sin (p 0 0).im * Real.cos (p 0 0).im := by
  have hη := Real.cos_sq_add_sin_sq (p 0 0).im
  have hξ₁ := Real.cos_sq_add_sin_sq (p 0 1).re
  have hξ₂ := Real.cos_sq_add_sin_sq (p 0 1).im
  have hs0 : Equiv.Perm.sign (Equiv.swap (Sum.inl 0 : Fin 4 ⊕ Fin 4) (Sum.inr 0 : Fin 4 ⊕ Fin 4)) = -1 :=
    Equiv.Perm.sign_swap (by decide)
  have hs1 : Equiv.Perm.sign (Equiv.swap (Sum.inl 0 : Fin 4 ⊕ Fin 4) (Sum.inr 1 : Fin 4 ⊕ Fin 4)) = -1 :=
    Equiv.Perm.sign_swap (by decide)
  have hs2 : Equiv.Perm.sign (Equiv.swap (Sum.inl 1 : Fin 4 ⊕ Fin 4) (Sum.inr 2 : Fin 4 ⊕ Fin 4)) = -1 :=
    Equiv.Perm.sign_swap (by decide)
  have hs3 : Equiv.Perm.sign (Equiv.swap (Sum.inl 2 : Fin 4 ⊕ Fin 4) (Sum.inr 3 : Fin 4 ⊕ Fin 4)) = -1 :=
    Equiv.Perm.sign_swap (by decide)
  have hs4 : Equiv.Perm.sign (Equiv.swap (Sum.inl 2 : Fin 4 ⊕ Fin 4) (Sum.inl 3 : Fin 4 ⊕ Fin 4)) = -1 :=
    Equiv.Perm.sign_swap (by decide)
  have hdet : (splitTable p).det = -((splitTriBlock p).det * (splitAngBlock p).det) := by
    have h1 := Matrix.det_submatrix_equiv_self splitReindex (splitTable p)
    have h2 := Matrix.det_permute' splitColPerm ((splitTable p).submatrix splitReindex splitReindex)
    rw [splitTable_reindex, Matrix.det_fromBlocks_zero₂₁] at h2
    simp only [splitColPerm, Equiv.Perm.sign_mul, hs0, hs1, hs2, hs3, hs4] at h2
    norm_num at h2
    linarith
  rw [hdet, det_splitTriBlock p hη hξ₁ hξ₂, det_splitAngBlock p hη hξ₁ hξ₂]
  ring1

private noncomputable def arrayBasis : Module.Basis (Σ _ : Fin 2, Σ _ : Fin 2, Fin 2) ℝ (Fin 2 → Fin 2 → ℂ) :=
  Pi.basis fun _ : Fin 2 => Pi.basis fun _ : Fin 2 => Complex.basisOneI

private noncomputable def coordTable (N : (Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → Fin 2 → ℂ)) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℝ :=
  Matrix.of fun ijs klt =>
    Complex.basisOneI.repr (N (arrayBasis ⟨klt.1, klt.2.1, klt.2.2⟩) ijs.1 ijs.2.1) ijs.2.2

private def sigmaSlots : (Σ _ : Fin 2, Σ _ : Fin 2, Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 :=
  (Equiv.sigmaCongrRight fun _ : Fin 2 => Equiv.sigmaEquivProd (Fin 2) (Fin 2)).trans
    (Equiv.sigmaEquivProd (Fin 2) (Fin 2 × Fin 2))

private theorem det_eq_det_coordTable (N : (Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → Fin 2 → ℂ)) :
    N.det = (coordTable N).det := by
  rw [← LinearMap.det_toMatrix arrayBasis, ← Matrix.det_reindex_self sigmaSlots]
  congr 1
  ext ⟨i, j, s⟩ ⟨k, l, t⟩
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, coordTable, sigmaSlots, LinearMap.toMatrix_apply, arrayBasis,
    Pi.basis_repr, Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight_apply, Equiv.sigmaEquivProd_symm_apply]

private theorem arrayBasis_apply (k l : Fin 2) (t : Fin 2) :
    arrayBasis ⟨k, l, t⟩ = Pi.single k (Pi.single l (Complex.basisOneI t)) := by
  simp [arrayBasis, Pi.basis_apply]

private def transposeLM : (Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → Fin 2 → ℂ) where
  toFun A := fun i j => A j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem transposeLM_apply (A : Matrix (Fin 2) (Fin 2) ℂ) : transposeLM A = A.transpose := rfl

private theorem transposeLM_comp_self : transposeLM.comp transposeLM = LinearMap.id := by
  ext A i j
  rfl

private theorem transposeLM_det_mul_self : transposeLM.det * transposeLM.det = 1 := by
  rw [← LinearMap.det_comp, transposeLM_comp_self, LinearMap.det_id]

private noncomputable def mulRightLM (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → Fin 2 → ℂ) :=
  LinearMap.pi fun i : Fin 2 =>
    (Matrix.toLin' T.transpose).comp (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => Fin 2 → ℂ) i)

private theorem mulRightLM_apply (T A : Matrix (Fin 2) (Fin 2) ℂ) : mulRightLM T A = A * T := by
  funext i k
  simp [mulRightLM, LinearMap.pi_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply, mul_comm]

private theorem mulRightLM_det (T : Matrix (Fin 2) (Fin 2) ℂ) : (mulRightLM T).det = T.det ^ 2 := by
  unfold mulRightLM
  rw [LinearMap.det_pi]
  simp [LinearMap.det_toLin', Finset.prod_const]

private noncomputable def mulLeftLM (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → Fin 2 → ℂ) :=
  transposeLM.comp ((mulRightLM T.transpose).comp transposeLM)

private theorem mulLeftLM_apply (T A : Matrix (Fin 2) (Fin 2) ℂ) : mulLeftLM T A = T * A := by
  have h1 : mulLeftLM T A = transposeLM (mulRightLM T.transpose (transposeLM A)) := rfl
  rw [h1, transposeLM_apply A, mulRightLM_apply T.transpose A.transpose,
    transposeLM_apply (A.transpose * T.transpose), Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose]

private theorem mulLeftLM_det (T : Matrix (Fin 2) (Fin 2) ℂ) : (mulLeftLM T).det = T.det ^ 2 := by
  unfold mulLeftLM
  rw [LinearMap.det_comp, LinearMap.det_comp, mulRightLM_det, Matrix.det_transpose]
  calc transposeLM.det * (T.det ^ 2 * transposeLM.det)
      = (transposeLM.det * transposeLM.det) * T.det ^ 2 := by ring
    _ = T.det ^ 2 := by rw [transposeLM_det_mul_self, one_mul]

private noncomputable def twistLM (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → Fin 2 → ℂ) :=
  (mulRightLM B).comp (mulLeftLM A)

private theorem twistLM_apply (A B X : Matrix (Fin 2) (Fin 2) ℂ) : twistLM A B X = A * X * B := by
  have h1 : twistLM A B X = mulRightLM B (mulLeftLM A X) := rfl
  rw [h1, mulLeftLM_apply, mulRightLM_apply]

private theorem twistLM_det (A B : Matrix (Fin 2) (Fin 2) ℂ) : (twistLM A B).det = (A.det * B.det) ^ 2 := by
  unfold twistLM
  rw [LinearMap.det_comp, mulRightLM_det, mulLeftLM_det]
  ring

private theorem twistLM_restrictScalars_det (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ((twistLM A B).restrictScalars ℝ).det = Complex.normSq (A.det * B.det) ^ 2 := by
  rw [LinearMap.det_restrictScalars, twistLM_det, Algebra.norm_complex_apply, map_pow]

private theorem exp_neg_ofReal_mul_I_eq (x : ℝ) :
    Complex.exp (-(x * Complex.I)) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * Complex.I := by
  rw [show -((x : ℂ) * Complex.I) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

private theorem exp_ofReal_mul_I_eq (x : ℝ) :
    Complex.exp (x * Complex.I) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem diffAt_reim {f g : (Fin 2 → Fin 2 → ℂ) → ℝ} {q : Fin 2 → Fin 2 → ℂ} (hf : DifferentiableAt ℝ f q)
    (hg : DifferentiableAt ℝ g q) :
    DifferentiableAt ℝ (fun x => ((f x : ℝ) : ℂ) + ((g x : ℝ) : ℂ) * Complex.I) q :=
  (Complex.ofRealCLM.differentiableAt.comp q hf).add
    ((Complex.ofRealCLM.differentiableAt.comp q hg).mul_const Complex.I)

private theorem hasDerivAt_reim (x y : ℝ → ℝ) (x' y' s : ℝ) (hx : HasDerivAt x x' s) (hy : HasDerivAt y y' s) :
    HasDerivAt (fun t => ((x t : ℝ) : ℂ) + ((y t : ℝ) : ℂ) * Complex.I) ((x' : ℂ) + (y' : ℂ) * Complex.I) s :=
  hx.ofReal_comp.add (hy.ofReal_comp.mul_const Complex.I)

private theorem hasDerivAt_constMat (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    HasDerivAt (fun _ : ℝ => M i j) ((0 : Matrix (Fin 2) (Fin 2) ℂ) i j) 0 :=
  (hasDerivAt_const (0 : ℝ) (M i j)).congr_deriv (Matrix.zero_apply i j).symm

private theorem hasDerivAt_mul2_entry (A B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (A' B' : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) 0) (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) 0)
    (i j : Fin 2) : HasDerivAt (fun s => (A s * B s) i j) ((A' * B 0 + A 0 * B') i j) 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]
  exact (((hA i 0).mul (hB 0 j)).add ((hA i 1).mul (hB 1 j))).congr_deriv
    (by (try simp only [Pi.add_apply, Pi.mul_apply]); ring)

private theorem deriv_comp_line_apply (Φ : (Fin 2 → Fin 2 → ℂ) → Fin 2 → Fin 2 → ℂ) (p : Fin 2 → Fin 2 → ℂ)
    (hΦ : DifferentiableAt ℝ Φ p) (v : Fin 2 → Fin 2 → ℂ) (i j : Fin 2) :
    deriv (fun s : ℝ => Φ (p + s • v) i j) 0 = fderiv ℝ Φ p v i j := by
  have hline : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id' (x := (0 : ℝ))).smul_const v).const_add p
  have hΦ' : HasFDerivAt Φ (fderiv ℝ Φ p) ((fun s : ℝ => p + s • v) 0) := by
    simp only [zero_smul, add_zero]
    exact hΦ.hasFDerivAt
  have hv : HasDerivAt (fun s : ℝ => Φ (p + s • v)) (fderiv ℝ Φ p v) 0 := hΦ'.comp_hasDerivAt (0 : ℝ) hline
  exact (hasDerivAt_pi.1 (hasDerivAt_pi.1 hv i) j).deriv

private noncomputable def scaleTrig (b₁ b₂ z₁ z₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(((b₁) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      (((b₁) * (z₁) : ℝ) : ℂ) + (((b₁) * (z₂) : ℝ) : ℂ) * Complex.I;
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      (((b₂) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I]

private noncomputable def unitaryTrig (ψ η ξ₁ ξ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(((Real.cos ξ₁) * (Real.cos η) * (Real.cos ψ) - (Real.cos η) * (Real.sin ξ₁) * (Real.sin ψ) : ℝ) : ℂ) +
        (((Real.cos ξ₁) * (Real.cos η) * (Real.sin ψ) + (Real.cos η) * (Real.cos ψ) * (Real.sin ξ₁) : ℝ) : ℂ) *
        Complex.I,
      (((Real.cos ξ₂) * (Real.cos ψ) * (Real.sin η) - (Real.sin ξ₂) * (Real.sin η) * (Real.sin ψ) : ℝ) : ℂ) +
        (((Real.cos ξ₂) * (Real.sin η) * (Real.sin ψ) + (Real.cos ψ) * (Real.sin ξ₂) * (Real.sin η) : ℝ) : ℂ) *
        Complex.I;
      ((-(Real.cos ξ₂) * (Real.cos ψ) * (Real.sin η) - (Real.sin ξ₂) * (Real.sin η) * (Real.sin ψ) : ℝ) : ℂ) +
        ((-(Real.cos ξ₂) * (Real.sin η) * (Real.sin ψ) + (Real.cos ψ) * (Real.sin ξ₂) * (Real.sin η) : ℝ) : ℂ) *
        Complex.I,
      (((Real.cos ξ₁) * (Real.cos η) * (Real.cos ψ) + (Real.cos η) * (Real.sin ξ₁) * (Real.sin ψ) : ℝ) : ℂ) +
        (((Real.cos ξ₁) * (Real.cos η) * (Real.sin ψ) - (Real.cos η) * (Real.cos ψ) * (Real.sin ξ₁) : ℝ) : ℂ) *
        Complex.I]

private noncomputable def splitFormula (p : Fin 2 → Fin 2 → ℂ) : Fin 2 → Fin 2 → ℂ :=
  Matrix.of.symm (scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re (p 1 1).im * unitaryTrig (p 0 0).re (p 0 0).im (p 0
      1).re (p 0 1).im)

private theorem scaleTrig_eq (p : Fin 2 → Fin 2 → ℂ) :
    !![((p 1 0).re : ℂ), ((p 1 0).re : ℂ) * p 1 1; 0, ((p 1 0).im : ℂ)] = scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re
        (p 1 1).im := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [scaleTrig, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im] <;>
    ring_nf

private theorem unitaryTrig_eq (ψ η ξ₁ ξ₂ : ℝ) :
      !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
          Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
        Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
          Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))] =
      unitaryTrig ψ η ξ₁ ξ₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [unitaryTrig, exp_ofReal_mul_I_eq, exp_neg_ofReal_mul_I_eq, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im] <;>
    ring_nf

private theorem splitChart_eq_formula (p : Fin 2 → Fin 2 → ℂ) (hp : p ∈ splitGuard) : splitChart p = splitFormula p
    := by
  apply Matrix.of.injective
  rw [of_splitChart p hp, val_unitaryElt, scaleTrig_eq p, unitaryTrig_eq (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im,
    splitFormula, Equiv.apply_symm_apply]

private theorem splitChart_eventuallyEq_formula (p : Fin 2 → Fin 2 → ℂ) (hp : p ∈ splitGuard) :
    splitChart =ᶠ[nhds p] splitFormula :=
  Filter.eventuallyEq_of_mem (isOpen_splitGuard.mem_nhds hp) fun q hq => splitChart_eq_formula q hq

private theorem differentiableAt_splitFormula (p : Fin 2 → Fin 2 → ℂ) : DifferentiableAt ℝ splitFormula p := by
  have h00re : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => (x 0 0).re) p :=
    Complex.reCLM.differentiableAt.comp p (differentiableAt_pi.1 (differentiableAt_pi.1 differentiableAt_id 0) 0)
  have h00im : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => (x 0 0).im) p :=
    Complex.imCLM.differentiableAt.comp p (differentiableAt_pi.1 (differentiableAt_pi.1 differentiableAt_id 0) 0)
  have h01re : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => (x 0 1).re) p :=
    Complex.reCLM.differentiableAt.comp p (differentiableAt_pi.1 (differentiableAt_pi.1 differentiableAt_id 0) 1)
  have h01im : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => (x 0 1).im) p :=
    Complex.imCLM.differentiableAt.comp p (differentiableAt_pi.1 (differentiableAt_pi.1 differentiableAt_id 0) 1)
  have h10re : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => (x 1 0).re) p :=
    Complex.reCLM.differentiableAt.comp p (differentiableAt_pi.1 (differentiableAt_pi.1 differentiableAt_id 1) 0)
  have h10im : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => (x 1 0).im) p :=
    Complex.imCLM.differentiableAt.comp p (differentiableAt_pi.1 (differentiableAt_pi.1 differentiableAt_id 1) 0)
  have h11re : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => (x 1 1).re) p :=
    Complex.reCLM.differentiableAt.comp p (differentiableAt_pi.1 (differentiableAt_pi.1 differentiableAt_id 1) 1)
  have h11im : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => (x 1 1).im) p :=
    Complex.imCLM.differentiableAt.comp p (differentiableAt_pi.1 (differentiableAt_pi.1 differentiableAt_id 1) 1)
  have hS00 : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => scaleTrig (x 1 0).re (x 1 0).im (x 1 1).re (x 1 1).im
      0 0) p := by
    show DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => ((((x 1 0).re) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) p
    exact diffAt_reim (by fun_prop) (by fun_prop)
  have hS01 : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => scaleTrig (x 1 0).re (x 1 0).im (x 1 1).re (x 1 1).im
      0 1) p := by
    show DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => ((((x 1 0).re) * ((x 1 1).re) : ℝ) : ℂ) + ((((x 1 0).re) *
      ((x 1 1).im) : ℝ) : ℂ) * Complex.I) p
    exact diffAt_reim (by fun_prop) (by fun_prop)
  have hS10 : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => scaleTrig (x 1 0).re (x 1 0).im (x 1 1).re (x 1 1).im
      1 0) p := by
    show DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) p
    exact diffAt_reim (by fun_prop) (by fun_prop)
  have hS11 : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => scaleTrig (x 1 0).re (x 1 0).im (x 1 1).re (x 1 1).im
      1 1) p := by
    show DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => ((((x 1 0).im) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) p
    exact diffAt_reim (by fun_prop) (by fun_prop)
  have hU00 : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => unitaryTrig (x 0 0).re (x 0 0).im (x 0 1).re (x 0
      1).im 0 0) p := by
    show DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => (((Real.cos (x 0 1).re) * (Real.cos (x 0 0).im) * (Real.cos
      (x 0 0).re) - (Real.cos (x 0 0).im) * (Real.sin (x 0 1).re) * (Real.sin (x 0 0).re) : ℝ) : ℂ) + (((Real.cos (x
      0 1).re) * (Real.cos (x 0 0).im) * (Real.sin (x 0 0).re) + (Real.cos (x 0 0).im) * (Real.cos (x 0 0).re) *
      (Real.sin (x 0 1).re) : ℝ) : ℂ) * Complex.I) p
    exact diffAt_reim (by fun_prop) (by fun_prop)
  have hU01 : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => unitaryTrig (x 0 0).re (x 0 0).im (x 0 1).re (x 0
      1).im 0 1) p := by
    show DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => (((Real.cos (x 0 1).im) * (Real.cos (x 0 0).re) * (Real.sin
      (x 0 0).im) - (Real.sin (x 0 1).im) * (Real.sin (x 0 0).im) * (Real.sin (x 0 0).re) : ℝ) : ℂ) + (((Real.cos (x
      0 1).im) * (Real.sin (x 0 0).im) * (Real.sin (x 0 0).re) + (Real.cos (x 0 0).re) * (Real.sin (x 0 1).im) *
      (Real.sin (x 0 0).im) : ℝ) : ℂ) * Complex.I) p
    exact diffAt_reim (by fun_prop) (by fun_prop)
  have hU10 : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => unitaryTrig (x 0 0).re (x 0 0).im (x 0 1).re (x 0
      1).im 1 0) p := by
    show DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => ((-(Real.cos (x 0 1).im) * (Real.cos (x 0 0).re) *
      (Real.sin (x 0 0).im) - (Real.sin (x 0 1).im) * (Real.sin (x 0 0).im) * (Real.sin (x 0 0).re) : ℝ) : ℂ) +
      ((-(Real.cos (x 0 1).im) * (Real.sin (x 0 0).im) * (Real.sin (x 0 0).re) + (Real.cos (x 0 0).re) * (Real.sin (x
      0 1).im) * (Real.sin (x 0 0).im) : ℝ) : ℂ) * Complex.I) p
    exact diffAt_reim (by fun_prop) (by fun_prop)
  have hU11 : DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => unitaryTrig (x 0 0).re (x 0 0).im (x 0 1).re (x 0
      1).im 1 1) p := by
    show DifferentiableAt ℝ (fun x : Fin 2 → Fin 2 → ℂ => (((Real.cos (x 0 1).re) * (Real.cos (x 0 0).im) * (Real.cos
      (x 0 0).re) + (Real.cos (x 0 0).im) * (Real.sin (x 0 1).re) * (Real.sin (x 0 0).re) : ℝ) : ℂ) + (((Real.cos (x
      0 1).re) * (Real.cos (x 0 0).im) * (Real.sin (x 0 0).re) - (Real.cos (x 0 0).im) * (Real.cos (x 0 0).re) *
      (Real.sin (x 0 1).re) : ℝ) : ℂ) * Complex.I) p
    exact diffAt_reim (by fun_prop) (by fun_prop)
  refine differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp only [splitFormula, Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · exact (hS00.mul hU00).add (hS01.mul hU10)
  · exact (hS00.mul hU01).add (hS01.mul hU11)
  · exact (hS10.mul hU00).add (hS11.mul hU10)
  · exact (hS10.mul hU01).add (hS11.mul hU11)

private theorem differentiableAt_splitChart (p : Fin 2 → Fin 2 → ℂ) (hp : p ∈ splitGuard) :
    DifferentiableAt ℝ splitChart p := by
  rw [(splitChart_eventuallyEq_formula p hp).differentiableAt_iff]
  exact differentiableAt_splitFormula p

private noncomputable def unitaryDeriv_psi (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.cos (p
        0 0).re) * (Real.sin (p 0 1).re) : ℝ) : ℂ) + (((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0
        0).re) - (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I,
      ((-(Real.cos (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p
        0 1).im) * (Real.sin (p 0 0).im) : ℝ) : ℂ) + (((Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0
        0).im) - (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I;
      (((Real.cos (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p
        0 1).im) * (Real.sin (p 0 0).im) : ℝ) : ℂ) + ((-(Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p
        0 0).im) - (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I,
      ((-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).im) * (Real.cos (p
        0 0).re) * (Real.sin (p 0 1).re) : ℝ) : ℂ) + (((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0
        0).re) + (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I]

private noncomputable def rightMC_psi (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I;
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I]

private noncomputable def unitaryDeriv_eta (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) + (Real.sin (p 0 1).re) * (Real.sin (p
        0 0).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) + ((-(Real.cos (p 0 1).re) * (Real.sin (p 0 0).im) * (Real.sin (p
        0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) : ℝ) : ℂ) * Complex.I,
      (((Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.sin (p
        0 1).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) + (((Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0
        0).re) + (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) : ℝ) : ℂ) * Complex.I;
      ((-(Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.sin (p
        0 1).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) + ((-(Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p
        0 0).re) + (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) : ℝ) : ℂ) * Complex.I,
      ((-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) - (Real.sin (p 0 1).re) * (Real.sin (p
        0 0).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) + ((-(Real.cos (p 0 1).re) * (Real.sin (p 0 0).im) * (Real.sin (p
        0 0).re) + (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) : ℝ) : ℂ) * Complex.I]

private noncomputable def rightMC_eta (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      (((Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) - (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) : ℝ) : ℂ) +
        (((Real.cos (p 0 1).re) * (Real.sin (p 0 1).im) + (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re) : ℝ) : ℂ) *
        Complex.I;
      ((-(Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) + (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) : ℝ) : ℂ) +
        (((Real.cos (p 0 1).re) * (Real.sin (p 0 1).im) + (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re) : ℝ) : ℂ) *
        Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I]

private noncomputable def unitaryDeriv_xi1 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.cos (p
        0 0).re) * (Real.sin (p 0 1).re) : ℝ) : ℂ) + (((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0
        0).re) - (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I;
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      (((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.cos (p
        0 0).re) * (Real.sin (p 0 1).re) : ℝ) : ℂ) + ((-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p
        0 0).re) - (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I]

private noncomputable def rightMC_xi1 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((0 : ℝ) : ℂ) + ((1 - (Real.sin (p 0 0).im) ^ 2 : ℝ) : ℂ) * Complex.I,
      (((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) + (Real.cos (p
        0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) : ℝ) : ℂ) + ((-(Real.cos (p
        0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) + (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) : ℝ) : ℂ) * Complex.I;
      ((-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) - (Real.cos (p
        0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) : ℝ) : ℂ) + ((-(Real.cos (p
        0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) + (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + (((Real.sin (p 0 0).im) ^ 2 - 1 : ℝ) : ℂ) * Complex.I]

private noncomputable def unitaryDeriv_xi2 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((-(Real.cos (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p
        0 1).im) * (Real.sin (p 0 0).im) : ℝ) : ℂ) + (((Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0
        0).im) - (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I;
      ((-(Real.cos (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).re) * (Real.sin (p
        0 1).im) * (Real.sin (p 0 0).im) : ℝ) : ℂ) + (((Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0
        0).im) + (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I]

private noncomputable def rightMC_xi2 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((0 : ℝ) : ℂ) + (((Real.sin (p 0 0).im) ^ 2 : ℝ) : ℂ) * Complex.I,
      ((-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) - (Real.cos (p
        0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) : ℝ) : ℂ) + (((Real.cos (p 0
        1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) - (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) : ℝ) : ℂ) * Complex.I;
      (((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) + (Real.cos (p
        0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) : ℝ) : ℂ) + (((Real.cos (p 0
        1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) - (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((-(Real.sin (p 0 0).im) ^ 2 : ℝ) : ℂ) * Complex.I]

private noncomputable def scaleDeriv_b1 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((((p 1 1).re) : ℝ) : ℂ) + ((((p 1 1).im) : ℝ) : ℂ) * Complex.I;
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I]

private noncomputable def scaleDeriv_b2 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I;
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I]

private noncomputable def scaleDeriv_z1 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((((p 1 0).re) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I;
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I]

private noncomputable def scaleDeriv_z2 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((((p 1 0).re) : ℝ) : ℂ) * Complex.I;
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I]

private noncomputable def splitColumn0 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((0 : ℝ) : ℂ) + ((((p 1 0).re) : ℝ) : ℂ) * Complex.I,
      ((-((p 1 0).re) * ((p 1 1).im) : ℝ) : ℂ) + ((((p 1 0).re) * ((p 1 1).re) : ℝ) : ℂ) * Complex.I;
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((((p 1 0).im) : ℝ) : ℂ) * Complex.I]

private noncomputable def splitColumn1 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((-((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * ((p 1 1).re) - ((p 1 0).re) * (Real.cos (p 0
        1).re) * (Real.sin (p 0 1).im) * ((p 1 1).im) - ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re)
        * ((p 1 1).im) + ((p 1 0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * ((p 1 1).re) : ℝ) : ℂ) +
        ((-((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * ((p 1 1).im) + ((p 1 0).re) * (Real.cos (p
        0 1).re) * (Real.sin (p 0 1).im) * ((p 1 1).re) + ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.sin (p 0
        1).re) * ((p 1 1).re) + ((p 1 0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * ((p 1 1).im) : ℝ) : ℂ)
        * Complex.I,
      ((((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) - ((p 1 0).re) * (Real.sin (p 0 1).re) *
        (Real.sin (p 0 1).im) : ℝ) : ℂ) + ((((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.sin (p 0 1).im) + ((p 1
        0).re) * (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re) : ℝ) : ℂ) * Complex.I;
      ((-((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) + ((p 1 0).im) * (Real.sin (p 0 1).re) *
        (Real.sin (p 0 1).im) : ℝ) : ℂ) + ((((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.sin (p 0 1).im) + ((p 1
        0).im) * (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re) : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I]

private noncomputable def splitColumn2 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) *
        ((p 1 1).im) - ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * ((p 1 1).re) - ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) * ((p 1 1).re) - ((p 1 0).re) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * ((p 1 1).im) : ℝ) : ℂ) + ((-((p 1
        0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) * ((p
        1 1).re) - ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin
        (p 0 0).im) * ((p 1 1).im) - ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0
        1).re) * (Real.sin (p 0 0).im) * ((p 1 1).im) + ((p 1 0).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re)
        * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * ((p 1 1).re) - ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 +
        ((p 1 0).re) : ℝ) : ℂ) * Complex.I,
      ((((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)
        + ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0
        0).im) - ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 * ((p 1 1).im) + ((p 1 0).re) * ((p 1 1).im) : ℝ) : ℂ) +
        ((-((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0
        0).im) + ((p 1 0).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p
        0 0).im) + ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 * ((p 1 1).re) - ((p 1 0).re) * ((p 1 1).re) : ℝ) : ℂ) *
        Complex.I;
      ((-((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)
        - ((p 1 0).im) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0
        0).im) : ℝ) : ℂ) + ((-((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 0).im) + ((p 1 0).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im)
        * (Real.sin (p 0 0).im) : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((((p 1 0).im) * (Real.sin (p 0 0).im) ^ 2 - ((p 1 0).im) : ℝ) : ℂ) * Complex.I]

private noncomputable def splitColumn3 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((-((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im)
        * ((p 1 1).im) + ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * ((p 1 1).re) + ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) * ((p 1 1).re) + ((p 1 0).re) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * ((p 1 1).im) : ℝ) : ℂ) + ((((p 1
        0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) * ((p
        1 1).re) + ((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin
        (p 0 0).im) * ((p 1 1).im) + ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0
        1).re) * (Real.sin (p 0 0).im) * ((p 1 1).im) - ((p 1 0).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re)
        * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * ((p 1 1).re) + ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 :
        ℝ) : ℂ) * Complex.I,
      ((-((p 1 0).re) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)
        - ((p 1 0).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0
        0).im) + ((p 1 0).re) * (Real.sin (p 0 0).im) ^ 2 * ((p 1 1).im) : ℝ) : ℂ) + ((((p 1 0).re) * (Real.cos (p 0
        1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) - ((p 1 0).re) * (Real.cos (p
        0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) - ((p 1 0).re) * (Real.sin
        (p 0 0).im) ^ 2 * ((p 1 1).re) : ℝ) : ℂ) * Complex.I;
      ((((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)
        + ((p 1 0).im) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0
        0).im) : ℝ) : ℂ) + ((((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 0).im) - ((p 1 0).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 1).im)
        * (Real.sin (p 0 0).im) : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((-((p 1 0).im) * (Real.sin (p 0 0).im) ^ 2 : ℝ) : ℂ) * Complex.I]

private noncomputable def splitColumn4 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((((p 1 1).re) : ℝ) : ℂ) + ((((p 1 1).im) : ℝ) : ℂ) * Complex.I;
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I]

private noncomputable def splitColumn5 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I;
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I]

private noncomputable def splitColumn6 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((((p 1 0).re) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I;
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I]

private noncomputable def splitColumn7 (p : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((((p 1 0).re) : ℝ) : ℂ) * Complex.I;
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I,
      ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I]

private noncomputable def splitColumnVec (p : Fin 2 → Fin 2 → ℂ) : Fin 8 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![splitColumn0 p, splitColumn1 p, splitColumn2 p, splitColumn3 p, splitColumn4 p, splitColumn5 p, splitColumn6 p,
      splitColumn7 p]

private theorem splitColumnVec_0 (p : Fin 2 → Fin 2 → ℂ) : splitColumnVec p 0 = splitColumn0 p := rfl

private theorem splitColumnVec_1 (p : Fin 2 → Fin 2 → ℂ) : splitColumnVec p 1 = splitColumn1 p := rfl

private theorem splitColumnVec_2 (p : Fin 2 → Fin 2 → ℂ) : splitColumnVec p 2 = splitColumn2 p := rfl

private theorem splitColumnVec_3 (p : Fin 2 → Fin 2 → ℂ) : splitColumnVec p 3 = splitColumn3 p := rfl

private theorem splitColumnVec_4 (p : Fin 2 → Fin 2 → ℂ) : splitColumnVec p 4 = splitColumn4 p := rfl

private theorem splitColumnVec_5 (p : Fin 2 → Fin 2 → ℂ) : splitColumnVec p 5 = splitColumn5 p := rfl

private theorem splitColumnVec_6 (p : Fin 2 → Fin 2 → ℂ) : splitColumnVec p 6 = splitColumn6 p := rfl

private theorem splitColumnVec_7 (p : Fin 2 → Fin 2 → ℂ) : splitColumnVec p 7 = splitColumn7 p := rfl

private def slotCol : (Σ _ : Fin 2, Σ _ : Fin 2, Fin 2) → Fin 8 :=
  fun klt => ⟨4 * klt.1.val + 2 * klt.2.1.val + klt.2.2.val, by omega⟩

private def prodSlots : Fin 2 × Fin 2 × Fin 2 → Fin 8 := fun x => ⟨4 * x.1.val + 2 * x.2.1.val + x.2.2.val, by omega⟩

private theorem prodSlots_bijective : Function.Bijective prodSlots := by decide

private noncomputable def prodSlotsEquiv : Fin 2 × Fin 2 × Fin 2 ≃ Fin 8 := Equiv.ofBijective prodSlots
    prodSlots_bijective

private theorem slotCol_000 : slotCol ⟨0, 0, 0⟩ = 0 := rfl

private theorem prodSlots_000 : prodSlots (0, 0, 0) = 0 := rfl

private theorem slotCol_001 : slotCol ⟨0, 0, 1⟩ = 1 := rfl

private theorem prodSlots_001 : prodSlots (0, 0, 1) = 1 := rfl

private theorem slotCol_010 : slotCol ⟨0, 1, 0⟩ = 2 := rfl

private theorem prodSlots_010 : prodSlots (0, 1, 0) = 2 := rfl

private theorem slotCol_011 : slotCol ⟨0, 1, 1⟩ = 3 := rfl

private theorem prodSlots_011 : prodSlots (0, 1, 1) = 3 := rfl

private theorem slotCol_100 : slotCol ⟨1, 0, 0⟩ = 4 := rfl

private theorem prodSlots_100 : prodSlots (1, 0, 0) = 4 := rfl

private theorem slotCol_101 : slotCol ⟨1, 0, 1⟩ = 5 := rfl

private theorem prodSlots_101 : prodSlots (1, 0, 1) = 5 := rfl

private theorem slotCol_110 : slotCol ⟨1, 1, 0⟩ = 6 := rfl

private theorem prodSlots_110 : prodSlots (1, 1, 0) = 6 := rfl

private theorem slotCol_111 : slotCol ⟨1, 1, 1⟩ = 7 := rfl

private theorem prodSlots_111 : prodSlots (1, 1, 1) = 7 := rfl

private noncomputable def splitMap (p : Fin 2 → Fin 2 → ℂ) : (Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  arrayBasis.constr ℝ fun klt => splitColumnVec p (slotCol klt)

private theorem splitMap_basis (p : Fin 2 → Fin 2 → ℂ) (k l t : Fin 2) :
    splitMap p (arrayBasis ⟨k, l, t⟩) = splitColumnVec p (slotCol ⟨k, l, t⟩) := by
  simp only [splitMap, Module.Basis.constr_basis]

private theorem coordTable_splitMap_000 (p : Fin 2 → Fin 2 → ℂ) (ijs : Fin 2 × Fin 2 × Fin 2) :
    coordTable (splitMap p) ijs (0, 0, 0) = (splitTable p).submatrix prodSlotsEquiv prodSlotsEquiv ijs (0, 0, 0) := by
  obtain ⟨i, j, s⟩ := ijs
  simp only [coordTable, Matrix.of_apply, Matrix.submatrix_apply, prodSlotsEquiv, Equiv.ofBijective_apply]
  erw [splitMap_basis]
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, slotCol_000, slotCol_001, slotCol_010, slotCol_011,
      slotCol_100, slotCol_101, slotCol_110, slotCol_111, prodSlots_000, prodSlots_001, prodSlots_010, prodSlots_011,
      prodSlots_100, prodSlots_101, prodSlots_110, prodSlots_111, splitColumnVec_0, splitColumnVec_1,
      splitColumnVec_2, splitColumnVec_3, splitColumnVec_4, splitColumnVec_5, splitColumnVec_6, splitColumnVec_7,
      splitColumn0, splitColumn1, splitColumn2, splitColumn3, splitColumn4, splitColumn5, splitColumn6, splitColumn7,
      Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add, Matrix.of_apply,
      splitTable, Matrix.cons_val] <;>
    ring1

private theorem coordTable_splitMap_001 (p : Fin 2 → Fin 2 → ℂ) (ijs : Fin 2 × Fin 2 × Fin 2) :
    coordTable (splitMap p) ijs (0, 0, 1) = (splitTable p).submatrix prodSlotsEquiv prodSlotsEquiv ijs (0, 0, 1) := by
  obtain ⟨i, j, s⟩ := ijs
  simp only [coordTable, Matrix.of_apply, Matrix.submatrix_apply, prodSlotsEquiv, Equiv.ofBijective_apply]
  erw [splitMap_basis]
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, slotCol_000, slotCol_001, slotCol_010, slotCol_011,
      slotCol_100, slotCol_101, slotCol_110, slotCol_111, prodSlots_000, prodSlots_001, prodSlots_010, prodSlots_011,
      prodSlots_100, prodSlots_101, prodSlots_110, prodSlots_111, splitColumnVec_0, splitColumnVec_1,
      splitColumnVec_2, splitColumnVec_3, splitColumnVec_4, splitColumnVec_5, splitColumnVec_6, splitColumnVec_7,
      splitColumn0, splitColumn1, splitColumn2, splitColumn3, splitColumn4, splitColumn5, splitColumn6, splitColumn7,
      Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add, Matrix.of_apply,
      splitTable, Matrix.cons_val] <;>
    ring1

private theorem coordTable_splitMap_010 (p : Fin 2 → Fin 2 → ℂ) (ijs : Fin 2 × Fin 2 × Fin 2) :
    coordTable (splitMap p) ijs (0, 1, 0) = (splitTable p).submatrix prodSlotsEquiv prodSlotsEquiv ijs (0, 1, 0) := by
  obtain ⟨i, j, s⟩ := ijs
  simp only [coordTable, Matrix.of_apply, Matrix.submatrix_apply, prodSlotsEquiv, Equiv.ofBijective_apply]
  erw [splitMap_basis]
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, slotCol_000, slotCol_001, slotCol_010, slotCol_011,
      slotCol_100, slotCol_101, slotCol_110, slotCol_111, prodSlots_000, prodSlots_001, prodSlots_010, prodSlots_011,
      prodSlots_100, prodSlots_101, prodSlots_110, prodSlots_111, splitColumnVec_0, splitColumnVec_1,
      splitColumnVec_2, splitColumnVec_3, splitColumnVec_4, splitColumnVec_5, splitColumnVec_6, splitColumnVec_7,
      splitColumn0, splitColumn1, splitColumn2, splitColumn3, splitColumn4, splitColumn5, splitColumn6, splitColumn7,
      Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add, Matrix.of_apply,
      splitTable, Matrix.cons_val] <;>
    ring1

private theorem coordTable_splitMap_011 (p : Fin 2 → Fin 2 → ℂ) (ijs : Fin 2 × Fin 2 × Fin 2) :
    coordTable (splitMap p) ijs (0, 1, 1) = (splitTable p).submatrix prodSlotsEquiv prodSlotsEquiv ijs (0, 1, 1) := by
  obtain ⟨i, j, s⟩ := ijs
  simp only [coordTable, Matrix.of_apply, Matrix.submatrix_apply, prodSlotsEquiv, Equiv.ofBijective_apply]
  erw [splitMap_basis]
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, slotCol_000, slotCol_001, slotCol_010, slotCol_011,
      slotCol_100, slotCol_101, slotCol_110, slotCol_111, prodSlots_000, prodSlots_001, prodSlots_010, prodSlots_011,
      prodSlots_100, prodSlots_101, prodSlots_110, prodSlots_111, splitColumnVec_0, splitColumnVec_1,
      splitColumnVec_2, splitColumnVec_3, splitColumnVec_4, splitColumnVec_5, splitColumnVec_6, splitColumnVec_7,
      splitColumn0, splitColumn1, splitColumn2, splitColumn3, splitColumn4, splitColumn5, splitColumn6, splitColumn7,
      Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add, Matrix.of_apply,
      splitTable, Matrix.cons_val] <;>
    ring1

private theorem coordTable_splitMap_100 (p : Fin 2 → Fin 2 → ℂ) (ijs : Fin 2 × Fin 2 × Fin 2) :
    coordTable (splitMap p) ijs (1, 0, 0) = (splitTable p).submatrix prodSlotsEquiv prodSlotsEquiv ijs (1, 0, 0) := by
  obtain ⟨i, j, s⟩ := ijs
  simp only [coordTable, Matrix.of_apply, Matrix.submatrix_apply, prodSlotsEquiv, Equiv.ofBijective_apply]
  erw [splitMap_basis]
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, slotCol_000, slotCol_001, slotCol_010, slotCol_011,
      slotCol_100, slotCol_101, slotCol_110, slotCol_111, prodSlots_000, prodSlots_001, prodSlots_010, prodSlots_011,
      prodSlots_100, prodSlots_101, prodSlots_110, prodSlots_111, splitColumnVec_0, splitColumnVec_1,
      splitColumnVec_2, splitColumnVec_3, splitColumnVec_4, splitColumnVec_5, splitColumnVec_6, splitColumnVec_7,
      splitColumn0, splitColumn1, splitColumn2, splitColumn3, splitColumn4, splitColumn5, splitColumn6, splitColumn7,
      Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add, Matrix.of_apply,
      splitTable, Matrix.cons_val] <;>
    ring1

private theorem coordTable_splitMap_101 (p : Fin 2 → Fin 2 → ℂ) (ijs : Fin 2 × Fin 2 × Fin 2) :
    coordTable (splitMap p) ijs (1, 0, 1) = (splitTable p).submatrix prodSlotsEquiv prodSlotsEquiv ijs (1, 0, 1) := by
  obtain ⟨i, j, s⟩ := ijs
  simp only [coordTable, Matrix.of_apply, Matrix.submatrix_apply, prodSlotsEquiv, Equiv.ofBijective_apply]
  erw [splitMap_basis]
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, slotCol_000, slotCol_001, slotCol_010, slotCol_011,
      slotCol_100, slotCol_101, slotCol_110, slotCol_111, prodSlots_000, prodSlots_001, prodSlots_010, prodSlots_011,
      prodSlots_100, prodSlots_101, prodSlots_110, prodSlots_111, splitColumnVec_0, splitColumnVec_1,
      splitColumnVec_2, splitColumnVec_3, splitColumnVec_4, splitColumnVec_5, splitColumnVec_6, splitColumnVec_7,
      splitColumn0, splitColumn1, splitColumn2, splitColumn3, splitColumn4, splitColumn5, splitColumn6, splitColumn7,
      Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add, Matrix.of_apply,
      splitTable, Matrix.cons_val] <;>
    ring1

private theorem coordTable_splitMap_110 (p : Fin 2 → Fin 2 → ℂ) (ijs : Fin 2 × Fin 2 × Fin 2) :
    coordTable (splitMap p) ijs (1, 1, 0) = (splitTable p).submatrix prodSlotsEquiv prodSlotsEquiv ijs (1, 1, 0) := by
  obtain ⟨i, j, s⟩ := ijs
  simp only [coordTable, Matrix.of_apply, Matrix.submatrix_apply, prodSlotsEquiv, Equiv.ofBijective_apply]
  erw [splitMap_basis]
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, slotCol_000, slotCol_001, slotCol_010, slotCol_011,
      slotCol_100, slotCol_101, slotCol_110, slotCol_111, prodSlots_000, prodSlots_001, prodSlots_010, prodSlots_011,
      prodSlots_100, prodSlots_101, prodSlots_110, prodSlots_111, splitColumnVec_0, splitColumnVec_1,
      splitColumnVec_2, splitColumnVec_3, splitColumnVec_4, splitColumnVec_5, splitColumnVec_6, splitColumnVec_7,
      splitColumn0, splitColumn1, splitColumn2, splitColumn3, splitColumn4, splitColumn5, splitColumn6, splitColumn7,
      Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add, Matrix.of_apply,
      splitTable, Matrix.cons_val] <;>
    ring1

private theorem coordTable_splitMap_111 (p : Fin 2 → Fin 2 → ℂ) (ijs : Fin 2 × Fin 2 × Fin 2) :
    coordTable (splitMap p) ijs (1, 1, 1) = (splitTable p).submatrix prodSlotsEquiv prodSlotsEquiv ijs (1, 1, 1) := by
  obtain ⟨i, j, s⟩ := ijs
  simp only [coordTable, Matrix.of_apply, Matrix.submatrix_apply, prodSlotsEquiv, Equiv.ofBijective_apply]
  erw [splitMap_basis]
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, slotCol_000, slotCol_001, slotCol_010, slotCol_011,
      slotCol_100, slotCol_101, slotCol_110, slotCol_111, prodSlots_000, prodSlots_001, prodSlots_010, prodSlots_011,
      prodSlots_100, prodSlots_101, prodSlots_110, prodSlots_111, splitColumnVec_0, splitColumnVec_1,
      splitColumnVec_2, splitColumnVec_3, splitColumnVec_4, splitColumnVec_5, splitColumnVec_6, splitColumnVec_7,
      splitColumn0, splitColumn1, splitColumn2, splitColumn3, splitColumn4, splitColumn5, splitColumn6, splitColumn7,
      Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add, Matrix.of_apply,
      splitTable, Matrix.cons_val] <;>
    ring1

private theorem coordTable_splitMap (p : Fin 2 → Fin 2 → ℂ) :
    coordTable (splitMap p) = (splitTable p).submatrix prodSlotsEquiv prodSlotsEquiv := by
  ext ijs klt
  obtain ⟨k, l, t⟩ := klt
  fin_cases k <;> fin_cases l <;> fin_cases t
  exacts [coordTable_splitMap_000 p ijs, coordTable_splitMap_001 p ijs, coordTable_splitMap_010 p ijs,
      coordTable_splitMap_011 p ijs,
    coordTable_splitMap_100 p ijs, coordTable_splitMap_101 p ijs, coordTable_splitMap_110 p ijs,
        coordTable_splitMap_111 p ijs]

private theorem line_000_00re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 0⟩) 0 0).re = (p 0 0).re + s := by
  simp [arrayBasis_apply]

private theorem line_000_00im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 0⟩) 0 0).im = (p 0 0).im := by
  simp [arrayBasis_apply]

private theorem line_000_01re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 0⟩) 0 1).re = (p 0 1).re := by
  simp [arrayBasis_apply]

private theorem line_000_01im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 0⟩) 0 1).im = (p 0 1).im := by
  simp [arrayBasis_apply]

private theorem line_000_10re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 0⟩) 1 0).re = (p 1 0).re := by
  simp [arrayBasis_apply]

private theorem line_000_10im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 0⟩) 1 0).im = (p 1 0).im := by
  simp [arrayBasis_apply]

private theorem line_000_11re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 0⟩) 1 1).re = (p 1 1).re := by
  simp [arrayBasis_apply]

private theorem line_000_11im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 0⟩) 1 1).im = (p 1 1).im := by
  simp [arrayBasis_apply]

private theorem line_001_00re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 1⟩) 0 0).re = (p 0 0).re := by
  simp [arrayBasis_apply]

private theorem line_001_00im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 1⟩) 0 0).im = (p 0 0).im + s := by
  simp [arrayBasis_apply]

private theorem line_001_01re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 1⟩) 0 1).re = (p 0 1).re := by
  simp [arrayBasis_apply]

private theorem line_001_01im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 1⟩) 0 1).im = (p 0 1).im := by
  simp [arrayBasis_apply]

private theorem line_001_10re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 1⟩) 1 0).re = (p 1 0).re := by
  simp [arrayBasis_apply]

private theorem line_001_10im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 1⟩) 1 0).im = (p 1 0).im := by
  simp [arrayBasis_apply]

private theorem line_001_11re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 1⟩) 1 1).re = (p 1 1).re := by
  simp [arrayBasis_apply]

private theorem line_001_11im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 0, 1⟩) 1 1).im = (p 1 1).im := by
  simp [arrayBasis_apply]

private theorem line_010_00re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 0⟩) 0 0).re = (p 0 0).re := by
  simp [arrayBasis_apply]

private theorem line_010_00im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 0⟩) 0 0).im = (p 0 0).im := by
  simp [arrayBasis_apply]

private theorem line_010_01re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 0⟩) 0 1).re = (p 0 1).re + s := by
  simp [arrayBasis_apply]

private theorem line_010_01im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 0⟩) 0 1).im = (p 0 1).im := by
  simp [arrayBasis_apply]

private theorem line_010_10re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 0⟩) 1 0).re = (p 1 0).re := by
  simp [arrayBasis_apply]

private theorem line_010_10im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 0⟩) 1 0).im = (p 1 0).im := by
  simp [arrayBasis_apply]

private theorem line_010_11re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 0⟩) 1 1).re = (p 1 1).re := by
  simp [arrayBasis_apply]

private theorem line_010_11im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 0⟩) 1 1).im = (p 1 1).im := by
  simp [arrayBasis_apply]

private theorem line_011_00re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 1⟩) 0 0).re = (p 0 0).re := by
  simp [arrayBasis_apply]

private theorem line_011_00im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 1⟩) 0 0).im = (p 0 0).im := by
  simp [arrayBasis_apply]

private theorem line_011_01re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 1⟩) 0 1).re = (p 0 1).re := by
  simp [arrayBasis_apply]

private theorem line_011_01im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 1⟩) 0 1).im = (p 0 1).im + s := by
  simp [arrayBasis_apply]

private theorem line_011_10re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 1⟩) 1 0).re = (p 1 0).re := by
  simp [arrayBasis_apply]

private theorem line_011_10im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 1⟩) 1 0).im = (p 1 0).im := by
  simp [arrayBasis_apply]

private theorem line_011_11re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 1⟩) 1 1).re = (p 1 1).re := by
  simp [arrayBasis_apply]

private theorem line_011_11im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨0, 1, 1⟩) 1 1).im = (p 1 1).im := by
  simp [arrayBasis_apply]

private theorem line_100_00re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 0⟩) 0 0).re = (p 0 0).re := by
  simp [arrayBasis_apply]

private theorem line_100_00im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 0⟩) 0 0).im = (p 0 0).im := by
  simp [arrayBasis_apply]

private theorem line_100_01re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 0⟩) 0 1).re = (p 0 1).re := by
  simp [arrayBasis_apply]

private theorem line_100_01im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 0⟩) 0 1).im = (p 0 1).im := by
  simp [arrayBasis_apply]

private theorem line_100_10re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 0⟩) 1 0).re = (p 1 0).re + s := by
  simp [arrayBasis_apply]

private theorem line_100_10im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 0⟩) 1 0).im = (p 1 0).im := by
  simp [arrayBasis_apply]

private theorem line_100_11re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 0⟩) 1 1).re = (p 1 1).re := by
  simp [arrayBasis_apply]

private theorem line_100_11im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 0⟩) 1 1).im = (p 1 1).im := by
  simp [arrayBasis_apply]

private theorem line_101_00re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 1⟩) 0 0).re = (p 0 0).re := by
  simp [arrayBasis_apply]

private theorem line_101_00im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 1⟩) 0 0).im = (p 0 0).im := by
  simp [arrayBasis_apply]

private theorem line_101_01re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 1⟩) 0 1).re = (p 0 1).re := by
  simp [arrayBasis_apply]

private theorem line_101_01im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 1⟩) 0 1).im = (p 0 1).im := by
  simp [arrayBasis_apply]

private theorem line_101_10re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 1⟩) 1 0).re = (p 1 0).re := by
  simp [arrayBasis_apply]

private theorem line_101_10im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 1⟩) 1 0).im = (p 1 0).im + s := by
  simp [arrayBasis_apply]

private theorem line_101_11re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 1⟩) 1 1).re = (p 1 1).re := by
  simp [arrayBasis_apply]

private theorem line_101_11im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 0, 1⟩) 1 1).im = (p 1 1).im := by
  simp [arrayBasis_apply]

private theorem line_110_00re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 0⟩) 0 0).re = (p 0 0).re := by
  simp [arrayBasis_apply]

private theorem line_110_00im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 0⟩) 0 0).im = (p 0 0).im := by
  simp [arrayBasis_apply]

private theorem line_110_01re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 0⟩) 0 1).re = (p 0 1).re := by
  simp [arrayBasis_apply]

private theorem line_110_01im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 0⟩) 0 1).im = (p 0 1).im := by
  simp [arrayBasis_apply]

private theorem line_110_10re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 0⟩) 1 0).re = (p 1 0).re := by
  simp [arrayBasis_apply]

private theorem line_110_10im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 0⟩) 1 0).im = (p 1 0).im := by
  simp [arrayBasis_apply]

private theorem line_110_11re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 0⟩) 1 1).re = (p 1 1).re + s := by
  simp [arrayBasis_apply]

private theorem line_110_11im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 0⟩) 1 1).im = (p 1 1).im := by
  simp [arrayBasis_apply]

private theorem line_111_00re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 1⟩) 0 0).re = (p 0 0).re := by
  simp [arrayBasis_apply]

private theorem line_111_00im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 1⟩) 0 0).im = (p 0 0).im := by
  simp [arrayBasis_apply]

private theorem line_111_01re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 1⟩) 0 1).re = (p 0 1).re := by
  simp [arrayBasis_apply]

private theorem line_111_01im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 1⟩) 0 1).im = (p 0 1).im := by
  simp [arrayBasis_apply]

private theorem line_111_10re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 1⟩) 1 0).re = (p 1 0).re := by
  simp [arrayBasis_apply]

private theorem line_111_10im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 1⟩) 1 0).im = (p 1 0).im := by
  simp [arrayBasis_apply]

private theorem line_111_11re (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 1⟩) 1 1).re = (p 1 1).re := by
  simp [arrayBasis_apply]

private theorem line_111_11im (p : Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    ((p + s • arrayBasis ⟨1, 1, 1⟩) 1 1).im = (p 1 1).im + s := by
  simp [arrayBasis_apply]

private theorem hasDerivAt_unitaryTrig_psi (p : Fin 2 → Fin 2 → ℂ) :
    ∀ i j, HasDerivAt (fun s : ℝ => unitaryTrig ((p 0 0).re + s) (p 0 0).im (p 0 1).re (p 0 1).im i j)
      (unitaryDeriv_psi p i j) 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · have hx : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re + s)) -
        (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 1).re)) * (Real.sin ((p 0 0).re + s)) : ℝ)) 0 = (-(Real.cos (p 0
        1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) *
        (Real.sin (p 0 1).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 0).re + s)) +
        (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re + s)) * (Real.sin ((p 0 1).re)) : ℝ)) 0 = ((Real.cos (p 0
        1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) *
        (Real.sin (p 0 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re + s)) -
        (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 1).re)) * (Real.sin ((p 0 0).re + s)) : ℝ) : ℂ) + (((Real.cos ((p 0
        1).re)) * (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 0).re + s)) + (Real.cos ((p 0 0).im)) * (Real.cos ((p 0
        0).re + s)) * (Real.sin ((p 0 1).re)) : ℝ) : ℂ) * Complex.I) (((-(Real.cos (p 0 1).re) * (Real.cos (p 0
        0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) : ℝ) :
        ℂ) + (((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) - (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => ((Real.cos ((p 0 1).im)) * (Real.cos ((p 0 0).re + s)) * (Real.sin ((p 0 0).im)) -
        (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re + s)) : ℝ)) 0 = (-(Real.cos (p 0
        1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((Real.cos ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re + s)) +
        (Real.cos ((p 0 0).re + s)) * (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) : ℝ)) 0 = ((Real.cos (p 0
        1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) - (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) *
        (Real.sin (p 0 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((Real.cos ((p 0 1).im)) * (Real.cos ((p 0 0).re + s)) * (Real.sin ((p 0 0).im)) -
        (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re + s)) : ℝ) : ℂ) + (((Real.cos ((p 0
        1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re + s)) + (Real.cos ((p 0 0).re + s)) * (Real.sin ((p
        0 1).im)) * (Real.sin ((p 0 0).im)) : ℝ) : ℂ) * Complex.I) (((-(Real.cos (p 0 1).im) * (Real.sin (p 0 0).im)
        * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) : ℝ) : ℂ) +
        (((Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) - (Real.sin (p 0 1).im) * (Real.sin
        (p 0 0).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => (-(Real.cos ((p 0 1).im)) * (Real.cos ((p 0 0).re + s)) * (Real.sin ((p 0 0).im)) -
        (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re + s)) : ℝ)) 0 = ((Real.cos (p 0
        1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => (-(Real.cos ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re + s)) +
        (Real.cos ((p 0 0).re + s)) * (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) : ℝ)) 0 = (-(Real.cos (p 0
        1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) - (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) *
        (Real.sin (p 0 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => ((-(Real.cos ((p 0 1).im)) * (Real.cos ((p 0 0).re + s)) * (Real.sin ((p 0 0).im))
        - (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re + s)) : ℝ) : ℂ) + ((-(Real.cos
        ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re + s)) + (Real.cos ((p 0 0).re + s)) *
        (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) : ℝ) : ℂ) * Complex.I) ((((Real.cos (p 0 1).im) * (Real.sin
        (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) :
        ℝ) : ℂ) + ((-(Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) - (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re + s)) +
        (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 1).re)) * (Real.sin ((p 0 0).re + s)) : ℝ)) 0 = (-(Real.cos (p 0
        1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) *
        (Real.sin (p 0 1).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 0).re + s)) -
        (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re + s)) * (Real.sin ((p 0 1).re)) : ℝ)) 0 = ((Real.cos (p 0
        1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) + (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) *
        (Real.sin (p 0 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re + s)) +
        (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 1).re)) * (Real.sin ((p 0 0).re + s)) : ℝ) : ℂ) + (((Real.cos ((p 0
        1).re)) * (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 0).re + s)) - (Real.cos ((p 0 0).im)) * (Real.cos ((p 0
        0).re + s)) * (Real.sin ((p 0 1).re)) : ℝ) : ℂ) * Complex.I) (((-(Real.cos (p 0 1).re) * (Real.cos (p 0
        0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) : ℝ) :
        ℂ) + (((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) + (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])

private theorem hasDerivAt_unitaryTrig_eta (p : Fin 2 → Fin 2 → ℂ) :
    ∀ i j, HasDerivAt (fun s : ℝ => unitaryTrig (p 0 0).re ((p 0 0).im + s) (p 0 1).re (p 0 1).im i j)
      (unitaryDeriv_eta p i j) 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · have hx : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im + s)) * (Real.cos ((p 0 0).re)) -
        (Real.cos ((p 0 0).im + s)) * (Real.sin ((p 0 1).re)) * (Real.sin ((p 0 0).re)) : ℝ)) 0 = (-(Real.cos (p 0
        1).re) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) + (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) *
        (Real.sin (p 0 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im + s)) * (Real.sin ((p 0 0).re)) +
        (Real.cos ((p 0 0).im + s)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 1).re)) : ℝ)) 0 = (-(Real.cos (p 0
        1).re) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) *
        (Real.sin (p 0 0).im) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im + s)) * (Real.cos ((p 0 0).re)) -
        (Real.cos ((p 0 0).im + s)) * (Real.sin ((p 0 1).re)) * (Real.sin ((p 0 0).re)) : ℝ) : ℂ) + (((Real.cos ((p 0
        1).re)) * (Real.cos ((p 0 0).im + s)) * (Real.sin ((p 0 0).re)) + (Real.cos ((p 0 0).im + s)) * (Real.cos ((p
        0 0).re)) * (Real.sin ((p 0 1).re)) : ℝ) : ℂ) * Complex.I) (((-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).re)
        * (Real.sin (p 0 0).im) + (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) +
        ((-(Real.cos (p 0 1).re) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin
        (p 0 1).re) * (Real.sin (p 0 0).im) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => ((Real.cos ((p 0 1).im)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 0).im + s)) -
        (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im + s)) * (Real.sin ((p 0 0).re)) : ℝ)) 0 = ((Real.cos (p 0
        1).im) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((Real.cos ((p 0 1).im)) * (Real.sin ((p 0 0).im + s)) * (Real.sin ((p 0 0).re)) +
        (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im + s)) : ℝ)) 0 = ((Real.cos (p 0
        1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) *
        (Real.sin (p 0 1).im) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((Real.cos ((p 0 1).im)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 0).im + s)) -
        (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im + s)) * (Real.sin ((p 0 0).re)) : ℝ) : ℂ) + (((Real.cos ((p 0
        1).im)) * (Real.sin ((p 0 0).im + s)) * (Real.sin ((p 0 0).re)) + (Real.cos ((p 0 0).re)) * (Real.sin ((p 0
        1).im)) * (Real.sin ((p 0 0).im + s)) : ℝ) : ℂ) * Complex.I) ((((Real.cos (p 0 1).im) * (Real.cos (p 0 0).im)
        * (Real.cos (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) +
        (((Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).im) * (Real.cos
        (p 0 0).re) * (Real.sin (p 0 1).im) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => (-(Real.cos ((p 0 1).im)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 0).im + s)) -
        (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im + s)) * (Real.sin ((p 0 0).re)) : ℝ)) 0 = (-(Real.cos (p 0
        1).im) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => (-(Real.cos ((p 0 1).im)) * (Real.sin ((p 0 0).im + s)) * (Real.sin ((p 0 0).re)) +
        (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im + s)) : ℝ)) 0 = (-(Real.cos (p 0
        1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) *
        (Real.sin (p 0 1).im) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => ((-(Real.cos ((p 0 1).im)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 0).im + s))
        - (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im + s)) * (Real.sin ((p 0 0).re)) : ℝ) : ℂ) + ((-(Real.cos
        ((p 0 1).im)) * (Real.sin ((p 0 0).im + s)) * (Real.sin ((p 0 0).re)) + (Real.cos ((p 0 0).re)) * (Real.sin
        ((p 0 1).im)) * (Real.sin ((p 0 0).im + s)) : ℝ) : ℂ) * Complex.I) (((-(Real.cos (p 0 1).im) * (Real.cos (p 0
        0).im) * (Real.cos (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).re) : ℝ) :
        ℂ) + ((-(Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).im) *
        (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im + s)) * (Real.cos ((p 0 0).re)) +
        (Real.cos ((p 0 0).im + s)) * (Real.sin ((p 0 1).re)) * (Real.sin ((p 0 0).re)) : ℝ)) 0 = (-(Real.cos (p 0
        1).re) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) - (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) *
        (Real.sin (p 0 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im + s)) * (Real.sin ((p 0 0).re)) -
        (Real.cos ((p 0 0).im + s)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 1).re)) : ℝ)) 0 = (-(Real.cos (p 0
        1).re) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) *
        (Real.sin (p 0 0).im) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im + s)) * (Real.cos ((p 0 0).re)) +
        (Real.cos ((p 0 0).im + s)) * (Real.sin ((p 0 1).re)) * (Real.sin ((p 0 0).re)) : ℝ) : ℂ) + (((Real.cos ((p 0
        1).re)) * (Real.cos ((p 0 0).im + s)) * (Real.sin ((p 0 0).re)) - (Real.cos ((p 0 0).im + s)) * (Real.cos ((p
        0 0).re)) * (Real.sin ((p 0 1).re)) : ℝ) : ℂ) * Complex.I) (((-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).re)
        * (Real.sin (p 0 0).im) - (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) +
        ((-(Real.cos (p 0 1).re) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).re) * (Real.sin
        (p 0 1).re) * (Real.sin (p 0 0).im) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])

private theorem hasDerivAt_unitaryTrig_xi1 (p : Fin 2 → Fin 2 → ℂ) :
    ∀ i j, HasDerivAt (fun s : ℝ => unitaryTrig (p 0 0).re (p 0 0).im ((p 0 1).re + s) (p 0 1).im i j)
      (unitaryDeriv_xi1 p i j) 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · have hx : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re + s)) * (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re)) -
        (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 1).re + s)) * (Real.sin ((p 0 0).re)) : ℝ)) 0 = (-(Real.cos (p 0
        1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) *
        (Real.sin (p 0 1).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re + s)) * (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 0).re)) +
        (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 1).re + s)) : ℝ)) 0 = ((Real.cos (p 0
        1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) *
        (Real.sin (p 0 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((Real.cos ((p 0 1).re + s)) * (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re)) -
        (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 1).re + s)) * (Real.sin ((p 0 0).re)) : ℝ) : ℂ) + (((Real.cos ((p 0
        1).re + s)) * (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 0).re)) + (Real.cos ((p 0 0).im)) * (Real.cos ((p 0
        0).re)) * (Real.sin ((p 0 1).re + s)) : ℝ) : ℂ) * Complex.I) (((-(Real.cos (p 0 1).re) * (Real.cos (p 0
        0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) : ℝ) :
        ℂ) + (((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) - (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => ((Real.cos ((p 0 1).im)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 0).im)) -
        (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((Real.cos ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) +
        (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((Real.cos ((p 0 1).im)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 0).im)) -
        (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) : ℝ) : ℂ) + (((Real.cos ((p 0
        1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) + (Real.cos ((p 0 0).re)) * (Real.sin ((p 0
        1).im)) * (Real.sin ((p 0 0).im)) : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => (-(Real.cos ((p 0 1).im)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 0).im)) -
        (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => (-(Real.cos ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) +
        (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => ((-(Real.cos ((p 0 1).im)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 0).im)) -
        (Real.sin ((p 0 1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) : ℝ) : ℂ) + ((-(Real.cos ((p 0
        1).im)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) + (Real.cos ((p 0 0).re)) * (Real.sin ((p 0
        1).im)) * (Real.sin ((p 0 0).im)) : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re + s)) * (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re)) +
        (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 1).re + s)) * (Real.sin ((p 0 0).re)) : ℝ)) 0 = ((Real.cos (p 0
        1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) *
        (Real.sin (p 0 1).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re + s)) * (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 0).re)) -
        (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 1).re + s)) : ℝ)) 0 = (-(Real.cos (p 0
        1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) *
        (Real.sin (p 0 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((Real.cos ((p 0 1).re + s)) * (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re)) +
        (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 1).re + s)) * (Real.sin ((p 0 0).re)) : ℝ) : ℂ) + (((Real.cos ((p 0
        1).re + s)) * (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 0).re)) - (Real.cos ((p 0 0).im)) * (Real.cos ((p 0
        0).re)) * (Real.sin ((p 0 1).re + s)) : ℝ) : ℂ) * Complex.I) ((((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im)
        * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) : ℝ) : ℂ) +
        ((-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.sin
        (p 0 1).re) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])

private theorem hasDerivAt_unitaryTrig_xi2 (p : Fin 2 → Fin 2 → ℂ) :
    ∀ i j, HasDerivAt (fun s : ℝ => unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re ((p 0 1).im + s) i j)
      (unitaryDeriv_xi2 p i j) 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · have hx : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re)) -
        (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 1).re)) * (Real.sin ((p 0 0).re)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 0).re)) +
        (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 1).re)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re)) -
        (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 1).re)) * (Real.sin ((p 0 0).re)) : ℝ) : ℂ) + (((Real.cos ((p 0
        1).re)) * (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 0).re)) + (Real.cos ((p 0 0).im)) * (Real.cos ((p 0
        0).re)) * (Real.sin ((p 0 1).re)) : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => ((Real.cos ((p 0 1).im + s)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 0).im)) -
        (Real.sin ((p 0 1).im + s)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) : ℝ)) 0 = (-(Real.cos (p 0
        1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((Real.cos ((p 0 1).im + s)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) +
        (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 1).im + s)) * (Real.sin ((p 0 0).im)) : ℝ)) 0 = ((Real.cos (p 0
        1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) - (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) *
        (Real.sin (p 0 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((Real.cos ((p 0 1).im + s)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 0).im)) -
        (Real.sin ((p 0 1).im + s)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) : ℝ) : ℂ) + (((Real.cos ((p 0
        1).im + s)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) + (Real.cos ((p 0 0).re)) * (Real.sin ((p 0
        1).im + s)) * (Real.sin ((p 0 0).im)) : ℝ) : ℂ) * Complex.I) (((-(Real.cos (p 0 1).im) * (Real.sin (p 0
        0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) : ℝ) :
        ℂ) + (((Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) - (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => (-(Real.cos ((p 0 1).im + s)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 0).im)) -
        (Real.sin ((p 0 1).im + s)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) : ℝ)) 0 = (-(Real.cos (p 0
        1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => (-(Real.cos ((p 0 1).im + s)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) +
        (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 1).im + s)) * (Real.sin ((p 0 0).im)) : ℝ)) 0 = ((Real.cos (p 0
        1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) + (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) *
        (Real.sin (p 0 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => ((-(Real.cos ((p 0 1).im + s)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 0).im))
        - (Real.sin ((p 0 1).im + s)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) : ℝ) : ℂ) + ((-(Real.cos
        ((p 0 1).im + s)) * (Real.sin ((p 0 0).im)) * (Real.sin ((p 0 0).re)) + (Real.cos ((p 0 0).re)) * (Real.sin
        ((p 0 1).im + s)) * (Real.sin ((p 0 0).im)) : ℝ) : ℂ) * Complex.I) (((-(Real.cos (p 0 1).im) * (Real.sin (p 0
        0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) : ℝ) :
        ℂ) + (((Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) + (Real.sin (p 0 1).im) *
        (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re)) +
        (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 1).re)) * (Real.sin ((p 0 0).re)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 0).re)) -
        (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re)) * (Real.sin ((p 0 1).re)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((Real.cos ((p 0 1).re)) * (Real.cos ((p 0 0).im)) * (Real.cos ((p 0 0).re)) +
        (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 1).re)) * (Real.sin ((p 0 0).re)) : ℝ) : ℂ) + (((Real.cos ((p 0
        1).re)) * (Real.cos ((p 0 0).im)) * (Real.sin ((p 0 0).re)) - (Real.cos ((p 0 0).im)) * (Real.cos ((p 0
        0).re)) * (Real.sin ((p 0 1).re)) : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])

private theorem hasDerivAt_scaleTrig_b1 (p : Fin 2 → Fin 2 → ℂ) :
    ∀ i j, HasDerivAt (fun s : ℝ => scaleTrig ((p 1 0).re + s) (p 1 0).im (p 1 1).re (p 1 1).im i j) (scaleDeriv_b1 p
      i j) 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · have hx : deriv (fun s : ℝ => ((((p 1 0).re + s)) : ℝ)) 0 = (1 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => (0 : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((((p 1 0).re + s)) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) (((1 : ℝ) : ℂ) + ((0 :
        ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => ((((p 1 0).re + s)) * (((p 1 1).re)) : ℝ)) 0 = (((p 1 1).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((((p 1 0).re + s)) * (((p 1 1).im)) : ℝ)) 0 = (((p 1 1).im) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((((p 1 0).re + s)) * (((p 1 1).re)) : ℝ) : ℂ) + (((((p 1 0).re + s)) * (((p 1
        1).im)) : ℝ) : ℂ) * Complex.I) (((((p 1 1).re) : ℝ) : ℂ) + ((((p 1 1).im) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => (0 : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) *
        Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx])
  · have hx : deriv (fun s : ℝ => ((((p 1 0).im)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => (0 : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((((p 1 0).im)) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) :
        ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])

private theorem hasDerivAt_scaleTrig_b2 (p : Fin 2 → Fin 2 → ℂ) :
    ∀ i j, HasDerivAt (fun s : ℝ => scaleTrig (p 1 0).re ((p 1 0).im + s) (p 1 1).re (p 1 1).im i j) (scaleDeriv_b2 p
      i j) 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · have hx : deriv (fun s : ℝ => ((((p 1 0).re)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => (0 : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((((p 1 0).re)) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) :
        ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => ((((p 1 0).re)) * (((p 1 1).re)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((((p 1 0).re)) * (((p 1 1).im)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((((p 1 0).re)) * (((p 1 1).re)) : ℝ) : ℂ) + (((((p 1 0).re)) * (((p 1 1).im)) :
        ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => (0 : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) *
        Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx])
  · have hx : deriv (fun s : ℝ => ((((p 1 0).im + s)) : ℝ)) 0 = (1 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => (0 : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((((p 1 0).im + s)) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) (((1 : ℝ) : ℂ) + ((0 :
        ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])

private theorem hasDerivAt_scaleTrig_z1 (p : Fin 2 → Fin 2 → ℂ) :
    ∀ i j, HasDerivAt (fun s : ℝ => scaleTrig (p 1 0).re (p 1 0).im ((p 1 1).re + s) (p 1 1).im i j) (scaleDeriv_z1 p
      i j) 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · have hx : deriv (fun s : ℝ => ((((p 1 0).re)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => (0 : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((((p 1 0).re)) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) :
        ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => ((((p 1 0).re)) * (((p 1 1).re + s)) : ℝ)) 0 = (((p 1 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((((p 1 0).re)) * (((p 1 1).im)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((((p 1 0).re)) * (((p 1 1).re + s)) : ℝ) : ℂ) + (((((p 1 0).re)) * (((p 1 1).im))
        : ℝ) : ℂ) * Complex.I) (((((p 1 0).re) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => (0 : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) *
        Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx])
  · have hx : deriv (fun s : ℝ => ((((p 1 0).im)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => (0 : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((((p 1 0).im)) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) :
        ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])

private theorem hasDerivAt_scaleTrig_z2 (p : Fin 2 → Fin 2 → ℂ) :
    ∀ i j, HasDerivAt (fun s : ℝ => scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re ((p 1 1).im + s) i j) (scaleDeriv_z2 p
      i j) 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · have hx : deriv (fun s : ℝ => ((((p 1 0).re)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => (0 : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((((p 1 0).re)) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) :
        ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => ((((p 1 0).re)) * (((p 1 1).re)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => ((((p 1 0).re)) * (((p 1 1).im + s)) : ℝ)) 0 = (((p 1 0).re) : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((((p 1 0).re)) * (((p 1 1).re)) : ℝ) : ℂ) + (((((p 1 0).re)) * (((p 1 1).im + s))
        : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((((p 1 0).re) : ℝ) : ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])
  · have hx : deriv (fun s : ℝ => (0 : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) *
        Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx])
  · have hx : deriv (fun s : ℝ => ((((p 1 0).im)) : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    have hy : deriv (fun s : ℝ => (0 : ℝ)) 0 = (0 : ℝ) := by
      conv_lhs => simp (disch := first | fun_prop | simp)
      all_goals first | ring1 | (field_simp; ring1)
    show HasDerivAt (fun s : ℝ => (((((p 1 0).im)) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) (((0 : ℝ) : ℂ) + ((0 : ℝ) :
        ℂ) * Complex.I) 0
    exact (hasDerivAt_reim _ _ _ _ _ (DifferentiableAt.hasDerivAt (by fun_prop))
      (DifferentiableAt.hasDerivAt (by fun_prop))).congr_deriv (by rw [hx, hy])

private theorem unitaryDeriv_eq_psi (p : Fin 2 → Fin 2 → ℂ)
    :
    unitaryDeriv_psi p = rightMC_psi p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [unitaryDeriv_psi, rightMC_psi, unitaryTrig, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination

private theorem column_eq_psi (p : Fin 2 → Fin 2 → ℂ)
    :
    splitColumn0 p = scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re (p 1 1).im * rightMC_psi p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [splitColumn0, scaleTrig, rightMC_psi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination

private theorem unitaryDeriv_eq_eta (p : Fin 2 → Fin 2 → ℂ)
    (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2 = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0
    1).im ^ 2 = 1) :
    unitaryDeriv_eta p = rightMC_eta p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [unitaryDeriv_eta, rightMC_eta, unitaryTrig, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) - (Real.sin (p 0
        1).re) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re)) * hξ₂
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0
        0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im)) * hξ₂
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination (-(Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) + (Real.cos (p 0
        0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).re)) * hξ₁
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination (-(Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0
        0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im)) * hξ₁
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) + (Real.cos (p 0
        0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).re)) * hξ₁
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0
        0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im)) * hξ₁
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) + (Real.sin (p 0
        1).re) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re)) * hξ₂
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0
        0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im)) * hξ₂

private theorem column_eq_eta (p : Fin 2 → Fin 2 → ℂ)
    :
    splitColumn1 p = scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re (p 1 1).im * rightMC_eta p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [splitColumn1, scaleTrig, rightMC_eta, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination

private theorem unitaryDeriv_eq_xi1 (p : Fin 2 → Fin 2 → ℂ)
    (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re
    ^ 2 = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1) :
    unitaryDeriv_xi1 p = rightMC_xi1 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [unitaryDeriv_xi1, rightMC_xi1, unitaryTrig, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) ^ 2 * (Real.sin (p 0
        0).re) + (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) ^ 2) *
        hξ₂
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination (-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0
        0).im) ^ 2 + (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) ^ 2 * (Real.sin (p 0
        0).re)) * hξ₂
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination (-(Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0
        0).re) - (Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) -
        (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos
        (p 0 0).re) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)) * hη + ((Real.cos (p
        0 1).im) * (Real.sin (p 0 0).im) ^ 3 * (Real.sin (p 0 0).re) - (Real.cos (p 0 1).im) * (Real.sin (p 0 0).im)
        * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) ^ 3 -
        (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)) * hξ₁
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0
        0).im) - (Real.cos (p 0 1).re) ^ 2 * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) +
        (Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 0).im) - (Real.sin
        (p 0 1).re) ^ 2 * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re)) * hη + (-(Real.cos
        (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) ^ 3 + (Real.cos (p 0 1).im) * (Real.cos (p 0
        0).re) * (Real.sin (p 0 0).im) + (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) ^ 3 * (Real.sin (p 0 0).re) -
        (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re)) * hξ₁
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination (-(Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0
        0).re) + (Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) -
        (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos
        (p 0 0).re) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)) * hη + ((Real.cos (p
        0 1).im) * (Real.sin (p 0 0).im) ^ 3 * (Real.sin (p 0 0).re) - (Real.cos (p 0 1).im) * (Real.sin (p 0 0).im)
        * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) ^ 3 +
        (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)) * hξ₁
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0
        0).im) + (Real.cos (p 0 1).re) ^ 2 * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) +
        (Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 0).im) + (Real.sin
        (p 0 1).re) ^ 2 * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re)) * hη + (-(Real.cos
        (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) ^ 3 + (Real.cos (p 0 1).im) * (Real.cos (p 0
        0).re) * (Real.sin (p 0 0).im) - (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) ^ 3 * (Real.sin (p 0 0).re) +
        (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re)) * hξ₁
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination (-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) ^ 2 * (Real.sin (p 0
        0).re) + (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) ^ 2) *
        hξ₂
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0
        0).im) ^ 2 + (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) ^ 2 * (Real.sin (p 0
        0).re)) * hξ₂

private theorem column_eq_xi1 (p : Fin 2 → Fin 2 → ℂ)
    :
    splitColumn2 p = scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re (p 1 1).im * rightMC_xi1 p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [splitColumn2, scaleTrig, rightMC_xi1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination

private theorem unitaryDeriv_eq_xi2 (p : Fin 2 → Fin 2 → ℂ)
    (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re
    ^ 2 = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1) :
    unitaryDeriv_xi2 p = rightMC_xi2 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [unitaryDeriv_xi2, rightMC_xi2, unitaryTrig, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination (-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) ^ 2 * (Real.sin (p 0
        0).re) - (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) ^ 2) *
        hξ₂
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0
        0).im) ^ 2 - (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) ^ 2 * (Real.sin (p 0
        0).re)) * hξ₂
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0
        0).re) + (Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) +
        (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) + (Real.cos
        (p 0 0).re) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)) * hη + (-(Real.cos
        (p 0 1).im) * (Real.sin (p 0 0).im) ^ 3 * (Real.sin (p 0 0).re) + (Real.cos (p 0 1).im) * (Real.sin (p 0
        0).im) * (Real.sin (p 0 0).re) - (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) ^ 3 +
        (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)) * hξ₁
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination (-(Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0
        0).im) + (Real.cos (p 0 1).re) ^ 2 * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) -
        (Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 0).im) + (Real.sin
        (p 0 1).re) ^ 2 * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re)) * hη + ((Real.cos (p
        0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) ^ 3 - (Real.cos (p 0 1).im) * (Real.cos (p 0 0).re)
        * (Real.sin (p 0 0).im) - (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) ^ 3 * (Real.sin (p 0 0).re) +
        (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re)) * hξ₁
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0
        0).re) - (Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) +
        (Real.cos (p 0 1).im) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) - (Real.cos
        (p 0 0).re) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)) * hη + (-(Real.cos
        (p 0 1).im) * (Real.sin (p 0 0).im) ^ 3 * (Real.sin (p 0 0).re) + (Real.cos (p 0 1).im) * (Real.sin (p 0
        0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) ^ 3 -
        (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im)) * hξ₁
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination (-(Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0
        0).im) - (Real.cos (p 0 1).re) ^ 2 * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) -
        (Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 0).im) - (Real.sin
        (p 0 1).re) ^ 2 * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re)) * hη + ((Real.cos (p
        0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) ^ 3 - (Real.cos (p 0 1).im) * (Real.cos (p 0 0).re)
        * (Real.sin (p 0 0).im) + (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) ^ 3 * (Real.sin (p 0 0).re) -
        (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re)) * hξ₁
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).im) ^ 2 * (Real.sin (p 0
        0).re) - (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) ^ 2) *
        hξ₂
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination (-(Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0
        0).im) ^ 2 - (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).im) ^ 2 * (Real.sin (p 0
        0).re)) * hξ₂

private theorem column_eq_xi2 (p : Fin 2 → Fin 2 → ℂ)
    :
    splitColumn3 p = scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re (p 1 1).im * rightMC_xi2 p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [splitColumn3, scaleTrig, rightMC_xi2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination

private theorem column_eq_b1 (p : Fin 2 → Fin 2 → ℂ) :
    splitColumn4 p = scaleDeriv_b1 p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [splitColumn4, scaleDeriv_b1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im] <;>
    ring1

private theorem column_eq_b2 (p : Fin 2 → Fin 2 → ℂ) :
    splitColumn5 p = scaleDeriv_b2 p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [splitColumn5, scaleDeriv_b2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im] <;>
    ring1

private theorem column_eq_z1 (p : Fin 2 → Fin 2 → ℂ) :
    splitColumn6 p = scaleDeriv_z1 p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [splitColumn6, scaleDeriv_z1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im] <;>
    ring1

private theorem column_eq_z2 (p : Fin 2 → Fin 2 → ℂ) :
    splitColumn7 p = scaleDeriv_z2 p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [splitColumn7, scaleDeriv_z2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    refine Complex.ext ?_ ?_ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im] <;>
    ring1

private theorem det_unitaryTrig (p : Fin 2 → Fin 2 → ℂ)
    (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^ 2 = 1) (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im
    ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2 = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin
    (p 0 1).im ^ 2 = 1) :
    (unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im).det = ((Real.cos (p 0 0).re : ℂ) + (Real.sin (p 0 0).re
        : ℂ) * Complex.I) * ((Real.cos (p 0 0).re : ℂ) + (Real.sin (p 0 0).re : ℂ) * Complex.I) := by
  simp only [unitaryTrig, Matrix.det_fin_two_of]
  refine Complex.ext ?_ ?_
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination ((Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 0).im) ^ 2 + (Real.cos (p 0 1).im) ^ 2 *
        (Real.sin (p 0 0).im) ^ 2 + (Real.cos (p 0 0).im) ^ 2 * (Real.sin (p 0 1).re) ^ 2 + (Real.sin (p 0 1).im) ^ 2
        * (Real.sin (p 0 0).im) ^ 2 - 1) * hψ + (-2 * (Real.cos (p 0 1).re) ^ 2 * (Real.sin (p 0 0).re) ^ 2 +
        (Real.cos (p 0 1).re) ^ 2 - 2 * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 0).re) ^ 2 + (Real.sin (p 0 1).re)
        ^ 2) * hη + (2 * (Real.sin (p 0 0).im) ^ 2 * (Real.sin (p 0 0).re) ^ 2 - (Real.sin (p 0 0).im) ^ 2 - 2 *
        (Real.sin (p 0 0).re) ^ 2 + 1) * hξ₁ + (-2 * (Real.sin (p 0 0).im) ^ 2 * (Real.sin (p 0 0).re) ^ 2 +
        (Real.sin (p 0 0).im) ^ 2) * hξ₂
  · (try simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]) <;>
      linear_combination (2 * (Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).re) + 2 *
        (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) ^ 2 * (Real.sin (p 0 0).re)) * hη + (-2 * (Real.cos (p 0 0).re)
        * (Real.sin (p 0 0).im) ^ 2 * (Real.sin (p 0 0).re) + 2 * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).re)) *
        hξ₁ + (2 * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) ^ 2 * (Real.sin (p 0 0).re)) * hξ₂

private theorem normSq_phase_mul_self (ψ : ℝ) :
    Complex.normSq (((Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I) * ((Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) *
        Complex.I)) =
      1 := by
  have hψ := Real.cos_sq_add_sin_sq ψ
  have h1 : Complex.normSq ((Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I) = 1 := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]
    linear_combination hψ
  rw [map_mul, h1, mul_one]

private theorem leibniz_psi (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^ 2 = 1) (hη
    : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2
    = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1) :
    (0 : Matrix (Fin 2) (Fin 2) ℂ) * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im + scaleTrig (p 1 0).re
      (p 1 0).im (p 1 1).re (p 1 1).im * unitaryDeriv_psi p = splitColumn0 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0
      1).re (p 0 1).im := by
  rw [column_eq_psi p, unitaryDeriv_eq_psi p]
  noncomm_ring

private theorem fderiv_splitFormula_psi (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^
    2 = 1) (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p
    0 1).re ^ 2 = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1)
    (hd : DifferentiableAt ℝ splitFormula p) :
    fderiv ℝ splitFormula p (arrayBasis ⟨0, 0, 0⟩) = splitColumn0 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p
        0 1).im := by
  funext i j
  rw [← deriv_comp_line_apply splitFormula p hd]
  have h2 := hasDerivAt_mul2_entry (fun s : ℝ => scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re (p 1 1).im) (fun s : ℝ =>
    unitaryTrig ((p 0 0).re + s) (p 0 0).im (p 0 1).re (p 0 1).im) ((0 : Matrix (Fin 2) (Fin 2) ℂ)) (unitaryDeriv_psi
    p) (fun i j => hasDerivAt_constMat _ i j) (hasDerivAt_unitaryTrig_psi p) i j
  have hfun : (fun s : ℝ => splitFormula (p + s • arrayBasis ⟨0, 0, 0⟩) i j) = fun s : ℝ => (scaleTrig (p 1 0).re (p
      1 0).im (p 1 1).re (p 1 1).im * unitaryTrig ((p 0 0).re + s) (p 0 0).im (p 0 1).re (p 0 1).im) i j := by
    funext s
    simp only [splitFormula, Matrix.of_symm_apply, line_000_00re, line_000_00im, line_000_01re, line_000_01im,
      line_000_10re, line_000_10im, line_000_11re, line_000_11im]
  rw [hfun, h2.deriv]
  simp only [add_zero]
  exact congrFun (congrFun (leibniz_psi p hψ hη hξ₁ hξ₂) i) j

private theorem leibniz_eta (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^ 2 = 1) (hη
    : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2
    = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1) :
    (0 : Matrix (Fin 2) (Fin 2) ℂ) * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im + scaleTrig (p 1 0).re
      (p 1 0).im (p 1 1).re (p 1 1).im * unitaryDeriv_eta p = splitColumn1 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0
      1).re (p 0 1).im := by
  rw [column_eq_eta p, unitaryDeriv_eq_eta p hξ₁ hξ₂]
  noncomm_ring

private theorem fderiv_splitFormula_eta (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^
    2 = 1) (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p
    0 1).re ^ 2 = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1)
    (hd : DifferentiableAt ℝ splitFormula p) :
    fderiv ℝ splitFormula p (arrayBasis ⟨0, 0, 1⟩) = splitColumn1 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p
        0 1).im := by
  funext i j
  rw [← deriv_comp_line_apply splitFormula p hd]
  have h2 := hasDerivAt_mul2_entry (fun s : ℝ => scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re (p 1 1).im) (fun s : ℝ =>
    unitaryTrig (p 0 0).re ((p 0 0).im + s) (p 0 1).re (p 0 1).im) ((0 : Matrix (Fin 2) (Fin 2) ℂ)) (unitaryDeriv_eta
    p) (fun i j => hasDerivAt_constMat _ i j) (hasDerivAt_unitaryTrig_eta p) i j
  have hfun : (fun s : ℝ => splitFormula (p + s • arrayBasis ⟨0, 0, 1⟩) i j) = fun s : ℝ => (scaleTrig (p 1 0).re (p
      1 0).im (p 1 1).re (p 1 1).im * unitaryTrig (p 0 0).re ((p 0 0).im + s) (p 0 1).re (p 0 1).im) i j := by
    funext s
    simp only [splitFormula, Matrix.of_symm_apply, line_001_00re, line_001_00im, line_001_01re, line_001_01im,
      line_001_10re, line_001_10im, line_001_11re, line_001_11im]
  rw [hfun, h2.deriv]
  simp only [add_zero]
  exact congrFun (congrFun (leibniz_eta p hψ hη hξ₁ hξ₂) i) j

private theorem leibniz_xi1 (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^ 2 = 1) (hη
    : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2
    = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1) :
    (0 : Matrix (Fin 2) (Fin 2) ℂ) * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im + scaleTrig (p 1 0).re
      (p 1 0).im (p 1 1).re (p 1 1).im * unitaryDeriv_xi1 p = splitColumn2 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0
      1).re (p 0 1).im := by
  rw [column_eq_xi1 p, unitaryDeriv_eq_xi1 p hη hξ₁ hξ₂]
  noncomm_ring

private theorem fderiv_splitFormula_xi1 (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^
    2 = 1) (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p
    0 1).re ^ 2 = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1)
    (hd : DifferentiableAt ℝ splitFormula p) :
    fderiv ℝ splitFormula p (arrayBasis ⟨0, 1, 0⟩) = splitColumn2 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p
        0 1).im := by
  funext i j
  rw [← deriv_comp_line_apply splitFormula p hd]
  have h2 := hasDerivAt_mul2_entry (fun s : ℝ => scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re (p 1 1).im) (fun s : ℝ =>
    unitaryTrig (p 0 0).re (p 0 0).im ((p 0 1).re + s) (p 0 1).im) ((0 : Matrix (Fin 2) (Fin 2) ℂ)) (unitaryDeriv_xi1
    p) (fun i j => hasDerivAt_constMat _ i j) (hasDerivAt_unitaryTrig_xi1 p) i j
  have hfun : (fun s : ℝ => splitFormula (p + s • arrayBasis ⟨0, 1, 0⟩) i j) = fun s : ℝ => (scaleTrig (p 1 0).re (p
      1 0).im (p 1 1).re (p 1 1).im * unitaryTrig (p 0 0).re (p 0 0).im ((p 0 1).re + s) (p 0 1).im) i j := by
    funext s
    simp only [splitFormula, Matrix.of_symm_apply, line_010_00re, line_010_00im, line_010_01re, line_010_01im,
      line_010_10re, line_010_10im, line_010_11re, line_010_11im]
  rw [hfun, h2.deriv]
  simp only [add_zero]
  exact congrFun (congrFun (leibniz_xi1 p hψ hη hξ₁ hξ₂) i) j

private theorem leibniz_xi2 (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^ 2 = 1) (hη
    : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2
    = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1) :
    (0 : Matrix (Fin 2) (Fin 2) ℂ) * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im + scaleTrig (p 1 0).re
      (p 1 0).im (p 1 1).re (p 1 1).im * unitaryDeriv_xi2 p = splitColumn3 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0
      1).re (p 0 1).im := by
  rw [column_eq_xi2 p, unitaryDeriv_eq_xi2 p hη hξ₁ hξ₂]
  noncomm_ring

private theorem fderiv_splitFormula_xi2 (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^
    2 = 1) (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p
    0 1).re ^ 2 = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1)
    (hd : DifferentiableAt ℝ splitFormula p) :
    fderiv ℝ splitFormula p (arrayBasis ⟨0, 1, 1⟩) = splitColumn3 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p
        0 1).im := by
  funext i j
  rw [← deriv_comp_line_apply splitFormula p hd]
  have h2 := hasDerivAt_mul2_entry (fun s : ℝ => scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re (p 1 1).im) (fun s : ℝ =>
    unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re ((p 0 1).im + s)) ((0 : Matrix (Fin 2) (Fin 2) ℂ)) (unitaryDeriv_xi2
    p) (fun i j => hasDerivAt_constMat _ i j) (hasDerivAt_unitaryTrig_xi2 p) i j
  have hfun : (fun s : ℝ => splitFormula (p + s • arrayBasis ⟨0, 1, 1⟩) i j) = fun s : ℝ => (scaleTrig (p 1 0).re (p
      1 0).im (p 1 1).re (p 1 1).im * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re ((p 0 1).im + s)) i j := by
    funext s
    simp only [splitFormula, Matrix.of_symm_apply, line_011_00re, line_011_00im, line_011_01re, line_011_01im,
      line_011_10re, line_011_10im, line_011_11re, line_011_11im]
  rw [hfun, h2.deriv]
  simp only [add_zero]
  exact congrFun (congrFun (leibniz_xi2 p hψ hη hξ₁ hξ₂) i) j

private theorem leibniz_b1 (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^ 2 = 1) (hη :
    Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2 =
    1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1) :
    scaleDeriv_b1 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im + scaleTrig (p 1 0).re (p 1 0).im (p 1
      1).re (p 1 1).im * (0 : Matrix (Fin 2) (Fin 2) ℂ) = splitColumn4 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0
      1).re (p 0 1).im := by
  rw [column_eq_b1 p]
  noncomm_ring

private theorem fderiv_splitFormula_b1 (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^
    2 = 1) (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p
    0 1).re ^ 2 = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1)
    (hd : DifferentiableAt ℝ splitFormula p) :
    fderiv ℝ splitFormula p (arrayBasis ⟨1, 0, 0⟩) = splitColumn4 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p
        0 1).im := by
  funext i j
  rw [← deriv_comp_line_apply splitFormula p hd]
  have h2 := hasDerivAt_mul2_entry (fun s : ℝ => scaleTrig ((p 1 0).re + s) (p 1 0).im (p 1 1).re (p 1 1).im) (fun s
    : ℝ => unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im) (scaleDeriv_b1 p) ((0 : Matrix (Fin 2) (Fin 2)
    ℂ)) (hasDerivAt_scaleTrig_b1 p) (fun i j => hasDerivAt_constMat _ i j) i j
  have hfun : (fun s : ℝ => splitFormula (p + s • arrayBasis ⟨1, 0, 0⟩) i j) = fun s : ℝ => (scaleTrig ((p 1 0).re +
      s) (p 1 0).im (p 1 1).re (p 1 1).im * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im) i j := by
    funext s
    simp only [splitFormula, Matrix.of_symm_apply, line_100_00re, line_100_00im, line_100_01re, line_100_01im,
      line_100_10re, line_100_10im, line_100_11re, line_100_11im]
  rw [hfun, h2.deriv]
  simp only [add_zero]
  exact congrFun (congrFun (leibniz_b1 p hψ hη hξ₁ hξ₂) i) j

private theorem leibniz_b2 (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^ 2 = 1) (hη :
    Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2 =
    1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1) :
    scaleDeriv_b2 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im + scaleTrig (p 1 0).re (p 1 0).im (p 1
      1).re (p 1 1).im * (0 : Matrix (Fin 2) (Fin 2) ℂ) = splitColumn5 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0
      1).re (p 0 1).im := by
  rw [column_eq_b2 p]
  noncomm_ring

private theorem fderiv_splitFormula_b2 (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^
    2 = 1) (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p
    0 1).re ^ 2 = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1)
    (hd : DifferentiableAt ℝ splitFormula p) :
    fderiv ℝ splitFormula p (arrayBasis ⟨1, 0, 1⟩) = splitColumn5 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p
        0 1).im := by
  funext i j
  rw [← deriv_comp_line_apply splitFormula p hd]
  have h2 := hasDerivAt_mul2_entry (fun s : ℝ => scaleTrig (p 1 0).re ((p 1 0).im + s) (p 1 1).re (p 1 1).im) (fun s
    : ℝ => unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im) (scaleDeriv_b2 p) ((0 : Matrix (Fin 2) (Fin 2)
    ℂ)) (hasDerivAt_scaleTrig_b2 p) (fun i j => hasDerivAt_constMat _ i j) i j
  have hfun : (fun s : ℝ => splitFormula (p + s • arrayBasis ⟨1, 0, 1⟩) i j) = fun s : ℝ => (scaleTrig (p 1 0).re ((p
      1 0).im + s) (p 1 1).re (p 1 1).im * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im) i j := by
    funext s
    simp only [splitFormula, Matrix.of_symm_apply, line_101_00re, line_101_00im, line_101_01re, line_101_01im,
      line_101_10re, line_101_10im, line_101_11re, line_101_11im]
  rw [hfun, h2.deriv]
  simp only [add_zero]
  exact congrFun (congrFun (leibniz_b2 p hψ hη hξ₁ hξ₂) i) j

private theorem leibniz_z1 (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^ 2 = 1) (hη :
    Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2 =
    1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1) :
    scaleDeriv_z1 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im + scaleTrig (p 1 0).re (p 1 0).im (p 1
      1).re (p 1 1).im * (0 : Matrix (Fin 2) (Fin 2) ℂ) = splitColumn6 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0
      1).re (p 0 1).im := by
  rw [column_eq_z1 p]
  noncomm_ring

private theorem fderiv_splitFormula_z1 (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^
    2 = 1) (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p
    0 1).re ^ 2 = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1)
    (hd : DifferentiableAt ℝ splitFormula p) :
    fderiv ℝ splitFormula p (arrayBasis ⟨1, 1, 0⟩) = splitColumn6 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p
        0 1).im := by
  funext i j
  rw [← deriv_comp_line_apply splitFormula p hd]
  have h2 := hasDerivAt_mul2_entry (fun s : ℝ => scaleTrig (p 1 0).re (p 1 0).im ((p 1 1).re + s) (p 1 1).im) (fun s
    : ℝ => unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im) (scaleDeriv_z1 p) ((0 : Matrix (Fin 2) (Fin 2)
    ℂ)) (hasDerivAt_scaleTrig_z1 p) (fun i j => hasDerivAt_constMat _ i j) i j
  have hfun : (fun s : ℝ => splitFormula (p + s • arrayBasis ⟨1, 1, 0⟩) i j) = fun s : ℝ => (scaleTrig (p 1 0).re (p
      1 0).im ((p 1 1).re + s) (p 1 1).im * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im) i j := by
    funext s
    simp only [splitFormula, Matrix.of_symm_apply, line_110_00re, line_110_00im, line_110_01re, line_110_01im,
      line_110_10re, line_110_10im, line_110_11re, line_110_11im]
  rw [hfun, h2.deriv]
  simp only [add_zero]
  exact congrFun (congrFun (leibniz_z1 p hψ hη hξ₁ hξ₂) i) j

private theorem leibniz_z2 (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^ 2 = 1) (hη :
    Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2 =
    1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1) :
    scaleDeriv_z2 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im + scaleTrig (p 1 0).re (p 1 0).im (p 1
      1).re (p 1 1).im * (0 : Matrix (Fin 2) (Fin 2) ℂ) = splitColumn7 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0
      1).re (p 0 1).im := by
  rw [column_eq_z2 p]
  noncomm_ring

private theorem fderiv_splitFormula_z2 (p : Fin 2 → Fin 2 → ℂ) (hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^
    2 = 1) (hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1) (hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p
    0 1).re ^ 2 = 1) (hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1)
    (hd : DifferentiableAt ℝ splitFormula p) :
    fderiv ℝ splitFormula p (arrayBasis ⟨1, 1, 1⟩) = splitColumn7 p * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p
        0 1).im := by
  funext i j
  rw [← deriv_comp_line_apply splitFormula p hd]
  have h2 := hasDerivAt_mul2_entry (fun s : ℝ => scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re ((p 1 1).im + s)) (fun s
    : ℝ => unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im) (scaleDeriv_z2 p) ((0 : Matrix (Fin 2) (Fin 2)
    ℂ)) (hasDerivAt_scaleTrig_z2 p) (fun i j => hasDerivAt_constMat _ i j) i j
  have hfun : (fun s : ℝ => splitFormula (p + s • arrayBasis ⟨1, 1, 1⟩) i j) = fun s : ℝ => (scaleTrig (p 1 0).re (p
      1 0).im (p 1 1).re ((p 1 1).im + s) * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im) i j := by
    funext s
    simp only [splitFormula, Matrix.of_symm_apply, line_111_00re, line_111_00im, line_111_01re, line_111_01im,
      line_111_10re, line_111_10im, line_111_11re, line_111_11im]
  rw [hfun, h2.deriv]
  simp only [add_zero]
  exact congrFun (congrFun (leibniz_z2 p hψ hη hξ₁ hξ₂) i) j

private theorem fderiv_splitFormula_eq (p : Fin 2 → Fin 2 → ℂ) :
    (fderiv ℝ splitFormula p : (Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → Fin 2 → ℂ)) =
      (twistLM 1 (unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im)).restrictScalars ℝ ∘ₗ splitMap p := by
  have hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 0).re
  have hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 0).im
  have hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 1).re
  have hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 1).im
  have hd : DifferentiableAt ℝ splitFormula p := differentiableAt_splitFormula p
  refine arrayBasis.ext fun klt => ?_
  obtain ⟨k, l, t⟩ := klt
  rw [LinearMap.comp_apply]
  erw [splitMap_basis]
  rw [LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, twistLM_apply]
  fin_cases k <;> fin_cases l <;> fin_cases t <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, slotCol_000, slotCol_001, slotCol_010, slotCol_011,
      slotCol_100, slotCol_101, slotCol_110, slotCol_111, splitColumnVec_0, splitColumnVec_1, splitColumnVec_2,
      splitColumnVec_3, splitColumnVec_4, splitColumnVec_5, splitColumnVec_6, splitColumnVec_7, Matrix.one_mul,
      one_mul]
  exacts [fderiv_splitFormula_psi p hψ hη hξ₁ hξ₂ hd, fderiv_splitFormula_eta p hψ hη hξ₁ hξ₂ hd,
      fderiv_splitFormula_xi1 p hψ hη hξ₁ hξ₂ hd, fderiv_splitFormula_xi2 p hψ hη hξ₁ hξ₂ hd,
    fderiv_splitFormula_b1 p hψ hη hξ₁ hξ₂ hd, fderiv_splitFormula_b2 p hψ hη hξ₁ hξ₂ hd, fderiv_splitFormula_z1 p hψ
        hη hξ₁ hξ₂ hd, fderiv_splitFormula_z2 p hψ hη hξ₁ hξ₂ hd]

private theorem det_fderiv_splitFormula (p : Fin 2 → Fin 2 → ℂ) :
    (fderiv ℝ splitFormula p).det = 2 * (p 1 0).re ^ 3 * (p 1 0).im ^ 3 * Real.sin (p 0 0).im * Real.cos (p 0 0).im
      := by
  have hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 0).re
  have hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 0).im
  have hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 1).re
  have hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 1).im
  unfold ContinuousLinearMap.det
  rw [fderiv_splitFormula_eq p, LinearMap.det_comp, twistLM_restrictScalars_det, Matrix.det_one, one_mul,
    det_unitaryTrig p hψ hη hξ₁ hξ₂, normSq_phase_mul_self, one_pow, one_mul, det_eq_det_coordTable,
        coordTable_splitMap,
    Matrix.det_submatrix_equiv_self, det_splitTable]

private theorem angle_eq_of_cos_eq_of_sin_eq {φ ψ : ℝ} (hφ : 0 < φ) (hφ2 : φ < 2 * Real.pi) (hψ : 0 < ψ)
    (hψ2 : ψ < 2 * Real.pi) (hc : Real.cos φ = Real.cos ψ) (hs : Real.sin φ = Real.sin ψ) : φ = ψ := by
  rcases le_or_gt 0 (Real.sin φ) with h | h
  · have hφπ : φ ≤ Real.pi := not_lt.1 fun hcon => by
      have h1 : 0 < Real.sin (φ - Real.pi) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at h1
      linarith
    have hψπ : ψ ≤ Real.pi := not_lt.1 fun hcon => by
      have h1 : 0 < Real.sin (ψ - Real.pi) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at h1
      linarith
    exact Real.injOn_cos ⟨hφ.le, hφπ⟩ ⟨hψ.le, hψπ⟩ hc
  · have hφπ : Real.pi < φ := not_le.1 fun hcon => by
      have h1 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ.le hcon
      linarith
    have hψπ : Real.pi < ψ := not_le.1 fun hcon => by
      have h1 : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_nonneg_of_le_pi hψ.le hcon
      linarith
    have h2 : Real.cos (φ - Real.pi) = Real.cos (ψ - Real.pi) := by rw [Real.cos_sub_pi, Real.cos_sub_pi, hc]
    have h3 : φ - Real.pi = ψ - Real.pi :=
      Real.injOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h2
    linarith

private theorem eq_of_mul_self_eq_of_pos (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x * x = y * y) : x = y := by
  have h2 : (x - y) * (x + y) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h0 | h0
  · linarith
  · linarith

private theorem parts_eq_of_mul_eq (m c s x y x' y' : ℝ) (hm : m ≠ 0) (hcs : c ^ 2 + s ^ 2 = 1)
    (h1 : m * (c * x + s * y) = m * (c * x' + s * y')) (h2 : m * (s * x - c * y) = m * (s * x' - c * y')) :
    x = x' ∧ y = y' := by
  have h1' : c * x + s * y = c * x' + s * y' := mul_left_cancel₀ hm h1
  have h2' : s * x - c * y = s * x' - c * y' := mul_left_cancel₀ hm h2
  constructor
  · linear_combination c * h1' + s * h2' - (x - x') * hcs
  · linear_combination s * h1' - c * h2' - (y - y') * hcs

private theorem shear_eq_of_mul_eq (m x y a b z₁ z₂ z₁' z₂' : ℝ) (hm : m ≠ 0) (hab : 0 < a ^ 2 + b ^ 2)
    (h1 : m * x + m * (z₁ * a - z₂ * b) = m * x + m * (z₁' * a - z₂' * b))
    (h2 : m * y + m * (z₁ * b + z₂ * a) = m * y + m * (z₁' * b + z₂' * a)) : z₁ = z₁' ∧ z₂ = z₂' := by
  have g1 : z₁ * a - z₂ * b = z₁' * a - z₂' * b := mul_left_cancel₀ hm (by linear_combination h1)
  have g2 : z₁ * b + z₂ * a = z₁' * b + z₂' * a := mul_left_cancel₀ hm (by linear_combination h2)
  have h3 : (z₁ - z₁') * (a ^ 2 + b ^ 2) = 0 := by linear_combination a * g1 + b * g2
  have h4 : (z₂ - z₂') * (a ^ 2 + b ^ 2) = 0 := by linear_combination a * g2 - b * g1
  constructor
  · linarith [(mul_eq_zero.1 h3).resolve_right hab.ne']
  · linarith [(mul_eq_zero.1 h4).resolve_right hab.ne']

private theorem det_scaleTrig (b₁ b₂ z₁ z₂ : ℝ) : (scaleTrig b₁ b₂ z₁ z₂).det = ((b₁ * b₂ : ℝ) : ℂ) := by
  simp only [scaleTrig, Matrix.det_fin_two_of]
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im] <;>
    ring

private theorem normSq_phase (ψ : ℝ) : Complex.normSq ((Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I) = 1 := by
  have hψ := Real.cos_sq_add_sin_sq ψ
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]
  linear_combination hψ

private theorem injOn_splitChart : Set.InjOn splitChart splitDom := by
  intro p hp q hq h
  have hgp : p ∈ splitGuard := ⟨hp.1, hp.2.1⟩
  have hgq : q ∈ splitGuard := ⟨hq.1, hq.2.1⟩
  simp only [splitDom, Set.mem_setOf_eq] at hp hq
  obtain ⟨hb₁, hb₂, hψ₀, hψ₁, hη₀, hη₁, hξ₁₀, hξ₁₁, hξ₂₀, hξ₂₁⟩ := hp
  obtain ⟨hb₁', hb₂', hψ₀', hψ₁', hη₀', hη₁', hξ₁₀', hξ₁₁', hξ₂₀', hξ₂₁'⟩ := hq
  have hψ : Real.cos (p 0 0).re ^ 2 + Real.sin (p 0 0).re ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 0).re
  have hη : Real.cos (p 0 0).im ^ 2 + Real.sin (p 0 0).im ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 0).im
  have hξ₁ : Real.cos (p 0 1).re ^ 2 + Real.sin (p 0 1).re ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 1).re
  have hξ₂ : Real.cos (p 0 1).im ^ 2 + Real.sin (p 0 1).im ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 1).im
  have hψ' : Real.cos (q 0 0).re ^ 2 + Real.sin (q 0 0).re ^ 2 = 1 := Real.cos_sq_add_sin_sq (q 0 0).re
  have hη' : Real.cos (q 0 0).im ^ 2 + Real.sin (q 0 0).im ^ 2 = 1 := Real.cos_sq_add_sin_sq (q 0 0).im
  have hξ₁' : Real.cos (q 0 1).re ^ 2 + Real.sin (q 0 1).re ^ 2 = 1 := Real.cos_sq_add_sin_sq (q 0 1).re
  have hξ₂' : Real.cos (q 0 1).im ^ 2 + Real.sin (q 0 1).im ^ 2 = 1 := Real.cos_sq_add_sin_sq (q 0 1).im
  have hsη : 0 < Real.sin (p 0 0).im := Real.sin_pos_of_pos_of_lt_pi hη₀ (by linarith [Real.pi_pos])
  have hcη : 0 < Real.cos (p 0 0).im := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hη₁⟩
  have hcη' : 0 < Real.cos (q 0 0).im := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hη₁'⟩
  have hF : splitFormula p = splitFormula q := by
    rw [← splitChart_eq_formula p hgp, ← splitChart_eq_formula q hgq, h]
  have hF' : Matrix.of.symm (scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re (p 1 1).im * unitaryTrig (p 0 0).re (p 0
      0).im (p 0 1).re (p 0 1).im) = Matrix.of.symm (scaleTrig (q 1 0).re (q 1 0).im (q 1 1).re (q 1 1).im *
      unitaryTrig (q 0 0).re (q 0 0).im (q 0 1).re (q 0 1).im) := hF
  have hM : scaleTrig (p 1 0).re (p 1 0).im (p 1 1).re (p 1 1).im * unitaryTrig (p 0 0).re (p 0 0).im (p 0 1).re (p 0
      1).im = scaleTrig (q 1 0).re (q 1 0).im (q 1 1).re (q 1 1).im * unitaryTrig (q 0 0).re (q 0 0).im (q 0 1).re (q
      0 1).im := Matrix.of.symm.injective hF'
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  have e01 := congrFun (congrFun hM 0) 1
  simp only [scaleTrig, unitaryTrig, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta, Fin.mk_one,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e10 e11 e01
  have e10re := congrArg Complex.re e10
  have e10im := congrArg Complex.im e10
  have e11re := congrArg Complex.re e11
  have e11im := congrArg Complex.im e11
  have e01re := congrArg Complex.re e01
  have e01im := congrArg Complex.im e01
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im] at e10re e10im e11re e11im e01re e01im
  have hb₂eq : (p 1 0).im = (q 1 0).im := by
    refine eq_of_mul_self_eq_of_pos _ _ hb₂ hb₂' ?_
    linear_combination (-((p 1 0).im) * (Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) - ((p 1
        0).im) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re) - ((q 1 0).im) * (Real.cos (q
        0 1).im) * (Real.cos (q 0 0).re) * (Real.sin (q 0 0).im) - ((q 1 0).im) * (Real.sin (q 0 1).im) * (Real.sin
        (q 0 0).im) * (Real.sin (q 0 0).re)) * e10re + (-((p 1 0).im) * (Real.cos (p 0 1).im) * (Real.sin (p 0 0).im)
        * (Real.sin (p 0 0).re) + ((p 1 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0
        0).im) - ((q 1 0).im) * (Real.cos (q 0 1).im) * (Real.sin (q 0 0).im) * (Real.sin (q 0 0).re) + ((q 1 0).im)
        * (Real.cos (q 0 0).re) * (Real.sin (q 0 1).im) * (Real.sin (q 0 0).im)) * e10im + (((p 1 0).im) * (Real.cos
        (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) + ((p 1 0).im) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).re) + ((q 1 0).im) * (Real.cos (q 0 1).re) * (Real.cos (q 0 0).im)
        * (Real.cos (q 0 0).re) + ((q 1 0).im) * (Real.cos (q 0 0).im) * (Real.sin (q 0 1).re) * (Real.sin (q 0
        0).re)) * e11re + (((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) - ((p
        1 0).im) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re) + ((q 1 0).im) * (Real.cos
        (q 0 1).re) * (Real.cos (q 0 0).im) * (Real.sin (q 0 0).re) - ((q 1 0).im) * (Real.cos (q 0 0).im) *
        (Real.cos (q 0 0).re) * (Real.sin (q 0 1).re)) * e11im + (-((p 1 0).im) ^ 2 * (Real.cos (p 0 1).re) ^ 2 *
        (Real.cos (p 0 0).im) ^ 2 - ((p 1 0).im) ^ 2 * (Real.cos (p 0 1).im) ^ 2 * (Real.sin (p 0 0).im) ^ 2 - ((p 1
        0).im) ^ 2 * (Real.cos (p 0 0).im) ^ 2 * (Real.sin (p 0 1).re) ^ 2 - ((p 1 0).im) ^ 2 * (Real.sin (p 0 1).im)
        ^ 2 * (Real.sin (p 0 0).im) ^ 2) * hψ + (-((p 1 0).im) ^ 2 * (Real.cos (p 0 1).re) ^ 2 - ((p 1 0).im) ^ 2 *
        (Real.sin (p 0 1).re) ^ 2) * hη + (((p 1 0).im) ^ 2 * (Real.sin (p 0 0).im) ^ 2 - ((p 1 0).im) ^ 2) * hξ₁ +
        (-((p 1 0).im) ^ 2 * (Real.sin (p 0 0).im) ^ 2) * hξ₂ + (((q 1 0).im) ^ 2 * (Real.cos (q 0 1).re) ^ 2 *
        (Real.cos (q 0 0).im) ^ 2 + ((q 1 0).im) ^ 2 * (Real.cos (q 0 1).im) ^ 2 * (Real.sin (q 0 0).im) ^ 2 + ((q 1
        0).im) ^ 2 * (Real.cos (q 0 0).im) ^ 2 * (Real.sin (q 0 1).re) ^ 2 + ((q 1 0).im) ^ 2 * (Real.sin (q 0 1).im)
        ^ 2 * (Real.sin (q 0 0).im) ^ 2) * hψ' + (((q 1 0).im) ^ 2 * (Real.cos (q 0 1).re) ^ 2 + ((q 1 0).im) ^ 2 *
        (Real.sin (q 0 1).re) ^ 2) * hη' + (-((q 1 0).im) ^ 2 * (Real.sin (q 0 0).im) ^ 2 + ((q 1 0).im) ^ 2) * hξ₁'
        + (((q 1 0).im) ^ 2 * (Real.sin (q 0 0).im) ^ 2) * hξ₂'
  have hηeq : (p 0 0).im = (q 0 0).im := by
    have hsq : (p 1 0).im * (p 1 0).im * (Real.cos (p 0 0).im * Real.cos (p 0 0).im) = (q 1 0).im * (q 1 0).im *
        (Real.cos (q 0 0).im * Real.cos (q 0 0).im) := by
      linear_combination (((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) + ((p
          1 0).im) * (Real.cos (p 0 0).im) * (Real.sin (p 0 1).re) * (Real.sin (p 0 0).re) + ((q 1 0).im) * (Real.cos
          (q 0 1).re) * (Real.cos (q 0 0).im) * (Real.cos (q 0 0).re) + ((q 1 0).im) * (Real.cos (q 0 0).im) *
          (Real.sin (q 0 1).re) * (Real.sin (q 0 0).re)) * e11re + (((p 1 0).im) * (Real.cos (p 0 1).re) * (Real.cos
          (p 0 0).im) * (Real.sin (p 0 0).re) - ((p 1 0).im) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) *
          (Real.sin (p 0 1).re) + ((q 1 0).im) * (Real.cos (q 0 1).re) * (Real.cos (q 0 0).im) * (Real.sin (q 0
          0).re) - ((q 1 0).im) * (Real.cos (q 0 0).im) * (Real.cos (q 0 0).re) * (Real.sin (q 0 1).re)) * e11im +
          (-((p 1 0).im) ^ 2 * (Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 0).im) ^ 2 - ((p 1 0).im) ^ 2 * (Real.cos
          (p 0 0).im) ^ 2 * (Real.sin (p 0 1).re) ^ 2) * hψ + (-((p 1 0).im) ^ 2 * (Real.cos (p 0 1).re) ^ 2 - ((p 1
          0).im) ^ 2 * (Real.sin (p 0 1).re) ^ 2 + ((p 1 0).im) ^ 2) * hη + (((p 1 0).im) ^ 2 * (Real.sin (p 0 0).im)
          ^ 2 - ((p 1 0).im) ^ 2) * hξ₁ + (((q 1 0).im) ^ 2 * (Real.cos (q 0 1).re) ^ 2 * (Real.cos (q 0 0).im) ^ 2 +
          ((q 1 0).im) ^ 2 * (Real.cos (q 0 0).im) ^ 2 * (Real.sin (q 0 1).re) ^ 2) * hψ' + (((q 1 0).im) ^ 2 *
          (Real.cos (q 0 1).re) ^ 2 + ((q 1 0).im) ^ 2 * (Real.sin (q 0 1).re) ^ 2 - ((q 1 0).im) ^ 2) * hη' + (-((q
          1 0).im) ^ 2 * (Real.sin (q 0 0).im) ^ 2 + ((q 1 0).im) ^ 2) * hξ₁'
    rw [← hb₂eq] at hsq
    have hc := eq_of_mul_self_eq_of_pos _ _ hcη hcη' (mul_left_cancel₀ (mul_pos hb₂ hb₂).ne' hsq)
    exact Real.injOn_cos ⟨hη₀.le, by linarith [Real.pi_pos]⟩ ⟨hη₀'.le, by linarith [Real.pi_pos]⟩ hc
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, det_scaleTrig, det_scaleTrig, det_unitaryTrig p hψ hη hξ₁ hξ₂, det_unitaryTrig
      q hψ' hη' hξ₁' hξ₂'] at hdet
  have hb₁eq : (p 1 0).re = (q 1 0).re := by
    have hn := congrArg Complex.normSq hdet
    simp only [map_mul, normSq_phase, normSq_phase_mul_self, Complex.normSq_ofReal, mul_one] at hn
    have hprod := eq_of_mul_self_eq_of_pos _ _ (mul_pos hb₁ hb₂) (mul_pos hb₁' hb₂') (by linear_combination hn)
    rw [← hb₂eq] at hprod
    exact mul_right_cancel₀ hb₂.ne' hprod
  have hψeq : (p 0 0).re = (q 0 0).re := by
    rw [← hb₁eq, ← hb₂eq] at hdet
    have hne : (((p 1 0).re * (p 1 0).im : ℝ) : ℂ) ≠ 0 := by
      first
        | exact_mod_cast (mul_pos hb₁ hb₂).ne'
        | exact Complex.ofReal_ne_zero.2 (mul_pos hb₁ hb₂).ne'
    have hEE := mul_left_cancel₀ hne hdet
    have hre := congrArg Complex.re hEE
    have him := congrArg Complex.im hEE
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im] at hre him
    have hc2 : Real.cos (2 * (p 0 0).re) = Real.cos (2 * (q 0 0).re) := by
      rw [Real.cos_two_mul, Real.cos_two_mul]
      linear_combination hre + hψ - hψ'
    have hs2 : Real.sin (2 * (p 0 0).re) = Real.sin (2 * (q 0 0).re) := by
      rw [Real.sin_two_mul, Real.sin_two_mul]
      linear_combination him
    have h2 : 2 * (p 0 0).re = 2 * (q 0 0).re :=
      angle_eq_of_cos_eq_of_sin_eq (by linarith) (by linarith) (by linarith) (by linarith) hc2 hs2
    linarith
  have hξ₁eq : (p 0 1).re = (q 0 1).re := by
    rw [← hb₂eq, ← hψeq, ← hηeq] at e11re e11im
    obtain ⟨hc, hs⟩ := parts_eq_of_mul_eq ((p 1 0).im * Real.cos (p 0 0).im) (Real.cos (p 0 0).re) (Real.sin (p 0
        0).re) (Real.cos (p 0 1).re) (Real.sin (p 0 1).re) (Real.cos (q 0 1).re) (Real.sin (q 0 1).re) (mul_pos hb₂
        hcη).ne' hψ (by linear_combination e11re) (by linear_combination e11im)
    exact angle_eq_of_cos_eq_of_sin_eq hξ₁₀ hξ₁₁ hξ₁₀' hξ₁₁' hc hs
  have hξ₂eq : (p 0 1).im = (q 0 1).im := by
    rw [← hb₂eq, ← hψeq, ← hηeq] at e10re e10im
    obtain ⟨hc, hs⟩ := parts_eq_of_mul_eq (-((p 1 0).im * Real.sin (p 0 0).im)) (Real.cos (p 0 0).re) (Real.sin (p 0
        0).re) (Real.cos (p 0 1).im) (Real.sin (p 0 1).im) (Real.cos (q 0 1).im) (Real.sin (q 0 1).im) (neg_ne_zero.2
        (mul_pos hb₂ hsη).ne') hψ (by linear_combination e10re) (by linear_combination e10im)
    exact angle_eq_of_cos_eq_of_sin_eq hξ₂₀ hξ₂₁ hξ₂₀' hξ₂₁' hc hs
  have hzeq : (p 1 1).re = (q 1 1).re ∧ (p 1 1).im = (q 1 1).im := by
    rw [← hb₁eq, ← hψeq, ← hηeq, ← hξ₁eq, ← hξ₂eq] at e01re e01im
    have hab : 0 < ((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) + (Real.cos (p 0 0).im) *
        (Real.sin (p 0 1).re) * (Real.sin (p 0 0).re)) ^ 2 + ((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) *
        (Real.sin (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re)) ^ 2 := by
      have hsq : ((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) + (Real.cos (p 0 0).im) *
          (Real.sin (p 0 1).re) * (Real.sin (p 0 0).re)) ^ 2 + ((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) *
          (Real.sin (p 0 0).re) - (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re)) ^ 2 =
          Real.cos (p 0 0).im ^ 2 := by
        linear_combination ((Real.cos (p 0 1).re) ^ 2 * (Real.cos (p 0 0).im) ^ 2 + (Real.cos (p 0 0).im) ^ 2 *
            (Real.sin (p 0 1).re) ^ 2) * hψ + ((Real.cos (p 0 1).re) ^ 2 + (Real.sin (p 0 1).re) ^ 2 - 1) * hη + (1 -
            (Real.sin (p 0 0).im) ^ 2) * hξ₁
      rw [hsq]
      exact pow_pos hcη 2
    exact shear_eq_of_mul_eq (p 1 0).re ((Real.cos (p 0 1).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 0).im) -
        (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im) * (Real.sin (p 0 0).re)) ((Real.cos (p 0 1).im) * (Real.sin (p
        0 0).im) * (Real.sin (p 0 0).re) + (Real.cos (p 0 0).re) * (Real.sin (p 0 1).im) * (Real.sin (p 0 0).im))
        ((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) + (Real.cos (p 0 0).im) * (Real.sin (p
        0 1).re) * (Real.sin (p 0 0).re)) ((Real.cos (p 0 1).re) * (Real.cos (p 0 0).im) * (Real.sin (p 0 0).re) -
        (Real.cos (p 0 0).im) * (Real.cos (p 0 0).re) * (Real.sin (p 0 1).re)) (p 1 1).re (p 1 1).im (q 1 1).re (q 1
        1).im hb₁.ne' hab (by linear_combination e01re) (by linear_combination e01im)
  funext i j
  fin_cases i <;> fin_cases j
  · first
      | exact Complex.ext hψeq hηeq
      | (simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]; exact Complex.ext hψeq hηeq)
  · first
      | exact Complex.ext hξ₁eq hξ₂eq
      | (simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]; exact Complex.ext hξ₁eq hξ₂eq)
  · first
      | exact Complex.ext hb₁eq hb₂eq
      | (simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]; exact Complex.ext hb₁eq hb₂eq)
  · first
      | exact Complex.ext hzeq.1 hzeq.2
      | (simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]; exact Complex.ext hzeq.1 hzeq.2)

private theorem abs_det_fderiv_splitChart (p : Fin 2 → Fin 2 → ℂ) (hp : p ∈ splitDom) :
    |(fderiv ℝ splitChart p).det| = splitDensity p := by
  have hg : p ∈ splitGuard := ⟨hp.1, hp.2.1⟩
  obtain ⟨hb₁, hb₂, -, -, hη₀, hη₁, -, -, -, -⟩ := hp
  have hsη : 0 < Real.sin (p 0 0).im := Real.sin_pos_of_pos_of_lt_pi hη₀ (by linarith [Real.pi_pos])
  have hcη : 0 < Real.cos (p 0 0).im := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hη₁⟩
  have hd0 : 0 ≤ 2 * (p 1 0).re ^ 3 * (p 1 0).im ^ 3 * Real.sin (p 0 0).im * Real.cos (p 0 0).im := by positivity
  rw [(splitChart_eventuallyEq_formula p hg).fderiv_eq, det_fderiv_splitFormula p, abs_of_nonneg hd0, splitDensity]

private theorem lambda_eq_splitChart :
    (fun p : Fin 2 → Fin 2 → ℂ => Matrix.of.symm
    (((if h : 0 < (p 1 0).re ∧ 0 < (p 1 0).im then
          twistedSplitElt ((p 1 0).re ^ 2) ((p 1 0).im ^ 2) ((p 1 0).re * p 1 1) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ *
            unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im
        else 1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))) =
      splitChart :=
  rfl

end AutomorphicForm.GL2Twisted

theorem solution :
    Measure.map
      (fun p : Fin 2 → Fin 2 → ℂ => Matrix.of.symm
      (((if h : 0 < (p 1 0).re ∧ 0 < (p 1 0).im then
            twistedSplitElt ((p 1 0).re ^ 2) ((p 1 0).im ^ 2) ((p 1 0).re * p 1 1) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ *
              unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im
          else 1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)))
      ((volume.restrict
        {p : Fin 2 → Fin 2 → ℂ |
          0 < (p 1 0).re ∧ 0 < (p 1 0).im ∧
          0 < (p 0 0).re ∧ (p 0 0).re < Real.pi ∧ 0 < (p 0 0).im ∧ (p 0 0).im < Real.pi / 2 ∧
          0 < (p 0 1).re ∧ (p 0 1).re < 2 * Real.pi ∧ 0 < (p 0 1).im ∧ (p 0 1).im < 2 * Real.pi}).withDensity
        (fun p : Fin 2 → Fin 2 → ℂ =>
          ENNReal.ofReal (2 * (p 1 0).re ^ 3 * (p 1 0).im ^ 3 * Real.sin (p 0 0).im * Real.cos (p 0 0).im))) =
      volume.restrict {m : Fin 2 → Fin 2 → ℂ | m 0 0 * m 1 1 - m 0 1 * m 1 0 ≠ 0} := by
  have h := map_splitChart_eq differentiableAt_splitChart injOn_splitChart abs_det_fderiv_splitChart
  rw [← lambda_eq_splitChart] at h
  exact h

end S_AutomorphicForm_GL2Twisted_map_splitProductChart
end P2MW
export P2MW.S_AutomorphicForm_GL2Twisted_map_splitProductChart (solution)
