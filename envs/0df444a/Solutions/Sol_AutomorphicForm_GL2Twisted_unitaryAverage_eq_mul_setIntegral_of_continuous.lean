-- Prove2me | solution 1 for AutomorphicForm.GL2Twisted.unitaryAverage_eq_mul_setIntegral_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3bfb5a98-8dd4-5432-af94-ea47817033d6

import Mathlib
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Twisted_unitaryAverage_eq_mul_setIntegral_of_continuous

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open MeasureTheory TopologicalSpace Topology
open AutomorphicForm.GL2Twisted

noncomputable section

namespace P2mUAvg

theorem continuousOn_matrixInv :
    ContinuousOn (fun A : Matrix (Fin 2) (Fin 2) ℂ => A⁻¹) {A | IsUnit A} := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine ContinuousOn.fun_smul ?_ (Continuous.matrix_adjugate continuous_id).continuousOn
  exact (Continuous.matrix_det continuous_id).continuousOn.inv₀ fun A hA =>
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero

theorem isEmbedding_glVal : IsEmbedding (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) :=
  Units.isEmbedding_val_mk' continuousOn_matrixInv fun u => (Matrix.coe_units_inv u).symm

theorem coe_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
          Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
        Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
          Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))] :=
  rfl

def kk (r : (ℝ × ℝ) × (ℝ × ℝ)) : GL (Fin 2) ℂ := unitaryElt r.1.1 r.1.2 r.2.1 r.2.2

theorem continuous_kk : Continuous kk := by
  rw [isEmbedding_glVal.continuous_iff]
  have h : (Units.val ∘ kk) = fun r : (ℝ × ℝ) × (ℝ × ℝ) =>
        !![Complex.exp (r.1.1 * Complex.I) * (Real.cos r.1.2 * Complex.exp (r.2.1 * Complex.I)),
            Complex.exp (r.1.1 * Complex.I) * (Real.sin r.1.2 * Complex.exp (r.2.2 * Complex.I));
          Complex.exp (r.1.1 * Complex.I) * (-(Real.sin r.1.2 * Complex.exp (-(r.2.2 * Complex.I)))),
            Complex.exp (r.1.1 * Complex.I) * (Real.cos r.1.2 * Complex.exp (-(r.2.1 * Complex.I)))] := by
    funext r
    exact coe_unitaryElt _ _ _ _
  rw [h]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem unitaryElt_add_pi (ψ η ξ₁ ξ₂ : ℝ) :
    unitaryElt (ψ + Real.pi) η ξ₁ ξ₂ = unitaryElt ψ η (ξ₁ + Real.pi) (ξ₂ + Real.pi) := by
  have hpi : Complex.exp (Real.pi * Complex.I) = -1 := by
    rw [Complex.exp_mul_I]; simp
  have hnpi : Complex.exp (-(Real.pi * Complex.I)) = -1 := by
    rw [show -(↑Real.pi * Complex.I) = (-Real.pi : ℝ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    simp [Complex.cos_neg, Complex.sin_neg]
  have e1 : Complex.exp (((ψ + Real.pi : ℝ) : ℂ) * Complex.I) = -Complex.exp (ψ * Complex.I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, hpi, mul_neg_one]
  have e2 : ∀ ξ : ℝ, Complex.exp (((ξ + Real.pi : ℝ) : ℂ) * Complex.I) = -Complex.exp (ξ * Complex.I) := by
    intro ξ; rw [Complex.ofReal_add, add_mul, Complex.exp_add, hpi, mul_neg_one]
  have e3 : ∀ ξ : ℝ, Complex.exp (-(((ξ + Real.pi : ℝ) : ℂ) * Complex.I)) = -Complex.exp (-(ξ * Complex.I)) := by
    intro ξ; rw [Complex.ofReal_add, add_mul, neg_add, Complex.exp_add, hnpi, mul_neg_one]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [coe_unitaryElt, coe_unitaryElt, e1, e2, e2, e3, e3]
  fin_cases i <;> fin_cases j <;> simp

theorem exp_add_two_pi_mul_I (ξ : ℝ) :
    Complex.exp (((ξ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) = Complex.exp (ξ * Complex.I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]
  have : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 2 * Real.pi * Complex.I by push_cast; ring]
    exact Complex.exp_two_pi_mul_I
  rw [this, mul_one]

theorem exp_neg_add_two_pi_mul_I (ξ : ℝ) :
    Complex.exp (-(((ξ + 2 * Real.pi : ℝ) : ℂ) * Complex.I)) = Complex.exp (-(ξ * Complex.I)) := by
  rw [Complex.ofReal_add, add_mul, neg_add, Complex.exp_add]
  have : Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I)) = 1 := by
    rw [show (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I)) = ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-1)
  rw [this, mul_one]

theorem unitaryElt_periodic_ξ₁ (ψ η ξ₁ ξ₂ : ℝ) :
    unitaryElt ψ η (ξ₁ + 2 * Real.pi) ξ₂ = unitaryElt ψ η ξ₁ ξ₂ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [coe_unitaryElt, coe_unitaryElt, exp_add_two_pi_mul_I, exp_neg_add_two_pi_mul_I]

theorem unitaryElt_periodic_ξ₂ (ψ η ξ₁ ξ₂ : ℝ) :
    unitaryElt ψ η ξ₁ (ξ₂ + 2 * Real.pi) = unitaryElt ψ η ξ₁ ξ₂ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [coe_unitaryElt, coe_unitaryElt, exp_add_two_pi_mul_I, exp_neg_add_two_pi_mul_I]

def hh (F : GL (Fin 2) ℂ → ℂ) (r : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  ((Real.sin r.1.2 : ℂ) * (Real.cos r.1.2 : ℂ)) * F (kk r)

theorem continuous_hh {F : GL (Fin 2) ℂ → ℂ} (hF : Continuous F) : Continuous (hh F) := by
  unfold hh
  refine Continuous.mul ?_ (hF.comp continuous_kk)
  exact (Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_snd.comp continuous_fst))).mul
    (Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_snd.comp continuous_fst)))

def BOX (L : ℝ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Set.Ioo 0 L ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ (Set.Ioo 0 (2 * Real.pi) ×ˢ Set.Ioo 0 (2 * Real.pi))

theorem setIntegral_Ioo_eq_intervalIntegral {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℂ) :
    ∫ x in Set.Ioo a b, g x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

theorem integrableOn_Ioo_prod {g : ℝ × ℝ → ℂ} (hg : Continuous g) (a b c d : ℝ) :
    IntegrableOn g (Set.Ioo a b ×ˢ Set.Ioo c d) volume :=
  (hg.continuousOn.integrableOn_compact ((isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := c) (b := d)))).mono_set
    (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)

theorem setIntegral_Ioo_prod {g : ℝ × ℝ → ℂ} (hg : Continuous g) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ z in Set.Ioo a b ×ˢ Set.Ioo c d, g z = ∫ x in a..b, ∫ y in c..d, g (x, y) := by
  have hint : Integrable g ((volume.restrict (Set.Ioo a b)).prod (volume.restrict (Set.Ioo c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact integrableOn_Ioo_prod hg a b c d
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod g hint,
    setIntegral_Ioo_eq_intervalIntegral hab]
  refine intervalIntegral.integral_congr fun x _ => ?_
  exact setIntegral_Ioo_eq_intervalIntegral hcd _

theorem setIntegral_BOX_eq (h : (ℝ × ℝ) × (ℝ × ℝ) → ℂ) (hc : Continuous h) (L : ℝ) (hL : 0 ≤ L) :
    ∫ r in BOX L, h r =
      ∫ ψ in (0 : ℝ)..L, ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        h ((ψ, η), (ξ₁, ξ₂)) := by
  have hπ2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity

  have hK : IsCompact ((Set.Icc 0 L ×ˢ Set.Icc 0 (Real.pi / 2)) ×ˢ (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) :
      Set ((ℝ × ℝ) × (ℝ × ℝ))) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)
  have hint0 : IntegrableOn h (BOX L) volume :=
    (hc.continuousOn.integrableOn_compact hK).mono_set (Set.prod_mono
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self))
  have hint : Integrable h ((volume.restrict (Set.Ioo 0 L ×ˢ Set.Ioo 0 (Real.pi / 2))).prod
      (volume.restrict (Set.Ioo 0 (2 * Real.pi) ×ˢ Set.Ioo 0 (2 * Real.pi)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hint0

  have step1 : ∫ r in BOX L, h r =
      ∫ pe in Set.Ioo 0 L ×ˢ Set.Ioo 0 (Real.pi / 2),
        ∫ xe in Set.Ioo 0 (2 * Real.pi) ×ˢ Set.Ioo 0 (2 * Real.pi), h (pe, xe) := by
    unfold BOX
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod h hint]

  have step2 : ∀ pe : ℝ × ℝ, ∫ xe in Set.Ioo 0 (2 * Real.pi) ×ˢ Set.Ioo 0 (2 * Real.pi), h (pe, xe) =
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), h (pe, (ξ₁, ξ₂)) := fun pe =>
    setIntegral_Ioo_prod (hc.comp (Continuous.prodMk continuous_const continuous_id)) h2π h2π

  have hKc : Continuous fun pe : ℝ × ℝ =>
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), h (pe, (ξ₁, ξ₂)) := by
    have h3 : Continuous fun q : (ℝ × ℝ) × ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), h (q.1, (q.2, ξ₂)) := by
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
      exact hc.comp (by fun_prop)
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
    exact h3.comp (by fun_prop)
  rw [step1]
  simp_rw [step2]
  exact setIntegral_Ioo_prod hKc hL hπ2

def n₁ (F : GL (Fin 2) ℂ → ℂ) (ψ : ℝ) : ℂ :=
  ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
    hh F ((ψ, η), (ξ₁, ξ₂))

theorem continuous_n₁ {F : GL (Fin 2) ℂ → ℂ} (hF : Continuous F) : Continuous (n₁ F) := by
  have hc := continuous_hh hF
  have h3 : Continuous fun q : (ℝ × ℝ) × ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), hh F (q.1, (q.2, ξ₂)) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
    exact hc.comp (by fun_prop)
  have h2 : Continuous fun pe : ℝ × ℝ =>
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), hh F (pe, (ξ₁, ξ₂)) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
    exact h3.comp (by fun_prop)
  unfold n₁
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  exact h2.comp (by fun_prop)

theorem n₁_add_pi {F : GL (Fin 2) ℂ → ℂ} (ψ : ℝ) : n₁ F (ψ + Real.pi) = n₁ F ψ := by
  unfold n₁
  refine intervalIntegral.integral_congr fun η _ => ?_

  have hξ₁ : ∀ ξ₂ : ℝ, (∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), hh F ((ψ + Real.pi, η), (ξ₁, ξ₂))) =
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), hh F ((ψ, η), (ξ₁, ξ₂ + Real.pi)) := by
    intro ξ₂
    have hper : Function.Periodic (fun ξ₁ => hh F ((ψ, η), (ξ₁, ξ₂ + Real.pi))) (2 * Real.pi) := fun ξ₁ => by
      simp only [hh, kk, unitaryElt_periodic_ξ₁]
    have h1 : (fun ξ₁ => hh F ((ψ + Real.pi, η), (ξ₁, ξ₂))) = fun ξ₁ => hh F ((ψ, η), (ξ₁ + Real.pi, ξ₂ + Real.pi)) := by
      funext ξ₁; simp only [hh, kk, unitaryElt_add_pi]
    rw [h1, intervalIntegral.integral_comp_add_right (fun ξ₁ => hh F ((ψ, η), (ξ₁, ξ₂ + Real.pi))) Real.pi,
      zero_add]
    have := hper.intervalIntegral_add_eq Real.pi 0
    rw [zero_add, show Real.pi + 2 * Real.pi = 2 * Real.pi + Real.pi by ring] at this
    exact this

  have hswap : (∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), hh F ((ψ + Real.pi, η), (ξ₁, ξ₂))) =
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), hh F ((ψ, η), (ξ₁ + Real.pi, ξ₂ + Real.pi)) := by
    refine intervalIntegral.integral_congr fun ξ₁ _ => ?_
    refine intervalIntegral.integral_congr fun ξ₂ _ => ?_
    simp only [hh, kk, unitaryElt_add_pi]
  rw [hswap]
  have hξ₂ : ∀ ξ₁ : ℝ, (∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), hh F ((ψ, η), (ξ₁ + Real.pi, ξ₂ + Real.pi))) =
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), hh F ((ψ, η), (ξ₁ + Real.pi, ξ₂)) := by
    intro ξ₁
    have hper : Function.Periodic (fun ξ₂ => hh F ((ψ, η), (ξ₁ + Real.pi, ξ₂))) (2 * Real.pi) := fun ξ₂ => by
      simp only [hh, kk, unitaryElt_periodic_ξ₂]
    rw [intervalIntegral.integral_comp_add_right (fun ξ₂ => hh F ((ψ, η), (ξ₁ + Real.pi, ξ₂))) Real.pi, zero_add]
    have := hper.intervalIntegral_add_eq Real.pi 0
    rw [zero_add, show Real.pi + 2 * Real.pi = 2 * Real.pi + Real.pi by ring] at this
    exact this
  simp_rw [hξ₂]

  have hper1 : Function.Periodic (fun ξ₁ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), hh F ((ψ, η), (ξ₁, ξ₂))) (2 * Real.pi) :=
    fun ξ₁ => by simp only [hh, kk, unitaryElt_periodic_ξ₁]
  rw [intervalIntegral.integral_comp_add_right (fun ξ₁ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), hh F ((ψ, η), (ξ₁, ξ₂)))
    Real.pi, zero_add]
  have := hper1.intervalIntegral_add_eq Real.pi 0
  rw [zero_add, show Real.pi + 2 * Real.pi = 2 * Real.pi + Real.pi by ring] at this
  exact this

theorem integral_zero_two_pi_eq_two_mul (G : ℝ → ℂ) (hG : ∀ θ, G (θ + Real.pi) = G θ)
    (hint : IntegrableOn G (Set.Ioc (0 : ℝ) (2 * Real.pi))) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), G θ = 2 * ∫ θ in (0 : ℝ)..Real.pi, G θ := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hπ2 : Real.pi ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  have h1 : IntervalIntegrable G volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).2 hint
  have hA : IntervalIntegrable G volume 0 Real.pi :=
    h1.mono_set (by rw [Set.uIcc_of_le hπ, Set.uIcc_of_le h2π]; exact Set.Icc_subset_Icc le_rfl hπ2)
  have hB : IntervalIntegrable G volume Real.pi (2 * Real.pi) :=
    h1.mono_set (by rw [Set.uIcc_of_le hπ2, Set.uIcc_of_le h2π]; exact Set.Icc_subset_Icc hπ le_rfl)
  have hshift : ∫ θ in Real.pi..(2 * Real.pi), G θ = ∫ θ in (0 : ℝ)..Real.pi, G θ := by
    have h := intervalIntegral.integral_comp_add_right (a := 0) (b := Real.pi) G Real.pi
    simp only [hG, zero_add] at h
    rw [h, two_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals hA hB, hshift, two_mul]

theorem main (F : GL (Fin 2) ℂ → ℂ) (hF : Continuous F) :
    unitaryAverage F = (1 / (2 * Real.pi ^ 3) : ℂ) *
      ∫ r in (Set.Ioo 0 Real.pi ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ (Set.Ioo 0 (2 * Real.pi) ×ˢ Set.Ioo 0 (2 * Real.pi)),
        (Real.sin r.1.2 * Real.cos r.1.2 : ℂ) * F (unitaryElt r.1.1 r.1.2 r.2.1 r.2.2) := by
  have hbox : (∫ r in (Set.Ioo 0 Real.pi ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ (Set.Ioo 0 (2 * Real.pi) ×ˢ Set.Ioo 0 (2 * Real.pi)),
        (Real.sin r.1.2 * Real.cos r.1.2 : ℂ) * F (unitaryElt r.1.1 r.1.2 r.2.1 r.2.2)) =
      ∫ ψ in (0 : ℝ)..Real.pi, n₁ F ψ := by
    exact setIntegral_BOX_eq (hh F) (continuous_hh hF) Real.pi Real.pi_pos.le
  have hbig : unitaryAverage F = (1 / (4 * Real.pi ^ 3) : ℂ) * ∫ ψ in (0 : ℝ)..(2 * Real.pi), n₁ F ψ := rfl
  have hdouble : ∫ ψ in (0 : ℝ)..(2 * Real.pi), n₁ F ψ = 2 * ∫ ψ in (0 : ℝ)..Real.pi, n₁ F ψ :=
    integral_zero_two_pi_eq_two_mul (n₁ F) n₁_add_pi
      (((continuous_n₁ hF).continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self)
  rw [hbig, hdouble, hbox]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring

end P2mUAvg

end

open AutomorphicForm.GL2Twisted in
theorem solution (F : GL (Fin 2) ℂ → ℂ) (hF : Continuous F) :
    unitaryAverage F = (1 / (2 * Real.pi ^ 3) : ℂ) *
      ∫ r in (Set.Ioo 0 Real.pi ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ (Set.Ioo 0 (2 * Real.pi) ×ˢ Set.Ioo 0 (2 * Real.pi)),
        (Real.sin r.1.2 * Real.cos r.1.2 : ℂ) * F (unitaryElt r.1.1 r.1.2 r.2.1 r.2.2) :=
  P2mUAvg.main F hF

end S_AutomorphicForm_GL2Twisted_unitaryAverage_eq_mul_setIntegral_of_continuous
end P2MW
export P2MW.S_AutomorphicForm_GL2Twisted_unitaryAverage_eq_mul_setIntegral_of_continuous (solution)
