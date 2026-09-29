-- Prove2me | solution 1 for AutomorphicForm.gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/949fe3f2-443e-503a-b57d-07e6c2c6254e

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight

set_option autoImplicit false

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight.AutomorphicForm Matrix"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchDir lowerUnipotentGL2 lowerUnipotentGL2_coe splitTorusGL2 archFlowMatrix rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archWeightOneℝ archWeightCharℝ unipotentGL2 unipotentGL2_coe"
namespace IwasawaAux
p2m_open "AutomorphicForm"

theorem splitTorusGL2_coe' (t : ℝ) : (splitTorusGL2 t : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.exp t, 0; 0, Real.exp (-t)] := rfl

theorem splitTorusGL2_mul (s t : ℝ) : splitTorusGL2 s * splitTorusGL2 t = splitTorusGL2 (s + t) := by
  ext i j
  simp only [Units.val_mul, splitTorusGL2_coe']
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add] <;> ring_nf

theorem splitTorusGL2_mul_unipotentGL2 (s t : ℝ) :
    splitTorusGL2 s * unipotentGL2 t = unipotentGL2 (Real.exp (2 * s) * t) * splitTorusGL2 s := by
  ext i j
  simp only [Units.val_mul, splitTorusGL2_coe', unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [show (2 : ℝ) * s = s + s by ring, Real.exp_add, Real.exp_neg]
  field_simp

theorem inv_sqrt_mul_inv_sqrt (t : ℝ) : (Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹ = (1 + t ^ 2)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by positivity)]

noncomputable def kIw (t : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹; t * (Real.sqrt (1 + t ^ 2))⁻¹, (Real.sqrt (1 + t ^ 2))⁻¹]
    (by
      rw [Matrix.det_fin_two_of]
      have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
      have h2 : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt hpos.le
      have : (Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹ - -t * (Real.sqrt (1 + t ^ 2))⁻¹ * (t * (Real.sqrt (1 + t ^ 2))⁻¹)
          = (1 + t ^ 2) * ((Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹) := by ring
      rw [this, inv_sqrt_mul_inv_sqrt, mul_inv_cancel₀ hpos.ne']
      exact one_ne_zero)

theorem kIw_coe (t : ℝ) : (kIw t : Matrix (Fin 2) (Fin 2) ℝ) =
    !![(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹; t * (Real.sqrt (1 + t ^ 2))⁻¹, (Real.sqrt (1 + t ^ 2))⁻¹] := rfl

theorem sqrt_one_add_sq_pos (t : ℝ) : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
theorem sq_sqrt_one_add_sq (t : ℝ) : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)

theorem det_kIw (t : ℝ) : ((kIw t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [kIw_coe, Matrix.det_fin_two_of]
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have : (Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹ - -t * (Real.sqrt (1 + t ^ 2))⁻¹ * (t * (Real.sqrt (1 + t ^ 2))⁻¹)
      = (1 + t ^ 2) * ((Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹) := by ring
  rw [this, inv_sqrt_mul_inv_sqrt, mul_inv_cancel₀ hpos.ne']

theorem kIw_mem (t : ℝ) : kIw t ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨det_kIw t, ?_, ?_⟩
  · rw [det_kIw, norm_one]
  · intro x y
    rw [kIw_coe]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have key : (x * (Real.sqrt (1 + t ^ 2))⁻¹ + y * (t * (Real.sqrt (1 + t ^ 2))⁻¹)) ^ 2 +
        (x * (-t * (Real.sqrt (1 + t ^ 2))⁻¹) + y * (Real.sqrt (1 + t ^ 2))⁻¹) ^ 2 =
        (x ^ 2 + y ^ 2) * ((1 + t ^ 2) * ((Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹)) := by ring
    rw [key, inv_sqrt_mul_inv_sqrt, mul_inv_cancel₀ hpos.ne', mul_one]

theorem archWeightCharℝ_kIw (n : ℤ) (t : ℝ) :
    ((archWeightCharℝ n ⟨kIw t, kIw_mem t⟩ : ℂˣ) : ℂ) =
      ((⟨(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹⟩ : ℂ)) ^ n := by
  show (((zpowGroupHom n).comp archWeightOneℝ ⟨kIw t, kIw_mem t⟩ : ℂˣ) : ℂ) = _
  simp only [MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val]
  congr 1

theorem lowerUnipotentGL2_iwasawa (t : ℝ) :
    lowerUnipotentGL2 t = unipotentGL2 (t / (1 + t ^ 2)) * splitTorusGL2 (-(Real.log (1 + t ^ 2)) / 2) * kIw t := by
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hsq := sq_sqrt_one_add_sq t
  have hs := sqrt_one_add_sq_pos t
  have hexp : Real.exp (-(Real.log (1 + t ^ 2)) / 2) = (Real.sqrt (1 + t ^ 2))⁻¹ := by
    rw [show -(Real.log (1 + t ^ 2)) / 2 = -(Real.log (1 + t ^ 2) / 2) by ring, Real.exp_neg,
      show Real.log (1 + t ^ 2) / 2 = Real.log (Real.sqrt (1 + t ^ 2)) by
        rw [Real.log_sqrt hpos.le], Real.exp_log hs]
  have hexp' : Real.exp (-(-(Real.log (1 + t ^ 2)) / 2)) = Real.sqrt (1 + t ^ 2) := by
    rw [show -(-(Real.log (1 + t ^ 2)) / 2) = Real.log (Real.sqrt (1 + t ^ 2)) by
      rw [Real.log_sqrt hpos.le]; ring, Real.exp_log hs]
  have hii := inv_sqrt_mul_inv_sqrt t
  have hsi : Real.sqrt (1 + t ^ 2) * (Real.sqrt (1 + t ^ 2))⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  ext i j
  simp only [Units.val_mul, lowerUnipotentGL2_coe, unipotentGL2_coe, splitTorusGL2_coe', kIw_coe, hexp, hexp']
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ·
    rw [hii]; field_simp
  ·
    have : (Real.sqrt (1 + t ^ 2))⁻¹ * (t * (Real.sqrt (1 + t ^ 2))⁻¹) = t * ((Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹) := by ring
    rw [this, hii]; field_simp; ring
  ·
    field_simp
  ·
    field_simp

end AutomorphicForm.IwasawaAux

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight.AutomorphicForm P2MW.S_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight.AutomorphicForm.IwasawaAux"

theorem solution
    (F : GL (Fin 2) ℝ → ℂ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (n : ℤ) (lam ν : ℂ) (hν : ν ^ 2 = 1 / 4 - lam)
    (DF : ArchDir → GL (Fin 2) ℝ → ℂ) (DHH DEF : GL (Fin 2) ℝ → ℂ)
    (hD : ∀ (d : ArchDir) (h : GL (Fin 2) ℝ), HasDerivAt (fun t : ℝ => F (h * archFlowMatrix d t)) (DF d h) 0)
    (hDHH : ∀ h : GL (Fin 2) ℝ, HasDerivAt (fun t : ℝ => DF .H (h * archFlowMatrix .H t)) (DHH h) 0)
    (hDEF : ∀ h : GL (Fin 2) ℝ, HasDerivAt (fun t : ℝ => DF .Fm (h * archFlowMatrix .E t)) (DEF h) 0)
    (hΩ : ∀ h : GL (Fin 2) ℝ, -((1 / 4 : ℂ) * DHH h - (1 / 2 : ℂ) * DF .H h + DEF h) = lam * F h)
    (hN : ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
      F (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * (ε * x)) * F h)
    (hK : ∀ (k : GL (Fin 2) ℝ) (hk : k ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
      F (h * k) = ((archWeightCharℝ n ⟨k, hk⟩ : ℂˣ) : ℂ) * F h) :
    let f : ℝ → ℂ := fun y => F (splitTorusGL2 (Real.log y / 2))
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * n : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by
  intro f

  have hflowH : ∀ t : ℝ, archFlowMatrix .H t = splitTorusGL2 t := fun _ => rfl
  have hflowE : ∀ t : ℝ, archFlowMatrix .E t = unipotentGL2 t := fun _ => rfl
  have hflowF : ∀ t : ℝ, archFlowMatrix .Fm t = lowerUnipotentGL2 t := fun _ => rfl
  let a : ℝ → GL (Fin 2) ℝ := fun y => splitTorusGL2 (Real.log y / 2)
  have hf_def : ∀ y, f y = F (a y) := fun _ => rfl

  have haH : ∀ (y s : ℝ), 0 < y → 0 < s → a y * archFlowMatrix .H (Real.log s / 2 - Real.log y / 2) = a s := by
    intro y s hy hs
    rw [hflowH]; show splitTorusGL2 _ * splitTorusGL2 _ = splitTorusGL2 _
    rw [splitTorusGL2_mul]; congr 1; ring
  have hinner : ∀ y : ℝ, 0 < y → HasDerivAt (fun s : ℝ => Real.log s / 2 - Real.log y / 2) (1 / (2 * y)) y := by
    intro y hy
    have h := ((Real.hasDerivAt_log hy.ne').div_const 2).sub_const (Real.log y / 2)
    convert h using 1 <;> first | rfl | field_simp

  let fD : ℝ → ℂ := fun y => (1 / (2 * y) : ℝ) • DF .H (a y)
  have hf1 : ∀ y : ℝ, 0 < y → HasDerivAt f (fD y) y := by
    intro y hy
    have hG : HasDerivAt (fun t : ℝ => F (a y * archFlowMatrix .H t)) (DF .H (a y))
        (Real.log y / 2 - Real.log y / 2) := by rw [sub_self]; exact hD .H (a y)
    have hcomp := hG.scomp y (hinner y hy)
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with s hs
    show f s = F (a y * archFlowMatrix .H (Real.log s / 2 - Real.log y / 2))
    rw [haH y s hy hs]
  have hderiv_f : ∀ y : ℝ, 0 < y → deriv f y = fD y := fun y hy => (hf1 y hy).deriv

  have hG1 : ∀ y : ℝ, 0 < y → HasDerivAt (fun s : ℝ => DF .H (a s)) ((1 / (2 * y) : ℝ) • DHH (a y)) y := by
    intro y hy
    have hG : HasDerivAt (fun t : ℝ => DF .H (a y * archFlowMatrix .H t)) (DHH (a y))
        (Real.log y / 2 - Real.log y / 2) := by rw [sub_self]; exact hDHH (a y)
    have hcomp := hG.scomp y (hinner y hy)
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with s hs
    show DF .H (a s) = DF .H (a y * archFlowMatrix .H (Real.log s / 2 - Real.log y / 2))
    rw [haH y s hy hs]

  let fDD : ℝ → ℂ := fun y => (1 / (2 * y) : ℝ) • ((1 / (2 * y) : ℝ) • DHH (a y)) + (-(1 / (2 * y ^ 2)) : ℝ) • DF .H (a y)
  have hf2 : ∀ y : ℝ, 0 < y → HasDerivAt fD (fDD y) y := by
    intro y hy
    have h1 : HasDerivAt (fun s : ℝ => (1 / (2 * s) : ℝ)) (-(1 / (2 * y ^ 2))) y := by
      have := ((hasDerivAt_id y).const_mul 2).inv (by positivity)
      convert this using 1
      all_goals first | rfl | skip
      · funext s; simp [one_div]
      · simp only [id]
        field_simp
    have := h1.smul (hG1 y hy)
    convert this using 1
    all_goals first | rfl | skip
  have hderiv_fD : ∀ y : ℝ, 0 < y → HasDerivAt (deriv f) (fDD y) y := by
    intro y hy
    refine (hf2 y hy).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with s hs
    exact hderiv_f s hs
  refine ⟨fun y hy => (hf1 y hy).differentiableAt.differentiableWithinAt,
    fun y hy => (hderiv_fD y hy).differentiableAt.differentiableWithinAt, ?_⟩
  intro y hy
  rw [(hderiv_fD y hy).deriv]

  have hNF : ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
      DF .Fm (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * (ε * x)) * DF .Fm h := by
    intro x h
    have h1 := hD .Fm (unipotentGL2 x * h)
    have h2 : HasDerivAt (fun t : ℝ => F (unipotentGL2 x * h * archFlowMatrix .Fm t))
        (Complex.exp (2 * Real.pi * Complex.I * (ε * x)) * DF .Fm h) 0 := by
      have := (hD .Fm h).const_mul (Complex.exp (2 * Real.pi * Complex.I * (ε * x)))
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      show F (unipotentGL2 x * h * archFlowMatrix .Fm t) = _
      rw [mul_assoc, hN]
    exact h1.unique h2

  have hay_n : ∀ t : ℝ, a y * unipotentGL2 t = unipotentGL2 (y * t) * a y := by
    intro t
    show splitTorusGL2 _ * unipotentGL2 t = unipotentGL2 (y * t) * splitTorusGL2 _
    rw [splitTorusGL2_mul_unipotentGL2]
    have : Real.exp (2 * (Real.log y / 2)) * t = y * t := by
      rw [show 2 * (Real.log y / 2) = Real.log y by ring, Real.exp_log hy]
    rw [this]
  have hDEF_val : DEF (a y) = (2 * Real.pi * Complex.I * (ε * y)) * DF .Fm (a y) := by
    have h1 := hDEF (a y)
    have h2 : HasDerivAt (fun t : ℝ => DF .Fm (a y * archFlowMatrix .E t))
        ((2 * Real.pi * Complex.I * (ε * y)) * DF .Fm (a y)) 0 := by
      have hfun : (fun t : ℝ => DF .Fm (a y * archFlowMatrix .E t)) =
          fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (ε * (y * t))) * DF .Fm (a y) := by
        funext t; rw [hflowE, hay_n, hNF]; push_cast; ring_nf
      rw [hfun]
      have hexp : HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (ε * (y * t))))
          (Complex.exp (2 * Real.pi * Complex.I * (ε * (y * 0))) * (2 * Real.pi * Complex.I * (ε * y))) 0 := by
        have hlin : HasDerivAt (fun t : ℝ => (2 * Real.pi * Complex.I * (ε * (y * t)) : ℂ))
            (2 * Real.pi * Complex.I * (ε * y)) 0 := by
          have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (2 * Real.pi * Complex.I * (ε * y))
          convert this using 1
          all_goals first | rfl | skip
          · funext t; simp only [id]; push_cast; ring
          · simp
        exact hlin.cexp
      have := hexp.mul_const (DF .Fm (a y))
      convert this using 1
      all_goals first | rfl | skip
      simp
    exact h1.unique h2

  have hDF_val : DF .Fm (a y) = (2 * Real.pi * Complex.I * (ε * y) - Complex.I * n) * f y := by
    have h1 := hD .Fm (a y)

    have hfun : (fun t : ℝ => F (a y * archFlowMatrix .Fm t)) = fun t : ℝ =>
        Complex.exp (2 * Real.pi * Complex.I * (ε * (y * (t / (1 + t ^ 2))))) *
          (((⟨(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹⟩ : ℂ)) ^ n *
            f (y / (1 + t ^ 2))) := by
      funext t
      have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
      have htor : a y * splitTorusGL2 (-(Real.log (1 + t ^ 2)) / 2) = a (y / (1 + t ^ 2)) := by
        show splitTorusGL2 _ * splitTorusGL2 _ = splitTorusGL2 _
        rw [splitTorusGL2_mul]; congr 1
        rw [Real.log_div hy.ne' hpos.ne']; ring
      rw [hflowF, lowerUnipotentGL2_iwasawa, ← mul_assoc, ← mul_assoc, hay_n, mul_assoc (unipotentGL2 _),
        mul_assoc (unipotentGL2 _), hN, hK (kIw t) (kIw_mem t), archWeightCharℝ_kIw, htor, hf_def]
      push_cast; ring_nf

    have hx : HasDerivAt (fun t : ℝ => t / (1 + t ^ 2)) 1 0 := by
      have hnum := hasDerivAt_id (0 : ℝ)
      have hden : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (0 : ℝ) 0 := by
        simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)
      have := hnum.div hden (by norm_num)
      convert this using 1 <;> first | rfl | simp
    have hE1 : HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (ε * (y * (t / (1 + t ^ 2))))))
        (2 * Real.pi * Complex.I * (ε * y)) 0 := by
      have hlin : HasDerivAt (fun t : ℝ => (2 * Real.pi * Complex.I * (ε * (y * (t / (1 + t ^ 2)))) : ℂ))
          (2 * Real.pi * Complex.I * (ε * y)) 0 := by
        have := (hx.ofReal_comp).const_mul (2 * Real.pi * Complex.I * (ε * y))
        convert this using 1
        all_goals first | rfl | skip
        · funext t; push_cast; ring
        · simp
      have := hlin.cexp
      convert this using 1
      all_goals first | rfl | skip
      simp
    have hbase : HasDerivAt (fun t : ℝ => ((⟨(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹⟩ : ℂ)))
        (-Complex.I) 0 := by

      have hc : HasDerivAt (fun t : ℝ => (Real.sqrt (1 + t ^ 2))⁻¹) 0 0 := by
        have hden : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (0 : ℝ) 0 := by
          simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)
        have hs := hden.sqrt (by norm_num)
        have hi := hs.inv (by norm_num)
        convert hi using 1 <;> first | rfl | simp
      have hc' : HasDerivAt (fun t : ℝ => ((Real.sqrt (1 + t ^ 2))⁻¹ : ℂ)) 0 0 := by
        simpa using hc.ofReal_comp
      have hl : HasDerivAt (fun t : ℝ => (1 - (t : ℂ) * Complex.I)) (-Complex.I) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).const_sub 1
        convert this using 1 <;> first | rfl | simp
      have hprod := hc'.mul hl
      have hfeq : (fun t : ℝ => ((⟨(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹⟩ : ℂ))) =
          fun t : ℝ => ((Real.sqrt (1 + t ^ 2))⁻¹ : ℂ) * (1 - (t : ℂ) * Complex.I) := by
        funext t
        apply Complex.ext <;> simp <;> ring
      rw [hfeq]
      convert hprod using 1
      all_goals first | rfl | skip
      simp
    have hpow : HasDerivAt (fun t : ℝ => ((⟨(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹⟩ : ℂ)) ^ n)
        (-(Complex.I * n)) 0 := by
      have h0 : ((⟨(Real.sqrt (1 + (0 : ℝ) ^ 2))⁻¹, -(0 : ℝ) * (Real.sqrt (1 + (0 : ℝ) ^ 2))⁻¹⟩ : ℂ)) = 1 := by
        apply Complex.ext <;> simp
      have hz := (hasDerivAt_zpow n (1 : ℂ) (Or.inl one_ne_zero))
      rw [← h0] at hz
      have := hz.comp (0 : ℝ) hbase
      convert this using 1
      all_goals first | rfl | skip
      rw [h0]; simp; ring
    have hfin : HasDerivAt (fun t : ℝ => f (y / (1 + t ^ 2))) 0 0 := by
      have hin : HasDerivAt (fun t : ℝ => y / (1 + t ^ 2)) 0 0 := by
        have hden : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (0 : ℝ) 0 := by
          simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)
        have := (hasDerivAt_const (0 : ℝ) y).div hden (by norm_num)
        convert this using 1 <;> first | rfl | simp
      have hfy : HasDerivAt f (fD y) (y / (1 + (0 : ℝ) ^ 2)) := by simpa using hf1 y hy
      have := hfy.scomp (0 : ℝ) hin
      simpa [Function.comp_def] using this
    have h2c : HasDerivAt (fun t : ℝ =>
        Complex.exp (2 * Real.pi * Complex.I * (ε * (y * (t / (1 + t ^ 2))))) *
          (((⟨(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹⟩ : ℂ)) ^ n *
            f (y / (1 + t ^ 2))))
        ((2 * Real.pi * Complex.I * (ε * y)) * f y + (-(Complex.I * n)) * f y) 0 := by
      have h0 : ((⟨(Real.sqrt (1 + (0 : ℝ) ^ 2))⁻¹, -(0 : ℝ) * (Real.sqrt (1 + (0 : ℝ) ^ 2))⁻¹⟩ : ℂ)) = 1 := by
        apply Complex.ext <;> simp
      convert hE1.mul (hpow.mul hfin) using 1
      all_goals first | rfl | skip
      have h1c : ((⟨1, 0⟩ : ℂ)) = 1 := rfl
      simp [h1c]
      try ring
    rw [← hfun] at h2c
    have h3 := h1.unique h2c
    rw [h3]
    ring

  have hΩy := hΩ (a y)
  have hε2 : (ε : ℂ) ^ 2 = 1 := by
    rcases hε with h | h <;> simp [h]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hlam : lam = 1 / 4 - ν ^ 2 := by rw [hν]; ring
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'

  rw [hDEF_val, hDF_val, hf_def] at hΩy
  have hy2 : (y : ℂ) ^ 2 * fDD y = -(1 / 2 : ℂ) * DF .H (a y) + (1 / 4 : ℂ) * DHH (a y) := by
    simp only [fDD, Complex.real_smul]
    push_cast
    field_simp
    ring
  rw [hy2, hf_def]
  push_cast
  linear_combination (-1 : ℂ) * hΩy
    + ((-4 * (Real.pi : ℂ) ^ 2 * (ε : ℂ) ^ 2 * (y : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * (ε : ℂ) * (y : ℂ) * (n : ℂ)) * F (a y)) * hI2
    + (4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2 * F (a y)) * hε2 - (F (a y)) * hν

end S_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight
end P2MW
export P2MW.S_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight (solution)
