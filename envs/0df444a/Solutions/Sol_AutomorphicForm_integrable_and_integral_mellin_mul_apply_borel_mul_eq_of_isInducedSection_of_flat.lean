-- Prove2me | solution 1 for AutomorphicForm.integrable_and_integral_mellin_mul_apply_borel_mul_eq_of_isInducedSection_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9a7e2670-20c8-5918-b0b5-e85f411c83ef

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar

import Theorems.Thm_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrable_and_integral_mellin_mul_apply_borel_mul_eq_of_isInducedSection_of_flat

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm
open IsDedekindDomain
open scoped NNReal

namespace D4C9

theorem ofReal_cpow_eq_exp (x : ℝ) (hx : 0 < x) (w : ℂ) :
    ((x : ℝ) : ℂ) ^ w = Complex.exp (w * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), ← Complex.ofReal_log hx.le, mul_comm]

theorem cpow_mul_cpow_neg_eq (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₂ : 0 < r₂) (s : ℂ) :
    ((r₁ : ℝ) : ℂ) ^ (s + 1 / 2) * ((r₂ : ℝ) : ℂ) ^ (-(s + 1 / 2)) =
      ((Real.sqrt (r₁ / r₂) : ℝ) : ℂ) * Complex.exp (s * ((Real.log (r₁ / r₂) : ℝ) : ℂ)) := by
  rw [ofReal_cpow_eq_exp _ h₁, ofReal_cpow_eq_exp _ h₂, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (div_pos h₁ h₂),
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, Real.log_div h₁.ne' h₂.ne']
  congr 1
  push_cast
  ring

end D4C9

theorem solution
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ s))
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        φ s (k : AdelicGL2 (𝓞 K) K) = φ 0 (k : AdelicGL2 (𝓞 K) K))
      (h : ℝ → ℂ) (_hh : ContDiff ℝ (⊤ : ℕ∞) h) (_hhc : HasCompactSupport h)
      (σ' : ℝ) (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K)
      (k : AdelicGL2 (𝓞 K) K) (_hk : k ∈ adelicMaximalCompact K),
    let c : ℂ → ℂ := fun s => ∫ u : ℝ, h u * Complex.exp (s * (u : ℂ))
    let r : ℝ := ((αm (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ) /
      ((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ)
    Integrable (fun t : ℝ =>
      c ((σ' : ℂ) + (t : ℂ) * Complex.I) * φ ((σ' : ℂ) + (t : ℂ) * Complex.I) (b * k)) ∧
    ∫ t : ℝ, c ((σ' : ℂ) + (t : ℂ) * Complex.I) * φ ((σ' : ℂ) + (t : ℂ) * Complex.I) (b * k) =
      (((2 * Real.pi) : ℝ) : ℂ) *
        (((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
          ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
          ((Real.sqrt r : ℝ) : ℂ) * h (-Real.log r) * φ 0 k) := by
  intro αm hαm μ ν φ hφ hφflat h hh hhc σ' b hb k hk c r
  have hflat : ∀ s, φ s k = φ 0 k := fun s => hφflat s ⟨k, hk⟩
  obtain ⟨hMdiff, hMdec, hMinv⟩ :=
    MellinPaleyWiener.differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport h hh hhc
  have hMcont : Continuous c := hMdiff.continuous
  set y₁ := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K)) with hy₁
  set y₂ := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K)) with hy₂
  set r₁ : ℝ := ((αm y₁ : ℝˣ) : ℝ) with hr₁def
  set r₂ : ℝ := ((αm y₂ : ℝˣ) : ℝ) with hr₂def
  have hr₁ : 0 < r₁ := hαm y₁
  have hr₂ : 0 < r₂ := hαm y₂
  have hr : r = r₁ / r₂ := rfl
  set L : ℝ := Real.log r with hLdef
  set c₀ : ℂ := ((μ y₁ : ℂˣ) : ℂ) * ((ν y₂ : ℂˣ) : ℂ) * φ 0 k with hc₀def

  have hpt : ∀ s : ℂ, c s * φ s (b * k) =
      (c₀ * ((Real.sqrt r : ℝ) : ℂ)) * (c s * Complex.exp (s * (L : ℂ))) := by
    intro s
    have e := D4C9.cpow_mul_cpow_neg_eq r₁ r₂ hr₁ hr₂ s
    rw [← hr, ← hLdef] at e
    rw [hφ s b hb k, hflat s, etaFst_apply, etaSnd_apply, Units.val_mul, Units.val_mul,
      cpowChar_apply_val, cpowChar_apply_val]
    linear_combination (c s * ((μ y₁ : ℂˣ) : ℂ) * ((ν y₂ : ℂˣ) : ℂ) * φ 0 k) * e

  have hI : ∫ t : ℝ, c ((σ' : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (L : ℂ)) =
      (((2 * Real.pi) : ℝ) : ℂ) * h (-L) := by
    have h' := hMinv σ' (-L)
    have e : (fun t : ℝ => (∫ v : ℝ, h v * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (v : ℂ))) *
        Complex.exp (-(((σ' : ℂ) + (t : ℂ) * Complex.I) * ((-L : ℝ) : ℂ)))) =
        fun t : ℝ => c ((σ' : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (L : ℂ)) := by
      funext t
      have : Complex.exp (-(((σ' : ℂ) + (t : ℂ) * Complex.I) * ((-L : ℝ) : ℂ))) =
          Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (L : ℂ)) := by
        congr 1; push_cast; ring
      rw [this]
    rw [e] at h'
    rw [h']
    have hπ : ((2 : ℂ) * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hπ, one_mul]

  have hs : Continuous fun t : ℝ => (σ' : ℂ) + (t : ℂ) * Complex.I := by fun_prop
  have hcont : Continuous fun t : ℝ => c ((σ' : ℂ) + (t : ℂ) * Complex.I) *
      Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (L : ℂ)) :=
    (hMcont.comp hs).mul (Complex.continuous_exp.comp (hs.mul continuous_const))
  obtain ⟨C, hC0, hC⟩ := hMdec 2 |σ'|
  have hint0 : Integrable (fun t : ℝ => c ((σ' : ℂ) + (t : ℂ) * Complex.I) *
      Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (L : ℂ))) := by
    refine ((integrable_one_add_norm (r := (2 : ℝ)) (by simp)).const_mul (C * Real.exp (σ' * L))).mono'
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_exp]
    have hre : (((σ' : ℂ) + (t : ℂ) * Complex.I) * (L : ℂ)).re = σ' * L := by
      simp [Complex.mul_re]
    rw [hre]
    have h1 : (1 + |t|) ^ 2 * ‖c ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := hC σ' le_rfl t
    have hpos : 0 < 1 + |t| := by positivity
    rw [Real.norm_eq_abs, Real.rpow_neg hpos.le, Real.rpow_two, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity)]
    calc ‖c ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ * Real.exp (σ' * L) * (1 + |t|) ^ 2
        = ((1 + |t|) ^ 2 * ‖c ((σ' : ℂ) + (t : ℂ) * Complex.I)‖) * Real.exp (σ' * L) := by ring
      _ ≤ C * Real.exp (σ' * L) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hfun : (fun t : ℝ => c ((σ' : ℂ) + (t : ℂ) * Complex.I) *
        φ ((σ' : ℂ) + (t : ℂ) * Complex.I) (b * k)) =
      fun t : ℝ => (c₀ * ((Real.sqrt r : ℝ) : ℂ)) * (c ((σ' : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (L : ℂ))) :=
    funext fun t => hpt _
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hint0.const_mul _
  · rw [hfun, integral_const_mul, hI, hc₀def]
    ring

end S_AutomorphicForm_integrable_and_integral_mellin_mul_apply_borel_mul_eq_of_isInducedSection_of_flat
end P2MW
export P2MW.S_AutomorphicForm_integrable_and_integral_mellin_mul_apply_borel_mul_eq_of_isInducedSection_of_flat (solution)
