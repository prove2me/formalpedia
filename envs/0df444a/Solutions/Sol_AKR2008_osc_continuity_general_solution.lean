-- Prove2me | solution 1 for AKR2008.osc_continuity_general_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T04:56:50.932743+00:00
-- url     : https://prove2.me/submissions/d7fa851e-6ef8-45ac-895c-ff2a5a7cf607

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

set_option autoImplicit false

namespace AKR2008OscCont

open AKR2008

lemma oscS_hasDerivAt (ω t y : ℝ) :
    HasDerivAt (fun z => oscS ω z t) (-(ω * y * Real.tan (ω * t))) y := by
  show HasDerivAt (fun z => -(ω * z ^ 2 / 2) * Real.tan (ω * t)) _ y
  have h1 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
  have h2 := ((h1.const_mul ω).div_const 2).neg.mul_const (Real.tan (ω * t))
  exact h2.congr_deriv (by ring)

lemma hasDerivAt_x (P : ℝ → ℝ → ℝ) (hd : Differentiable ℝ (Function.uncurry P)) (x t : ℝ) :
    HasDerivAt (fun y => P y t) (fderiv ℝ (Function.uncurry P) (x, t) ((1 : ℝ), (0 : ℝ))) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y, t)) ((1 : ℝ), (0 : ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  exact (hd (x, t)).hasFDerivAt.comp_hasDerivAt x h1

lemma hasDerivAt_t (P : ℝ → ℝ → ℝ) (hd : Differentiable ℝ (Function.uncurry P)) (x t : ℝ) :
    HasDerivAt (fun s => P x s) (fderiv ℝ (Function.uncurry P) (x, t) ((0 : ℝ), (1 : ℝ))) t := by
  have h1 : HasDerivAt (fun s : ℝ => (x, s)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  exact (hd (x, t)).hasFDerivAt.comp_hasDerivAt t h1

lemma key (ω : ℝ) (P : ℝ → ℝ → ℝ) (hd : Differentiable ℝ (Function.uncurry P)) (y t : ℝ)
    (hc : Real.cos (ω * t) ≠ 0) :
    HasDerivAt (fun s => P (y * Real.cos (ω * s)) s * Real.cos (ω * s))
      (Real.cos (ω * t) * (deriv (fun s => P (y * Real.cos (ω * t)) s) t +
        deriv (fun u => P u t * deriv (fun z => oscS ω z t) u) (y * Real.cos (ω * t)))) t := by
  set D := fderiv ℝ (Function.uncurry P) (y * Real.cos (ω * t), t) with hD
  have hcos : HasDerivAt (fun s => Real.cos (ω * s)) (-Real.sin (ω * t) * ω) t := by
    have := ((hasDerivAt_id t).const_mul ω).cos
    simpa using this
  have hcurve : HasDerivAt (fun s => (y * Real.cos (ω * s), s))
      (y * (-Real.sin (ω * t) * ω), (1 : ℝ)) t :=
    (hcos.const_mul y).prodMk (hasDerivAt_id t)
  have hPc : HasDerivAt (Function.uncurry P ∘ fun s => (y * Real.cos (ω * s), s))
      (D (y * (-Real.sin (ω * t) * ω), (1 : ℝ))) t :=
    (hd _).hasFDerivAt.comp_hasDerivAt t hcurve
  have hg := hPc.mul hcos
  have e1 : deriv (fun s => P (y * Real.cos (ω * t)) s) t = D ((0 : ℝ), (1 : ℝ)) :=
    (hasDerivAt_t P hd _ t).deriv
  have e2 : deriv (fun u => P u t * deriv (fun z => oscS ω z t) u) (y * Real.cos (ω * t)) =
      D ((1 : ℝ), (0 : ℝ)) * (-(ω * (y * Real.cos (ω * t)) * Real.tan (ω * t))) +
        P (y * Real.cos (ω * t)) t * (-(ω * Real.tan (ω * t))) := by
    have hfun : (fun u => P u t * deriv (fun z => oscS ω z t) u) =
        fun u => P u t * (-(ω * u * Real.tan (ω * t))) := by
      funext u; rw [(oscS_hasDerivAt ω t u).deriv]
    rw [hfun]
    have hl : HasDerivAt (fun u : ℝ => -(ω * u * Real.tan (ω * t))) (-(ω * Real.tan (ω * t)))
        (y * Real.cos (ω * t)) := by
      have h := (hasDerivAt_mul_const (x := y * Real.cos (ω * t)) (ω * Real.tan (ω * t))).neg
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
      (try simp only [Pi.neg_apply]); ring
    exact ((hasDerivAt_x P hd _ t).mul hl).deriv
  refine hg.congr_deriv ?_
  rw [e1, e2]
  have hlin : D (y * (-Real.sin (ω * t) * ω), (1 : ℝ)) =
      (y * (-Real.sin (ω * t) * ω)) * D ((1 : ℝ), (0 : ℝ)) + D ((0 : ℝ), (1 : ℝ)) := by
    have : ((y * (-Real.sin (ω * t) * ω)), (1 : ℝ)) =
        (y * (-Real.sin (ω * t) * ω)) • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
  simp only [Function.comp_apply, Function.uncurry_apply_pair]
  rw [hlin, Real.tan_eq_sin_div_cos]
  field_simp
  ring

lemma cos_pos_strip (ω : ℝ) (hω : 0 < ω) (t : ℝ) (ht : |t| < Real.pi / (2 * ω)) :
    0 < Real.cos (ω * t) := by
  apply Real.cos_pos_of_mem_Ioo
  rw [abs_lt] at ht
  have h1 : ω * t < ω * (Real.pi / (2 * ω)) := mul_lt_mul_of_pos_left ht.2 hω
  have h2 : ω * (-(Real.pi / (2 * ω))) < ω * t := mul_lt_mul_of_pos_left ht.1 hω
  have h3 : ω * (Real.pi / (2 * ω)) = Real.pi / 2 := by field_simp
  constructor <;> linarith

end AKR2008OscCont

open AKR2008 in
theorem solution (ω : ℝ) (hω : 0 < ω) (P : ℝ → ℝ → ℝ)
    (hP : ContDiff ℝ 1 (Function.uncurry P)) :
    (∀ x t, |t| < Real.pi / (2 * ω) →
      deriv (fun s => P x s) t + deriv (fun y => P y t * deriv (fun z => oscS ω z t) y) x = 0) ↔
    ∃ f : ℝ → ℝ, ∀ x t, |t| < Real.pi / (2 * ω) →
      P x t = f (x / Real.cos (ω * t)) / Real.cos (ω * t) := by
  have hd : Differentiable ℝ (Function.uncurry P) := hP.differentiable one_ne_zero
  have hT : 0 < Real.pi / (2 * ω) := by positivity
  have hmem : ∀ s, s ∈ Set.Ioo (-(Real.pi / (2 * ω))) (Real.pi / (2 * ω)) →
      |s| < Real.pi / (2 * ω) := fun s hs => abs_lt.2 hs
  constructor
  · intro hE
    refine ⟨fun y => P y 0, fun x t ht => ?_⟩
    have hc := AKR2008OscCont.cos_pos_strip ω hω t ht
    have hconst := (isOpen_Ioo (a := -(Real.pi / (2 * ω))) (b := Real.pi / (2 * ω))).is_const_of_deriv_eq_zero
      (f := fun s => P (x / Real.cos (ω * t) * Real.cos (ω * s)) s * Real.cos (ω * s))
      isPreconnected_Ioo
      (fun s hs => (AKR2008OscCont.key ω P hd (x / Real.cos (ω * t)) s
        (AKR2008OscCont.cos_pos_strip ω hω s (hmem s hs)).ne').differentiableAt.differentiableWithinAt)
      (fun s hs => by
        rw [(AKR2008OscCont.key ω P hd (x / Real.cos (ω * t)) s (AKR2008OscCont.cos_pos_strip ω hω s (hmem s hs)).ne').deriv,
          hE _ s (hmem s hs)]
        simp)
      (x := t) (y := 0) (abs_lt.1 ht)
      (by constructor <;> linarith)
    simp only [mul_zero, Real.cos_zero, mul_one, div_mul_cancel₀ x hc.ne'] at hconst
    show P x t = P (x / Real.cos (ω * t)) 0 / Real.cos (ω * t)
    rw [← hconst]
    field_simp
  · rintro ⟨f, hf⟩ x t ht
    have hc := AKR2008OscCont.cos_pos_strip ω hω t ht
    have hk := AKR2008OscCont.key ω P hd (x / Real.cos (ω * t)) t hc.ne'
    have hg0 : HasDerivAt (fun s => P (x / Real.cos (ω * t) * Real.cos (ω * s)) s *
        Real.cos (ω * s)) 0 t := by
      apply (hasDerivAt_const t (f (x / Real.cos (ω * t)))).congr_of_eventuallyEq
      have hopen : Set.Ioo (-(Real.pi / (2 * ω))) (Real.pi / (2 * ω)) ∈ nhds t :=
        Ioo_mem_nhds (abs_lt.1 ht).1 (abs_lt.1 ht).2
      filter_upwards [hopen] with s hs
      have hcs := AKR2008OscCont.cos_pos_strip ω hω s (hmem s hs)
      rw [hf _ s (hmem s hs), mul_div_cancel_right₀ _ hcs.ne', div_mul_cancel₀ _ hcs.ne']
    have h0 := hk.unique hg0
    rw [div_mul_cancel₀ x hc.ne'] at h0
    exact (mul_eq_zero.1 h0).resolve_left hc.ne'
