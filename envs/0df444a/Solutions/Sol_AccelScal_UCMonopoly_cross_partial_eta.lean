-- Prove2me | solution 1 for AccelScal.UCMonopoly.cross_partial_eta
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:59:09.621841+00:00
-- url     : https://prove2.me/submissions/bdaa2642-65b6-4be6-afed-a6848be7b986

import Mathlib
import Definitions.Def_AccelScal_UCMonopoly_Setting

set_option autoImplicit false
open Filter Topology

namespace ASUP
open AccelScal.UCMonopoly

theorem hasDeriv_u (T : Tech) {R : ℝ} (hR : 0 < R) :
    HasDerivAt T.u (T.A * (T.β * (R ^ T.β / R))) R := by
  have h := (Real.hasDerivAt_rpow_const (p := T.β) (Or.inl hR.ne')).const_mul T.A
  rw [Real.rpow_sub_one hR.ne'] at h
  exact h

theorem hasDeriv_lam (T : Tech) {R : ℝ} (hR : 0 < R) :
    HasDerivAt T.lam (T.η * (T.γ * (R ^ T.γ / R))) R := by
  have h := (Real.hasDerivAt_rpow_const (p := T.γ) (Or.inl hR.ne')).const_mul T.η
  rw [Real.rpow_sub_one hR.ne'] at h
  exact h

/-- the closed form of the `R`-derivative of `logV` -/
noncomputable def D1 (A β η γ r R : ℝ) : ℝ :=
  ((A * (β * (R ^ β / R))) * (η * R ^ γ) + (A * R ^ β) * (η * (γ * (R ^ γ / R))) - 1) /
      ((A * R ^ β) * (η * R ^ γ) - R)
    - (η * (γ * (R ^ γ / R))) / ((η * R ^ γ) + r)

theorem hasDeriv_logV (T : Tech) (r : ℝ) {R : ℝ} (hR : 0 < R)
    (hD : T.u R * T.lam R - R ≠ 0) (hL : T.lam R + r ≠ 0) :
    deriv (fun x => logV T r x) R = D1 T.A T.β T.η T.γ r R := by
  have hu := hasDeriv_u T hR
  have hl := hasDeriv_lam T hR
  have h1 : HasDerivAt (fun x => T.u x * T.lam x - x)
      (T.A * (T.β * (R ^ T.β / R)) * T.lam R + T.u R * (T.η * (T.γ * (R ^ T.γ / R))) - 1) R :=
    ((hu.mul hl).sub (hasDerivAt_id R))
  have h2 : HasDerivAt (fun x => T.lam x + r) (T.η * (T.γ * (R ^ T.γ / R))) R := hl.add_const r
  have h3 := (h1.log hD).sub (h2.log hL)
  unfold logV
  refine h3.deriv.trans ?_
  rfl

end ASUP

theorem solution (T : AccelScal.UCMonopoly.Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (R : ℝ)
    (hR1 : 1 ≤ R) (hRu : R < T.u R * T.lam R) :
    deriv (fun e => deriv (fun x => AccelScal.UCMonopoly.logV { T with η := e } r x) R) T.η =
        (T.u R * (1 - T.β - T.γ) / (T.lam R * T.u R - R) ^ 2 -
          r * T.γ / (R * (T.lam R + r) ^ 2)) * R ^ T.γ ∧
      (T.γ = 0 →
        0 < (T.u R * (1 - T.β - T.γ) / (T.lam R * T.u R - R) ^ 2 -
          r * T.γ / (R * (T.lam R + r) ^ 2)) * R ^ T.γ) := by
  obtain ⟨hA, hη, hβ0, hβ1, hγ0, hγ1, hβγ, hAη⟩ := hT
  have hR : 0 < R := by linarith
  have hlamR : 0 < T.lam R := by unfold AccelScal.UCMonopoly.Tech.lam; positivity
  have huR : T.u R = T.A * R ^ T.β := rfl
  have hlR : T.lam R = T.η * R ^ T.γ := rfl
  have hDpos : 0 < T.lam R * T.u R - R := by nlinarith
  have hne0 : (fun e : ℝ => (T.A * R ^ T.β) * (e * R ^ T.γ) - R) T.η ≠ 0 := by
    show (T.A * R ^ T.β) * (T.η * R ^ T.γ) - R ≠ 0
    rw [← huR, ← hlR]; nlinarith
  have hcont : ContinuousAt (fun e : ℝ => (T.A * R ^ T.β) * (e * R ^ T.γ) - R) T.η := by fun_prop
  have hev : (fun e => deriv (fun x => AccelScal.UCMonopoly.logV { T with η := e } r x) R) =ᶠ[𝓝 T.η]
      fun e => ASUP.D1 T.A T.β e T.γ r R := by
    filter_upwards [hcont.eventually_ne hne0, lt_mem_nhds hη] with e ha he
    exact ASUP.hasDeriv_logV { T with η := e } r hR ha (by
      show e * R ^ T.γ + r ≠ 0
      have : 0 < e * R ^ T.γ := by positivity
      linarith)
  rw [hev.deriv_eq]
  have hL : T.η * R ^ T.γ + r ≠ 0 := by rw [← hlR]; linarith
  have hDne : T.A * R ^ T.β * (T.η * R ^ T.γ) - R ≠ 0 := by
    rw [← huR, ← hlR]; nlinarith
  have hN : HasDerivAt (fun e : ℝ => (T.A * (T.β * (R ^ T.β / R))) * (e * R ^ T.γ) +
      (T.A * R ^ T.β) * (e * (T.γ * (R ^ T.γ / R))) - 1)
      ((T.A * (T.β * (R ^ T.β / R))) * R ^ T.γ + (T.A * R ^ T.β) * (T.γ * (R ^ T.γ / R))) T.η := by
    have := ((((hasDerivAt_id T.η).mul_const (R ^ T.γ)).const_mul (T.A * (T.β * (R ^ T.β / R)))).add
      (((hasDerivAt_id T.η).mul_const (T.γ * (R ^ T.γ / R))).const_mul (T.A * R ^ T.β))).sub_const 1
    refine this.congr_deriv ?_
    simp
  have hDd : HasDerivAt (fun e : ℝ => (T.A * R ^ T.β) * (e * R ^ T.γ) - R)
      ((T.A * R ^ T.β) * R ^ T.γ) T.η := by
    have := (((hasDerivAt_id T.η).mul_const (R ^ T.γ)).const_mul (T.A * R ^ T.β)).sub_const R
    refine this.congr_deriv ?_
    simp
  have hM : HasDerivAt (fun e : ℝ => e * (T.γ * (R ^ T.γ / R))) (T.γ * (R ^ T.γ / R)) T.η := by
    have := (hasDerivAt_id T.η).mul_const (T.γ * (R ^ T.γ / R))
    refine this.congr_deriv ?_
    simp
  have hLm : HasDerivAt (fun e : ℝ => e * R ^ T.γ + r) (R ^ T.γ) T.η := by
    have := ((hasDerivAt_id T.η).mul_const (R ^ T.γ)).add_const r
    refine this.congr_deriv ?_
    simp
  have h3 := (hN.div hDd hDne).sub (hM.div hLm hL)
  have hd : HasDerivAt (fun e => ASUP.D1 T.A T.β e T.γ r R)
      ((T.u R * (1 - T.β - T.γ) / (T.lam R * T.u R - R) ^ 2 -
          r * T.γ / (R * (T.lam R + r) ^ 2)) * R ^ T.γ) T.η := by
    refine h3.congr_deriv ?_
    rw [hlR, huR] at hDpos ⊢
    have hD3 : T.η * R ^ T.γ * (T.A * R ^ T.β) - R ≠ 0 := by
      intro h; apply hDne; linarith
    have hL2 : T.η * R ^ T.γ + r ≠ 0 := hL
    field_simp
    ring
  refine ⟨hd.deriv, fun hγ => ?_⟩
  have huPos : 0 < T.u R := by rw [huR]; positivity
  rw [hγ, Real.rpow_zero]
  simp only [mul_zero, zero_div, sub_zero, mul_one, sub_zero]
  exact div_pos (mul_pos huPos (by linarith)) (pow_pos hDpos 2)
