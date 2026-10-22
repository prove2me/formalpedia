-- Prove2me | solution 1 for AccelScal.UCMonopoly.cross_partial_A
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:54:11.523795+00:00
-- url     : https://prove2.me/submissions/a92920a4-c032-4d0e-83be-a374e89595a7

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
    deriv (fun a => deriv (fun x => AccelScal.UCMonopoly.logV { T with A := a } r x) R) T.A =
        T.lam R / (T.lam R * T.u R - R) ^ 2 * R ^ T.β * (1 - T.β - T.γ) ∧
      0 < T.lam R / (T.lam R * T.u R - R) ^ 2 * R ^ T.β * (1 - T.β - T.γ) := by
  obtain ⟨hA, hη, hβ0, hβ1, hγ0, hγ1, hβγ, hAη⟩ := hT
  have hR : 0 < R := by linarith
  have hlamR : 0 < T.lam R := by unfold AccelScal.UCMonopoly.Tech.lam; positivity
  have huR : T.u R = T.A * R ^ T.β := rfl
  have hlR : T.lam R = T.η * R ^ T.γ := rfl
  have hDpos : 0 < T.lam R * T.u R - R := by nlinarith
  have hne0 : (fun a : ℝ => a * R ^ T.β * (T.η * R ^ T.γ) - R) T.A ≠ 0 := by
    show T.A * R ^ T.β * (T.η * R ^ T.γ) - R ≠ 0
    rw [← huR, ← hlR]; nlinarith
  have hcont : ContinuousAt (fun a : ℝ => a * R ^ T.β * (T.η * R ^ T.γ) - R) T.A := by fun_prop
  have hev : (fun a => deriv (fun x => AccelScal.UCMonopoly.logV { T with A := a } r x) R) =ᶠ[𝓝 T.A]
      fun a => ASUP.D1 a T.β T.η T.γ r R := by
    filter_upwards [hcont.eventually_ne hne0] with a ha
    exact ASUP.hasDeriv_logV { T with A := a } r hR ha (by
      show T.η * R ^ T.γ + r ≠ 0
      rw [← hlR]; linarith)
  rw [hev.deriv_eq]
  have hxR : (R ^ T.β / R) * R = R ^ T.β := by field_simp
  have hL : T.lam R + r ≠ 0 := by linarith
  have hDne : T.A * R ^ T.β * (T.η * R ^ T.γ) - R ≠ 0 := by
    rw [← huR, ← hlR]; nlinarith
  have hN : HasDerivAt (fun a : ℝ => (a * (T.β * (R ^ T.β / R))) * (T.η * R ^ T.γ) +
      (a * R ^ T.β) * (T.η * (T.γ * (R ^ T.γ / R))) - 1)
      ((T.β * (R ^ T.β / R)) * (T.η * R ^ T.γ) + R ^ T.β * (T.η * (T.γ * (R ^ T.γ / R)))) T.A := by
    have := ((((hasDerivAt_id T.A).mul_const (T.β * (R ^ T.β / R))).mul_const (T.η * R ^ T.γ)).add
      (((hasDerivAt_id T.A).mul_const (R ^ T.β)).mul_const (T.η * (T.γ * (R ^ T.γ / R))))).sub_const 1
    refine this.congr_deriv ?_
    simp
  have hDd : HasDerivAt (fun a : ℝ => (a * R ^ T.β) * (T.η * R ^ T.γ) - R)
      (R ^ T.β * (T.η * R ^ T.γ)) T.A := by
    have := (((hasDerivAt_id T.A).mul_const (R ^ T.β)).mul_const (T.η * R ^ T.γ)).sub_const R
    refine this.congr_deriv ?_
    simp
  have h3 := (hN.div hDd hDne).sub_const ((T.η * (T.γ * (R ^ T.γ / R))) / ((T.η * R ^ T.γ) + r))
  have hd : HasDerivAt (fun a => ASUP.D1 a T.β T.η T.γ r R)
      (T.lam R / (T.lam R * T.u R - R) ^ 2 * R ^ T.β * (1 - T.β - T.γ)) T.A := by
    refine h3.congr_deriv ?_
    rw [hlR, huR] at hDpos ⊢
    have hD2 : T.A * R ^ T.β * (T.η * R ^ T.γ) - R ≠ 0 := hDne
    have hD3 : T.η * R ^ T.γ * (T.A * R ^ T.β) - R ≠ 0 := by
      intro h; apply hD2; linarith
    field_simp
    ring
  refine ⟨hd.deriv, ?_⟩
  have h1bg : 0 < 1 - T.β - T.γ := by linarith
  exact mul_pos (mul_pos (div_pos hlamR (pow_pos hDpos 2)) (Real.rpow_pos_of_pos hR _)) h1bg
