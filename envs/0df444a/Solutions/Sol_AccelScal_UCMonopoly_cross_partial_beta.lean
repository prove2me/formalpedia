-- Prove2me | solution 1 for AccelScal.UCMonopoly.cross_partial_beta
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:59:10.558868+00:00
-- url     : https://prove2.me/submissions/c89c0056-76d3-43c8-b873-c1e9afd761c3

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
    deriv (fun b => deriv (fun x => AccelScal.UCMonopoly.logV { T with β := b } r x) R) T.β =
        T.lam R / (T.lam R * T.u R - R) ^ 2 * (T.A * R ^ T.β * Real.log R) * (1 - T.β - T.γ) +
          T.u R * T.lam R / R * (T.lam R * T.u R - R)⁻¹ ∧
      (T.β ≠ 0 →
        0 < T.lam R / (T.lam R * T.u R - R) ^ 2 * (T.A * R ^ T.β * Real.log R) * (1 - T.β - T.γ) +
          T.u R * T.lam R / R * (T.lam R * T.u R - R)⁻¹) := by
  obtain ⟨hA, hη, hβ0, hβ1, hγ0, hγ1, hβγ, hAη⟩ := hT
  have hR : 0 < R := by linarith
  have hlamR : 0 < T.lam R := by unfold AccelScal.UCMonopoly.Tech.lam; positivity
  have huR : T.u R = T.A * R ^ T.β := rfl
  have hlR : T.lam R = T.η * R ^ T.γ := rfl
  have hDpos : 0 < T.lam R * T.u R - R := by nlinarith
  have hne0 : (fun b : ℝ => (T.A * R ^ b) * (T.η * R ^ T.γ) - R) T.β ≠ 0 := by
    show (T.A * R ^ T.β) * (T.η * R ^ T.γ) - R ≠ 0
    rw [← huR, ← hlR]; nlinarith
  have hRb : ContinuousAt (fun b : ℝ => R ^ b) T.β := Real.continuousAt_const_rpow hR.ne'
  have hcont : ContinuousAt (fun b : ℝ => (T.A * R ^ b) * (T.η * R ^ T.γ) - R) T.β := by
    exact ((continuousAt_const.mul hRb).mul continuousAt_const).sub continuousAt_const
  have hev : (fun b => deriv (fun x => AccelScal.UCMonopoly.logV { T with β := b } r x) R) =ᶠ[𝓝 T.β]
      fun b => ASUP.D1 T.A b T.η T.γ r R := by
    filter_upwards [hcont.eventually_ne hne0] with b hb
    exact ASUP.hasDeriv_logV { T with β := b } r hR hb (by
      show T.η * R ^ T.γ + r ≠ 0
      rw [← hlR]; linarith)
  rw [hev.deriv_eq]
  have hL : T.η * R ^ T.γ + r ≠ 0 := by rw [← hlR]; linarith
  have hDne : T.A * R ^ T.β * (T.η * R ^ T.γ) - R ≠ 0 := by
    rw [← huR, ← hlR]; nlinarith
  have hX : HasDerivAt (fun b : ℝ => R ^ b) (R ^ T.β * Real.log R) T.β :=
    (Real.hasStrictDerivAt_const_rpow hR T.β).hasDerivAt
  have hXR : HasDerivAt (fun b : ℝ => R ^ b / R) (R ^ T.β * Real.log R / R) T.β := hX.div_const R
  have hbX : HasDerivAt (fun b : ℝ => b * (R ^ b / R))
      (1 * (R ^ T.β / R) + T.β * (R ^ T.β * Real.log R / R)) T.β :=
    (hasDerivAt_id T.β).mul hXR
  have hN : HasDerivAt (fun b : ℝ => (T.A * (b * (R ^ b / R))) * (T.η * R ^ T.γ) +
      (T.A * R ^ b) * (T.η * (T.γ * (R ^ T.γ / R))) - 1)
      (T.A * (1 * (R ^ T.β / R) + T.β * (R ^ T.β * Real.log R / R)) * (T.η * R ^ T.γ) +
        T.A * (R ^ T.β * Real.log R) * (T.η * (T.γ * (R ^ T.γ / R)))) T.β := by
    have := (((hbX.const_mul T.A).mul_const (T.η * R ^ T.γ)).add
      ((hX.const_mul T.A).mul_const (T.η * (T.γ * (R ^ T.γ / R))))).sub_const 1
    exact this
  have hDd : HasDerivAt (fun b : ℝ => (T.A * R ^ b) * (T.η * R ^ T.γ) - R)
      (T.A * (R ^ T.β * Real.log R) * (T.η * R ^ T.γ)) T.β := by
    have := ((hX.const_mul T.A).mul_const (T.η * R ^ T.γ)).sub_const R
    exact this
  have h3 := (hN.div hDd hDne).sub_const ((T.η * (T.γ * (R ^ T.γ / R))) / ((T.η * R ^ T.γ) + r))
  have hd : HasDerivAt (fun b => ASUP.D1 T.A b T.η T.γ r R)
      (T.lam R / (T.lam R * T.u R - R) ^ 2 * (T.A * R ^ T.β * Real.log R) * (1 - T.β - T.γ) +
          T.u R * T.lam R / R * (T.lam R * T.u R - R)⁻¹) T.β := by
    refine h3.congr_deriv ?_
    rw [hlR, huR] at hDpos ⊢
    have hD3 : T.η * R ^ T.γ * (T.A * R ^ T.β) - R ≠ 0 := by
      intro h; apply hDne; linarith
    field_simp
    ring
  refine ⟨hd.deriv, fun _ => ?_⟩
  have h1bg : 0 < 1 - T.β - T.γ := by linarith
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR1
  have huPos : 0 < T.u R := by rw [huR]; positivity
  have hxpos : 0 < R ^ T.β := Real.rpow_pos_of_pos hR _
  have t1 : 0 ≤ T.lam R / (T.lam R * T.u R - R) ^ 2 * (T.A * R ^ T.β * Real.log R) * (1 - T.β - T.γ) := by
    have : 0 ≤ T.A * R ^ T.β * Real.log R := by positivity
    exact mul_nonneg (mul_nonneg (div_nonneg hlamR.le (sq_nonneg _)) this) h1bg.le
  have t2 : 0 < T.u R * T.lam R / R * (T.lam R * T.u R - R)⁻¹ :=
    mul_pos (div_pos (mul_pos huPos hlamR) hR) (inv_pos.2 hDpos)
  linarith
