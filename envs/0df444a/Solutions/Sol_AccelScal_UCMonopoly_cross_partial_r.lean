-- Prove2me | solution 1 for AccelScal.UCMonopoly.cross_partial_r
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:52:25.946334+00:00
-- url     : https://prove2.me/submissions/268f1f61-2451-4826-ba33-d00be9b4b567

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
    deriv (fun s => deriv (fun x => AccelScal.UCMonopoly.logV T s x) R) r = deriv T.lam R / (T.lam R + r) ^ 2 ∧
      (0 < T.γ → 0 < deriv T.lam R / (T.lam R + r) ^ 2) := by
  obtain ⟨hA, hη, hβ0, hβ1, hγ0, hγ1, hβγ, hAη⟩ := hT
  have hR : 0 < R := by linarith
  have hlamR : 0 < T.lam R := by unfold AccelScal.UCMonopoly.Tech.lam; positivity
  have hD : T.u R * T.lam R - R ≠ 0 := by linarith
  have hlam' := ASUP.hasDeriv_lam T hR
  have hev : (fun s => deriv (fun x => AccelScal.UCMonopoly.logV T s x) R) =ᶠ[𝓝 r]
      fun s => ASUP.D1 T.A T.β T.η T.γ s R := by
    filter_upwards [lt_mem_nhds hr] with s hs
    exact ASUP.hasDeriv_logV T s hR hD (by linarith)
  rw [hev.deriv_eq]
  have hL : T.lam R + r ≠ 0 := by linarith
  have h1 : HasDerivAt (fun s : ℝ => T.lam R + s) 1 r := (hasDerivAt_id r).const_add _
  have h2 := (hasDerivAt_const r (T.η * (T.γ * (R ^ T.γ / R)))).div h1 hL
  have h3 := (hasDerivAt_const r (((T.A * (T.β * (R ^ T.β / R))) * (T.η * R ^ T.γ) +
      (T.A * R ^ T.β) * (T.η * (T.γ * (R ^ T.γ / R))) - 1) /
      ((T.A * R ^ T.β) * (T.η * R ^ T.γ) - R))).sub h2
  have e : deriv T.lam R = T.η * (T.γ * (R ^ T.γ / R)) := hlam'.deriv
  have hd : HasDerivAt (fun s => ASUP.D1 T.A T.β T.η T.γ s R)
      (deriv T.lam R / (T.lam R + r) ^ 2) r := by
    refine h3.congr_deriv ?_
    rw [e]
    have : T.lam R = T.η * R ^ T.γ := rfl
    rw [this]
    field_simp
    ring
  refine ⟨hd.deriv, fun hγ => ?_⟩
  rw [e]
  have : 0 < R ^ T.γ / R := by positivity
  positivity
