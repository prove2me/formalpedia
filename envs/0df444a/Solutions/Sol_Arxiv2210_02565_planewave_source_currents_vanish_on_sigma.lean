-- Prove2me | solution 1 for Arxiv2210_02565.planewave_source_currents_vanish_on_sigma
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T06:58:33.188794+00:00
-- url     : https://prove2.me/submissions/995eea67-e317-4185-889d-23e4f413896d

import Mathlib
import Definitions.Def_Arxiv2210_02565_Basic

open Filter Topology

namespace S81PW
open Arxiv2210_02565

lemma hm (A B : ℂ) (z : ℝ) : HasDerivAt (fun z : ℝ => Complex.exp (Complex.I * (A - B * z)))
    (-(Complex.I * B) * Complex.exp (Complex.I * (A - B * z))) z := by
  have h := ((((hasDerivAt_id' (z:ℂ)).const_mul B).const_sub A).const_mul Complex.I).cexp.comp_ofReal
  convert h using 1
  ring_nf

lemma hp (A B : ℂ) (z : ℝ) : HasDerivAt (fun z : ℝ => Complex.exp (Complex.I * (A + B * z)))
    (Complex.I * B * Complex.exp (Complex.I * (A + B * z))) z := by
  have h := ((((hasDerivAt_id' (z:ℂ)).const_mul B).const_add A).const_mul Complex.I).cexp.comp_ofReal
  convert h using 1
  ring_nf

end S81PW

open Arxiv2210_02565 S81PW in
theorem solution (s : PlanewaveSetup) (hω : 0 < s.ω)
    (hε1 : s.ε1 ≠ 0) (hμ1 : s.μ1 ≠ 0) (hε2 : s.ε2 ≠ 0) (hμ2 : s.μ2 ≠ 0)
    (hk1z : 0 ≤ s.k1z) (hk1 : (s.k1y : ℂ) ^ 2 + (s.k1z : ℂ) ^ 2 = (s.ω : ℂ) ^ 2 * s.μ1 * s.ε1)
    (hTE : s.μ2 * s.k1z + s.μ1 * s.k2z ≠ 0) (hTM : s.ε2 * s.k1z + s.ε1 * s.k2z ≠ 0) :
    ∀ r : Space, r 2 = 0 → srcCurrentM s zhat r = 0 ∧ srcCurrentJ s zhat r = 0 := by
  intro r hr
  have hw : (s.ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  have dH1 : HasDerivAt (fun z => s.Hx1 (r 1) z)
      (s.H0 * (-(Complex.I * s.k1z) * Complex.exp (Complex.I * (s.k1y * (r 1) - s.k1z * (0:ℝ)))) +
        s.H0 * s.RTM * (Complex.I * s.k1z * Complex.exp (Complex.I * (s.k1y * (r 1) + s.k1z * (0:ℝ))))) 0 := by
    unfold PlanewaveSetup.Hx1
    exact ((hm _ _ 0).const_mul _).add ((hp _ _ 0).const_mul _)
  have dH2 : HasDerivAt (fun z => s.Hx2 (r 1) z)
      (s.H0 * s.TTM * (-(Complex.I * s.k2z) * Complex.exp (Complex.I * (s.k1y * (r 1) - s.k2z * (0:ℝ))))) 0 := by
    unfold PlanewaveSetup.Hx2
    exact ((hm _ _ 0).const_mul _)
  have dE1 : HasDerivAt (fun z => s.Ex1 (r 1) z)
      (s.E0 * (-(Complex.I * s.k1z) * Complex.exp (Complex.I * (s.k1y * (r 1) - s.k1z * (0:ℝ)))) +
        s.E0 * s.RTE * (Complex.I * s.k1z * Complex.exp (Complex.I * (s.k1y * (r 1) + s.k1z * (0:ℝ))))) 0 := by
    unfold PlanewaveSetup.Ex1
    exact ((hm _ _ 0).const_mul _).add ((hp _ _ 0).const_mul _)
  have dE2 : HasDerivAt (fun z => s.Ex2 (r 1) z)
      (s.E0 * s.TTE * (-(Complex.I * s.k2z) * Complex.exp (Complex.I * (s.k1y * (r 1) - s.k2z * (0:ℝ))))) 0 := by
    unfold PlanewaveSetup.Ex2
    exact ((hm _ _ 0).const_mul _)
  have e1 : s.RTE + 1 = s.TTE := by
    unfold PlanewaveSetup.RTE PlanewaveSetup.TTE; field_simp; ring
  have e2 : s.RTM + 1 = s.TTM := by
    unfold PlanewaveSetup.RTM PlanewaveSetup.TTM; field_simp; ring
  have e3 : s.RTE - 1 = -(2 * s.μ1 * s.k2z) / (s.μ2 * s.k1z + s.μ1 * s.k2z) := by
    unfold PlanewaveSetup.RTE; field_simp; ring
  have e4 : s.RTM - 1 = -(2 * s.ε1 * s.k2z) / (s.ε2 * s.k1z + s.ε1 * s.k2z) := by
    unfold PlanewaveSetup.RTM; field_simp; ring
  constructor
  · unfold srcCurrentM srcE1 srcE2 fieldE
    rw [hr, dH1.deriv, dH2.deriv]
    funext i
    fin_cases i <;> simp [crossProduct, zhat, PlanewaveSetup.Ex1, PlanewaveSetup.Ex2]
    · rw [show s.RTM = 1 - 2 * s.ε1 * s.k2z / (s.ε2 * s.k1z + s.ε1 * s.k2z) by
        rw [sub_eq_add_neg, ← neg_div, ← e4]; ring]
      unfold PlanewaveSetup.TTM; field_simp; ring
    · rw [← e1]; ring
  · unfold srcCurrentJ srcH1 srcH2 fieldH
    rw [hr, dE1.deriv, dE2.deriv]
    funext i
    fin_cases i <;> simp [crossProduct, zhat, PlanewaveSetup.Hx1, PlanewaveSetup.Hx2]
    · rw [show s.RTE = 1 - 2 * s.μ1 * s.k2z / (s.μ2 * s.k1z + s.μ1 * s.k2z) by
        rw [sub_eq_add_neg, ← neg_div, ← e3]; ring]
      unfold PlanewaveSetup.TTE; field_simp; ring
    · rw [← e2]; ring
