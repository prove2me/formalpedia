-- Prove2me | solution 1 for AuditEvasion.eq_12_unique_root
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:26:11.243209+00:00
-- url     : https://prove2.me/submissions/77fa791c-7e5f-4b51-83eb-a93509b62dfd

import Mathlib
import Definitions.Def_AuditEvasion_Gamma

open AuditEvasion in
theorem solution (p : Params) (hlam : 0 < p.lam) (htheta : 0 < p.theta)
    (hk : 0 < p.k) (hh : 0 < p.h) (hhF : p.h ≤ p.F) :
    ∃! t : ℝ, 0 < t ∧ Gamma p t = 0 := by
  have hd1 : ∀ t, HasDerivAt (fun t => Real.exp (-p.lam * t))
      (Real.exp (-p.lam * t) * (-p.lam)) t := by
    intro t
    have := ((hasDerivAt_id t).const_mul (-p.lam)).exp
    simpa using this
  have hd2 : ∀ t, HasDerivAt (fun t => Real.exp (-(p.lam + p.theta) * t))
      (Real.exp (-(p.lam + p.theta) * t) * (-(p.lam + p.theta))) t := by
    intro t
    have := ((hasDerivAt_id t).const_mul (-(p.lam + p.theta))).exp
    simpa using this
  have hΓ : ∀ t, HasDerivAt (Gamma p)
      (p.lam * (p.lam + p.theta) * ((p.k + p.F) * Real.exp (-p.lam * t) -
        p.h * Real.exp (-(p.lam + p.theta) * t))) t := by
    intro t
    have h := ((((hd1 t).const_mul (p.k + p.F)).const_sub p.F).const_mul (p.lam + p.theta)).sub
      (((hd2 t).const_sub 1).const_mul (p.lam * p.h))
    refine h.congr_deriv ?_
    ring
  have hcont : Continuous (Gamma p) :=
    continuous_iff_continuousAt.mpr fun t => (hΓ t).continuousAt
  have hmono : StrictMonoOn (Gamma p) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcont.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := hx
    rw [(hΓ x).deriv]
    have he : Real.exp (-(p.lam + p.theta) * x) ≤ Real.exp (-p.lam * x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have he1 := Real.exp_pos (-p.lam * x)
    have : p.h * Real.exp (-(p.lam + p.theta) * x) < (p.k + p.F) * Real.exp (-p.lam * x) := by
      calc p.h * Real.exp (-(p.lam + p.theta) * x) ≤ p.h * Real.exp (-p.lam * x) :=
            mul_le_mul_of_nonneg_left he hh.le
        _ < (p.k + p.F) * Real.exp (-p.lam * x) := mul_lt_mul_of_pos_right (by linarith) he1
    have hpos : 0 < p.lam * (p.lam + p.theta) := mul_pos hlam (by linarith)
    exact mul_pos hpos (by linarith)
  have hG0 : Gamma p 0 < 0 := by
    unfold Gamma
    simp only [mul_zero, Real.exp_zero, sub_self, mul_one]
    nlinarith
  set c := (p.lam + p.theta) * p.F - p.lam * p.h with hc
  have hcpos : 0 < c := by nlinarith
  set M := (p.lam + p.theta) * (p.k + p.F) with hM
  have hMpos : 0 < M := mul_pos (by linarith) (by linarith)
  set T := M / (c * p.lam) with hTdef
  have hTpos : 0 < T := div_pos hMpos (mul_pos hcpos hlam)
  have hlT : p.lam * T = M / c := by
    rw [hTdef]
    field_simp
  have hE : Real.exp (-p.lam * T) * (1 + p.lam * T) ≤ 1 := by
    have h1 := Real.add_one_le_exp (p.lam * T)
    have h2 : Real.exp (-p.lam * T) * Real.exp (p.lam * T) = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 := Real.exp_pos (-p.lam * T)
    nlinarith
  have hGT : 0 < Gamma p T := by
    rw [hlT] at hE
    have hE0 := Real.exp_pos (-p.lam * T)
    have hE2 := Real.exp_pos (-(p.lam + p.theta) * T)
    have hEc : Real.exp (-p.lam * T) * (c + M) ≤ c := by
      have : Real.exp (-p.lam * T) * (1 + M / c) * c ≤ 1 * c :=
        mul_le_mul_of_nonneg_right hE hcpos.le
      have e : Real.exp (-p.lam * T) * (1 + M / c) * c = Real.exp (-p.lam * T) * (c + M) := by
        field_simp
      linarith
    have hME : M * Real.exp (-p.lam * T) < c := by nlinarith
    unfold Gamma
    have : 0 ≤ p.lam * p.h * Real.exp (-(p.lam + p.theta) * T) := by positivity
    nlinarith
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Ioo hTpos.le hcont.continuousOn ⟨hG0, hGT⟩
  refine ⟨t, ⟨ht.1, hzero⟩, ?_⟩
  rintro s ⟨hs, hs0⟩
  exact hmono.injOn (Set.mem_Ici.mpr hs.le) (Set.mem_Ici.mpr ht.1.le) (by rw [hs0, hzero])
