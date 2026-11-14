-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.stationary_linear_covariance_lyapunov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:29:32.14104+00:00
-- url     : https://prove2.me/submissions/cab3feb7-11dd-4fa8-b3bc-1798b744e13c

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory
open scoped BigOperators Topology

theorem solution
    (n : ℕ)
    (F Q Pstat : Matrix (Fin n) (Fin n) ℝ)
    (P : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hstationary : ∀ t : ℝ, P t = Pstat)
    (hCovODE : ∀ (t : ℝ) (i j : Fin n),
      deriv (fun s : ℝ => P s i j) t =
        (F * P t + P t * F.transpose + Q) i j) :
    F * Pstat + Pstat * F.transpose + Q = 0 := by
  ext i j
  have hconst :
      (fun s : ℝ => P s i j) = fun _ => Pstat i j := by
    funext s
    rw [hstationary s]
  have hderiv : deriv (fun s : ℝ => P s i j) 0 = 0 := by
    rw [hconst]
    simp
  have hode := hCovODE 0 i j
  rw [hstationary 0, hderiv] at hode
  simpa using hode.symm
