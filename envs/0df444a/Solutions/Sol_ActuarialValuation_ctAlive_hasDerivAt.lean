-- Prove2me | solution 1 for ActuarialValuation.ctAlive_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:16:35.380455+00:00
-- url     : https://prove2.me/submissions/9927d2b2-9cf6-4cbf-bcc9-f5845e21e71d

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctAlive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mu t : ℝ) : HasDerivAt (ctAlive mu) (-mu*ctAlive mu t) t := by
  have hsub : HasDerivAt (fun x : ℝ => (0 : ℝ) - x) ((0 : ℝ) - 1) t := by
    exact (hasDerivAt_const t (0 : ℝ)).sub (hasDerivAt_id t)
  have hs := hsub.const_mul mu
  have hrate : mu * ((0 : ℝ) - 1) = -mu := by ring
  rw [hrate] at hs
  have hfun : (fun x : ℝ => mu * ((0 : ℝ) - x)) =
      (fun x : ℝ => (-mu) * x) := by
    funext x
    ring
  rw [hfun] at hs
  have hexp : HasDerivAt (fun x : ℝ => Real.exp ((-mu) * x))
      (Real.exp ((-mu) * t) * (-mu)) t :=
    (Real.hasDerivAt_exp _).comp t hs
  have hsurv : ctAlive mu = (fun x : ℝ => Real.exp ((-mu) * x)) := by
    funext x
    unfold ctAlive
    congr 1
  rw [hsurv]
  have hmul : (-mu) * Real.exp ((-mu) * t) =
      Real.exp ((-mu) * t) * (-mu) := by ring
  rw [hmul]
  exact hexp
