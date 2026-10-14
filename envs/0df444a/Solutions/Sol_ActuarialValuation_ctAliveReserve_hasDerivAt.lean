-- Prove2me | solution 1 for ActuarialValuation.ctAliveReserve_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:26:22.608915+00:00
-- url     : https://prove2.me/submissions/e22321b2-938d-479e-9141-9f0ff6fedcdd

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRiskRate
import Definitions.Def_actuarial_ctAliveReserve
import Definitions.Def_actuarial_ctAliveThiele

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (delta mu b death maturity t : ℝ) (h : ctRiskRate delta mu ≠ 0) : HasDerivAt (ctAliveReserve delta mu b death maturity) (ctAliveThiele delta mu b death (ctAliveReserve delta mu b death maturity t)) t := by
  let r := ctRiskRate delta mu
  let f := ctInsuranceFlow b mu death
  have haff : HasDerivAt (fun x : ℝ => (-r) * (maturity - x)) r t := by
    have hsub : HasDerivAt (fun x : ℝ => maturity - x) ((0 : ℝ) - 1) t := by
      exact (hasDerivAt_const t maturity).sub (hasDerivAt_id t)
    have hs := hsub.const_mul (-r)
    have hrid : (-r) * ((0 : ℝ) - 1) = r := by ring
    rw [hrid] at hs
    exact hs
  have hexp : HasDerivAt (fun x : ℝ => Real.exp ((-r) * (maturity - x)))
      (Real.exp ((-r) * (maturity - t)) * r) t :=
    (Real.hasDerivAt_exp _).comp t haff
  have hmain : HasDerivAt
      (fun x : ℝ => (f / r) * (1 - Real.exp ((-r) * (maturity - x))))
      ((f / r) * (0 - (Real.exp ((-r) * (maturity - t)) * r))) t :=
    ((hasDerivAt_const t (1 : ℝ)).sub hexp).const_mul (f / r)
  have hident : ctAliveThiele delta mu b death
      (ctAliveReserve delta mu b death maturity t) =
      (f / r) * (0 - Real.exp ((-r) * (maturity - t)) * r) := by
    unfold ctAliveThiele ctAliveReserve
    dsimp [r, f]
    field_simp [h]
    ring
  rw [hident]
  change HasDerivAt
    (fun x : ℝ => (f / r) * (1 - Real.exp ((-r) * (maturity - x))))
    ((f / r) * (0 - (Real.exp ((-r) * (maturity - t)) * r))) t
  exact hmain
