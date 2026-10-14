-- Prove2me | solution 1 for ActuarialValuation.ctGeneratorThiele_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:06:00.909935+00:00
-- url     : https://prove2.me/submissions/116ffbaa-6399-4eb2-bfb5-62af038435a2

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctGenerator
import Definitions.Def_actuarial_ctEuler
import Definitions.Def_actuarial_ctAlive
import Definitions.Def_actuarial_ctRiskRate
import Definitions.Def_actuarial_ctAliveReserve
import Definitions.Def_actuarial_ctAliveThiele

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : Fin 3 → Fin 3 → ℝ) (h delta mu b death maturity t : ℝ) (hr : ctRiskRate delta mu ≠ 0) (i : Fin 3) : ((∑ j : Fin 3, ctGenerator r i j)=0) ∧ ((∑ j : Fin 3, ctEuler r h i j)=1) ∧ (∀ s u : ℝ, ctAlive mu (s+u)=ctAlive mu s*ctAlive mu u) ∧ (HasDerivAt (ctAliveReserve delta mu b death maturity) (ctAliveThiele delta mu b death (ctAliveReserve delta mu b death maturity t)) t) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · fin_cases i <;> simp [ctGenerator, ctRateOut, Fin.sum_univ_succ] <;> ring
  · fin_cases i <;> simp [ctEuler, ctGenerator, ctRateOut, Fin.sum_univ_succ] <;> ring
  · intro s u
    unfold ctAlive
    have hexp : (-mu) * (s+u) = (-mu)*s + (-mu)*u := by ring
    rw [hexp, Real.exp_add]
  ·
    let rr := ctRiskRate delta mu
    let f := ctInsuranceFlow b mu death
    have haff : HasDerivAt (fun x : ℝ => (-rr) * (maturity - x)) rr t := by
      have hsub : HasDerivAt (fun x : ℝ => maturity - x) ((0 : ℝ) - 1) t := by
        exact (hasDerivAt_const t maturity).sub (hasDerivAt_id t)
      have hs := hsub.const_mul (-rr)
      have hrid : (-rr) * ((0 : ℝ) - 1) = rr := by ring
      rw [hrid] at hs
      exact hs
    have hexp : HasDerivAt (fun x : ℝ => Real.exp ((-rr) * (maturity - x)))
        (Real.exp ((-rr) * (maturity - t)) * rr) t :=
      (Real.hasDerivAt_exp _).comp t haff
    have hmain : HasDerivAt
        (fun x : ℝ => (f / rr) * (1 - Real.exp ((-rr) * (maturity - x))))
        ((f / rr) * (0 - (Real.exp ((-rr) * (maturity - t)) * rr))) t :=
      ((hasDerivAt_const t (1 : ℝ)).sub hexp).const_mul (f / rr)
    have hident : ctAliveThiele delta mu b death
        (ctAliveReserve delta mu b death maturity t) =
        (f / rr) * (0 - Real.exp ((-rr) * (maturity - t)) * rr) := by
      unfold ctAliveThiele ctAliveReserve
      dsimp [rr, f]
      field_simp [hr]
      ring
    rw [hident]
    change HasDerivAt
      (fun x : ℝ => (f / rr) * (1 - Real.exp ((-rr) * (maturity - x))))
      ((f / rr) * (0 - (Real.exp ((-rr) * (maturity - t)) * rr))) t
    exact hmain
