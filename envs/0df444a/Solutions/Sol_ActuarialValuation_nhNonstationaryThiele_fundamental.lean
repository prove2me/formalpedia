-- Prove2me | solution 1 for ActuarialValuation.nhNonstationaryThiele_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:29:58.508979+00:00
-- url     : https://prove2.me/submissions/a44b4eac-5f9e-436b-a36a-fc53b1ca4693

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhGenerator
import Definitions.Def_actuarial_nhTransition
import Definitions.Def_actuarial_nhReserve
import Definitions.Def_actuarial_nhThieleRHS

import Theorems.Thm_ActuarialValuation_nhGenerator_alive_row
import Theorems.Thm_ActuarialValuation_nhTransition_alive_row
import Theorems.Thm_ActuarialValuation_nhReserve_terminal
import Theorems.Thm_ActuarialValuation_nhReserve_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p δ B1 B2 M T t : ℝ) (ha : 0≤a) (hb : 0≤b) (hp : 0≤p) (hq : p≤1) (ht : 0≤t) (hT : t≤T) : ((∑ j : Fin 3, nhGenerator a b p t 0 j)=0) ∧ ((∑ j : Fin 3, nhTransition a b p t T 0 j)=1) ∧ (nhReserve a b p δ B1 B2 M T T=M) ∧ HasDerivAt (nhReserve a b p δ B1 B2 M T) (nhThieleRHS a b p δ B1 B2 t (nhReserve a b p δ B1 B2 M T t)) t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact nhGenerator_alive_row a b p t
  · exact nhTransition_alive_row a b p t T
  · exact nhReserve_terminal a b p δ B1 B2 M T
  · exact nhReserve_deriv a b p δ B1 B2 M T t
