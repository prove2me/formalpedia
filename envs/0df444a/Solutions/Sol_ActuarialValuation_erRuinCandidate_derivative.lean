-- Prove2me | solution 1 for ActuarialValuation.erRuinCandidate_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T21:47:18.853975+00:00
-- url     : https://prove2.me/submissions/911e9ae1-2f06-44e7-ab6f-1098cca785aa

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Group.Ext
import Definitions.Def_actuarial_erRuinCandidate
import Definitions.Def_actuarial_erRuinDerivativeRHS

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda c beta u : ℝ) :
    HasDerivAt (erRuinCandidate lambda c beta)
      (erRuinDerivativeRHS lambda c beta u) u := by
  letI : AddCommGroup ℝ := Real.instAddCommGroup
  letI : Module ℝ ℝ := @Semiring.toModule ℝ Real.semiring
  have hlinear := (hasDerivAt_id u).const_mul (-(erAdjustment lambda c beta))
  have hexp :=
    (Real.hasDerivAt_exp (-(erAdjustment lambda c beta) * u)).comp u hlinear
  have hscaled := hexp.const_mul (erTrafficIntensity lambda c beta)
  unfold erRuinCandidate erRuinDerivativeRHS
  have hadd : @Ring.toAddCommGroup ℝ (@NormedRing.toRing ℝ (@NormedCommRing.toNormedRing ℝ Real.normedCommRing)) = Real.instAddCommGroup := by apply AddCommGroup.ext; funext x y; rfl
  have hmod : @NormedSpace.toModule ℝ ℝ inferInstance inferInstance inferInstance = @Semiring.toModule ℝ Real.semiring := by apply Module.ext; funext a x; rfl
  convert hscaled using 1
  simp only [HasDerivAt, hadd, hmod, mul_assoc, mul_left_comm, mul_comm]
  · apply Module.ext
    funext a x
    rfl
  · funext y
    rfl
  · simp only [erRuinCandidate]
    ring
