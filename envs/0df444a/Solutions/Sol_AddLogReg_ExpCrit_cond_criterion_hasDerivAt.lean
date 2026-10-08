-- Prove2me | solution 1 for AddLogReg.ExpCrit.cond_criterion_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:03:51.82101+00:00
-- url     : https://prove2.me/submissions/27cb2bd4-1494-435d-9269-0660b3f863dd

import Mathlib
import Definitions.Def_AddLogReg_ExpCrit_Setting

open MeasureTheory ProbabilityTheory

open AddLogReg.ExpCrit

private lemma bool_integral (μ : Measure Bool) [IsFiniteMeasure μ] (f : Bool → ℝ) :
    (∫ b, f b ∂μ) = (μ {false}).toReal * f false + (μ {true}).toReal * f true := by
  rw [integral_fintype Integrable.of_finite]
  simp [Fintype.sum_bool, Measure.real, smul_eq_mul, add_comm]


/-- Proof of Lemma 1, second display (p. 345): `∂E(e^{−yF(x)}|x)/∂F(x) =
−P(y = 1|x)e^{−F(x)} + P(y = −1|x)e^{F(x)}`. -/
theorem solution {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (x : X) (t : ℝ) :
    HasDerivAt (condCrit ν x)
      (-(condProb ν true x) * Real.exp (-t) + condProb ν false x * Real.exp t) t := by
  have he : condCrit ν x = fun t =>
      condProb ν false x * Real.exp t + condProb ν true x * Real.exp (-t) := by
    funext t
    rw [condCrit, bool_integral]
    simp [condProb, sgn]
  rw [he]
  convert ((Real.hasDerivAt_exp t).const_mul (condProb ν false x)).add
    (((hasDerivAt_id t).neg.exp).const_mul (condProb ν true x)) using 1 <;>
      first | rfl | (funext u; dsimp; ring) | (dsimp; ring) | ring

#print axioms solution
