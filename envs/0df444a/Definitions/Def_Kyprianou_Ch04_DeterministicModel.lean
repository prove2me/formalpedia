-- Prove2me | Definitions.Def_Kyprianou_Ch04_DeterministicModel
-- name    : Kyprianou_Ch04_DeterministicModel
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:22:00.564119+00:00
-- url     : https://prove2.me/theorems/8dcf91d3-0c8a-4031-a8ed-8411a35a7166
-- title:
--   Singleton deterministic Levy path and real-mark zero-intensity Poisson random measure
-- statement:
--   Concrete probability model on Unit with unit deterministic drift and an identically zero real-mark Poisson random measure of zero intensity. The definitions package their actual Levy-process and PRM laws.
-- source:
--   Elementary deterministic Levy and zero-intensity Poisson model; auxiliary to Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04.DeterministicModel
/-- All sigma-fields are independent on a one-point probability space. -/
private theorem singletonIndep {ι : Type} (m : ι → MeasurableSpace Unit) :
    iIndep m (Measure.dirac ()) := by
  classical
  rw [iIndep_iff]
  intro S A hA
  simp [Set.indicator_apply, Finset.prod_boole]

/-- A deterministic unit-speed path is a Levy process. -/
private theorem unitDriftLevy :
    IsLevyProcess (fun t : NNReal => fun _ : Unit => (t : Real))
      (Measure.dirac ()) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro n t ht
    apply (iIndepFun_iff_iIndep _ _ _).2
    exact singletonIndep _
  · intro s h
    have heq : increment (fun t : NNReal => fun _ : Unit => (t : Real))
        s (s+h) = increment (fun t : NNReal => fun _ : Unit => (t : Real))
        0 h := by
      funext w
      simp [increment]
    rw [heq]
    exact IdentDistrib.refl (by fun_prop)
  · apply Eventually.of_forall
    intro w t
    have hc : Continuous (fun t : NNReal => (t : Real)) := continuous_subtype_val
    exact ⟨hc.continuousWithinAt, ⟨(t : Real), hc.continuousWithinAt⟩⟩

/-- A zero-intensity Poisson random measure with no atoms. -/
noncomputable def zeroPRM :
    PoissonRandomMeasure.{0,0,0} (Measure.dirac () : Measure Unit)
      (0 : Measure Real) where
  N := fun _ => 0
  measurable_eval := by intros; exact measurable_const
  integer_valued := by
    intros
    exact Eventually.of_forall (fun _ => ⟨0, by simp⟩)
  infinite_at_infinite_intensity := by
    intro B hB h
    simp [referenceIntensity, Measure.prod_zero] at h
  poisson_law := by
    intro B hB hfin
    have hp : poissonMeasure 0 = Measure.dirac 0 := by
      apply Measure.ext_of_singleton
      intro n
      cases n <;> simp [poissonMeasure_singleton]
    simp [referenceIntensity, Measure.prod_zero, poissonMeasureENN, hp]
  independent_disjoint := by
    intros
    apply (iIndepFun_iff_iIndep _ _ _).2
    exact singletonIndep _
  joint_past_future_independent := by
    intros
    simp only [Measure.coe_zero, Pi.zero_apply, MeasurableSpace.comap_const]
    exact indep_bot_right _

/-- A concrete deterministic unit-speed Lévy process on the singleton probability space. -/
def unitDrift : {X : NNReal → Unit → Real // IsLevyProcess X (Measure.dirac ())} :=
  ⟨fun t _ => (t : Real), unitDriftLevy⟩

end Kyprianou.Ch04.DeterministicModel


