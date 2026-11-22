-- Prove2me | Definitions.Def_Csg_IntrusionDetectionRecurrence
-- name    : Csg_IntrusionDetectionRecurrence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:42:51.671881+00:00
-- url     : https://prove2.me/theorems/c4fbe7fc-0ed1-4602-abb2-4b6b238206f5
-- title:
--   Intrusion Detection Recurrence
-- statement:
--   Definitions and structural lemmas for Intrusion Detection Recurrence, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionRecurrence.lean

import Definitions.Def_Csg_IntrusionDetection
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
set_option autoImplicit true
namespace Csg
open MeasureTheory Measure ProbabilityTheory
instance : MeasurableSpace IDSState := ⊤
instance : MeasurableSpace PolicyAction := ⊤
instance : MeasurableSpace AttackAction := ⊤
instance : DiscreteMeasurableSpace IDSState := ⟨fun _ => trivial⟩
instance : DiscreteMeasurableSpace PolicyAction := ⟨fun _ => trivial⟩
instance : DiscreteMeasurableSpace AttackAction := ⟨fun _ => trivial⟩
variable (q : ℕ → PMF AttackAction)
noncomputable def idsRoundPMF (n : ℕ) : PMF (PolicyAction × AttackAction) :=
  (PMF.uniformOfFintype PolicyAction).bind fun a1 => (q n).map fun a2 => (a1, a2)
noncomputable def idsPlayMeasure : Measure (ℕ → PolicyAction × AttackAction) :=
  Measure.infinitePi fun n => (idsRoundPMF q n).toMeasure
instance idsPlayMeasure_isProbabilityMeasure : IsProbabilityMeasure (idsPlayMeasure q) := by
  unfold idsPlayMeasure
  infer_instance
def idsRoundHealthy (p : PolicyAction × AttackAction) : Bool :=
  decide (idsNext p.1 p.2 = .healthy)
end Csg


