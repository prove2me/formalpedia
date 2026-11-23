-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA
-- name    : ReciprocityTheory_SemistableReduction_SphereTorusA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:23.5312+00:00
-- url     : https://prove2.me/theorems/3fa93b4e-589f-471e-b8b9-7771ccba7c02
-- title:
--   Sphere Torus A
-- statement:
--   Definitions and structural lemmas for Sphere Torus A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusA.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial
instance isProbabilityMeasure_restrict_Ioc_zero_one :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; simp⟩
instance isProbabilityMeasure_torusProb_sphere (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (torusProb ι) := by
  unfold torusProb; infer_instance
end ReciprocityTheory.MultiplicativeHeights


