-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:43.851697+00:00
-- url     : https://prove2.me/theorems/ed2f6e15-a076-4d60-b352-51bac514be0f
-- title:
--   Arith Degree Exact
-- statement:
--   Definitions and structural lemmas for Arith Degree Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
section Span
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) (σ : K →+* ℂ)
end Span
section GramBlock
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
end GramBlock
def HermitianBundle.arithDegree (A : HermitianBundle K) : ℝ :=
  GroundTheory.Heights₂.Heights.arithDegree A.metric
namespace HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable {m n : Type*} [Fintype m] [Fintype n]
end HermitianExtension
namespace HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
end HermitianExtension
end
end GroundTheory.Heights₂.Heights


