-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DeterminedOnOpenStratum
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_DeterminedOnOpenStratum
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:38:37.802847+00:00
-- url     : https://prove2.me/theorems/646de9f8-eb11-4259-a394-f247ea4137d1
-- title:
--   Determined On Open Stratum
-- statement:
--   Definitions and structural lemmas for Determined On Open Stratum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DeterminedOnOpenStratum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_WeilTensorLiftConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_BoundaryVanishingPullback
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct
namespace GlobalTheory.OpenStratumMaps
section General
variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
def contraction (ρ : Representation F G V) (σ : Representation F H W) (l : W →ₗ[F] F) :
    Representation.IntertwiningMap ((extTensor ρ σ).comp (MonoidHom.inl G H)) ρ where
  toLinearMap := (TensorProduct.rid F V).toLinearMap ∘ₗ l.lTensor V
  isIntertwining' g := by
    refine TensorProduct.ext' fun v w => ?_
    show TensorProduct.rid F V (l.lTensor V (extTensor ρ σ (g, 1) (v ⊗ₜ w))) =
      ρ g (TensorProduct.rid F V (l.lTensor V (v ⊗ₜ w)))
    rw [extTensor_tmul]
    simp
end General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.OpenStratumMaps


