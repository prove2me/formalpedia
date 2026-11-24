-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFnDegRelDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFnDegRelDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:00.203637+00:00
-- url     : https://prove2.me/theorems/6506b57a-7479-4e5a-ba57-cd3d850cb625
-- title:
--   PFn Deg Rel Deg
-- statement:
--   Definitions and structural lemmas for PFn Deg Rel Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
namespace FnDegRelDeg
section Dehom
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
end Dehom
section Contract
variable {F : Type u} [Field F] {K K' : Type} {ι' : K' → Type} (j : K ↪ K') (P' : Ideal (MRing ι' F))
  [P'.IsPrime] (i' : ∀ k', ι' k')
end Contract
end FnDegRelDeg
end
end GroundTheory.Heights₂.Heights.Targets


