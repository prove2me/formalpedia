-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:42.518564+00:00
-- url     : https://prove2.me/theorems/f50bb2ec-b7f6-485c-afa6-d9fa25b8e461
-- title:
--   Hom Relation Holds
-- statement:
--   Definitions and structural lemmas for Hom Relation Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/HomRelationHolds.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open Finset
section gen
variable {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [DecidableEq ι]
def postC (X : Module.End K W) : Module.End K (V →ₗ[K] W) where
  toFun := fun φ => X ∘ₗ φ
  map_add' := by intro φ ψ; ext x; simp
  map_smul' := by intro c φ; ext x; simp
def preC (Y : Module.End K V) : Module.End K (V →ₗ[K] W) where
  toFun := fun φ => φ ∘ₗ Y
  map_add' := by intro φ ψ; ext x; simp
  map_smul' := by intro c φ; ext x; simp
end gen
end Formalism.InvariantFactorPaths.PW


