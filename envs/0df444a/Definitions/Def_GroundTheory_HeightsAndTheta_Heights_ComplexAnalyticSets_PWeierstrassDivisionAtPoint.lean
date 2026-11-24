-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeierstrassDivisionAtPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeierstrassDivisionAtPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:08.541653+00:00
-- url     : https://prove2.me/theorems/e0478f72-7da8-41b6-905a-61ae9b5c27c9
-- title:
--   PWeierstrass Division At Point
-- statement:
--   Definitions and structural lemmas for PWeierstrass Division At Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeierstrassDivisionAtPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassDivisionAtPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
noncomputable section
variable {τ : Type} [DecidableEq τ]
def lastToCoordinate (c : τ) : (Option {c' // c' ≠ c} → ℂ) →L[ℂ] (τ → ℂ) :=
  ContinuousLinearMap.pi fun c' =>
    if h : c' = c then ContinuousLinearMap.proj none else ContinuousLinearMap.proj (some ⟨c', h⟩)
def coordinateToLast (c : τ) : (τ → ℂ) →L[ℂ] (Option {c' // c' ≠ c} → ℂ) :=
  ContinuousLinearMap.pi fun o =>
    match o with
    | none => ContinuousLinearMap.proj c
    | some c' => ContinuousLinearMap.proj c'.1
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


