-- Prove2me | Definitions.Def_AddOns_Approximable
-- name    : AddOns_Approximable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:38:22.709806+00:00
-- url     : https://prove2.me/theorems/d8d024b1-c21b-413f-9dfa-54b2e7bc6cf4
-- title:
--   Approximable
-- statement:
--   Definitions and structural lemmas for Approximable, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped Cardinal
open Filter Topology
namespace SVD
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
def IsApproximable (S : X →L[𝕜] Y) : Prop :=
  Tendsto (SNumbers.approximationNumber S) atTop (𝓝 0)
section ApproximableImpliesCompact
variable [LocallyCompactSpace 𝕜] [CompleteSpace Y]
end ApproximableImpliesCompact
end SVD


