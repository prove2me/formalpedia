-- Prove2me | Definitions.Def_BasicResults_GarlingGordon
-- name    : BasicResults_GarlingGordon
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:38:15.802181+00:00
-- url     : https://prove2.me/theorems/cede5298-d9a2-4c6b-9aed-065bf92d6c0f
-- title:
--   Garling Gordon
-- statement:
--   Definitions and structural lemmas for Garling Gordon, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/GarlingGordon.lean

module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_BasicResults_John
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
end SNumbers


