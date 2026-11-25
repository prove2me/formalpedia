-- Prove2me | Definitions.Def_BasicResults_KadetsSnobar
-- name    : BasicResults_KadetsSnobar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:42:36.525224+00:00
-- url     : https://prove2.me/theorems/4bd9039f-45e7-4560-8f98-e237e33aa657
-- title:
--   Kadets Snobar
-- statement:
--   Definitions and structural lemmas for Kadets Snobar, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/KadetsSnobar.lean

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
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
end SNumbers


