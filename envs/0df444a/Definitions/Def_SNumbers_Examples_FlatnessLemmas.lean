-- Prove2me | Definitions.Def_SNumbers_Examples_FlatnessLemmas
-- name    : SNumbers_Examples_FlatnessLemmas
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:41.334601+00:00
-- url     : https://prove2.me/theorems/d6fc237f-d6d9-4cda-8ed4-066565203773
-- title:
--   Flatness Lemmas
-- statement:
--   Definitions and structural lemmas for Flatness Lemmas, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/FlatnessLemmas.lean

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Mathlib.Analysis.Convex.KreinMilman
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped ENNReal
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
end SNumbers


