-- Prove2me | Definitions.Def_SNumbers_ContinuousLinearMapRank
-- name    : SNumbers_ContinuousLinearMapRank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:34.816293+00:00
-- url     : https://prove2.me/theorems/69545de3-bcfd-4fdb-9577-a2461020ae3e
-- title:
--   Continuous Linear Map Rank
-- statement:
--   Definitions and structural lemmas for Continuous Linear Map Rank, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/ContinuousLinearMapRank.lean

module
public import Definitions.Def_SNumbers_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped Cardinal
namespace ContinuousLinearMap
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
section Rank
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
end Rank
section CompRank
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
end CompRank
end ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
end SNumbers


