-- Prove2me | Definitions.Def_SNumbers_Inequalities
-- name    : SNumbers_Inequalities
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T04:14:20.463352+00:00
-- url     : https://prove2.me/theorems/89076314-1273-4a5a-8f50-e74dcf4ffb8f
-- title:
--   Inequalities
-- statement:
--   Definitions and structural lemmas for Inequalities, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
section Hilbert
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
end Hilbert
variable [CompleteSpace X] [CompleteSpace Y]
end SNumbers


