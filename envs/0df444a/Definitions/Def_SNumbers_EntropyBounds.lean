-- Prove2me | Definitions.Def_SNumbers_EntropyBounds
-- name    : SNumbers_EntropyBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T04:30:44.767682+00:00
-- url     : https://prove2.me/theorems/f44f0601-f227-5a8c-a535-f9dea5772687
-- title:
--   Entropy Bounds
-- statement:
--   Definitions and structural lemmas for Entropy Bounds, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
section Identity
open MeasureTheory
end Identity
section Hilbert
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
end Hilbert
end SNumbers


