-- Prove2me | Definitions.Def_BasicResults_LittleGrothendieck
-- name    : BasicResults_LittleGrothendieck
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:00.543179+00:00
-- url     : https://prove2.me/theorems/5e1bd818-4932-4bfc-8b1b-1b8361435f39
-- title:
--   Little Grothendieck
-- statement:
--   Definitions and structural lemmas for Little Grothendieck, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
namespace SNumbers
section SignedSum
variable {G : Type*} [AddCommGroup G] {ι : Type*} [DecidableEq ι]
def signedSum (w : ι → G) (S J : Finset ι) : G :=
  ∑ j ∈ J, if j ∈ S then w j else -w j
end SignedSum
section Averaging
variable {ι : Type*} [DecidableEq ι]
end Averaging
section Linfty
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*} [DecidableEq ι]
end Linfty
section L1
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*} [DecidableEq ι]
end L1
section Tsum
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
end Tsum
end SNumbers


