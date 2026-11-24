-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
-- name    : LeanPool_BlockSpectralSensitivity_Defs_Tournament
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:44:07.319124+00:00
-- url     : https://prove2.me/theorems/362f9b38-b59b-4f8b-9b59-04c38db04b6b
-- title:
--   Tournament
-- statement:
--   Definitions and structural lemmas for Tournament, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
open Finset
variable {ι : Type*}
structure IsTournament (Arc : ι → ι → Bool) : Prop where
  /-- There is no arc from a vertex to itself. -/
  arc_self : ∀ i, Arc i i = false
  /-- Distinct vertices are joined by exactly one arc. -/
  arc_eq_not_arc : ∀ {i j}, i ≠ j → Arc i j = !Arc j i
namespace IsTournament
variable {Arc : ι → ι → Bool} (h : IsTournament Arc) {i j : ι}
include h
end IsTournament
variable [Fintype ι]
def outNbrs (Arc : ι → ι → Bool) (i : ι) : Finset ι := {j | Arc i j}
def inNbrs (Arc : ι → ι → Bool) (i : ι) : Finset ι := {j | Arc j i}
section Nbrs
variable {Arc : ι → ι → Bool} {i j : ι}
end Nbrs
variable [DecidableEq ι]
def commonOut (Arc : ι → ι → Bool) (i j : ι) : Finset ι := outNbrs Arc i ∩ outNbrs Arc j
def commonIn (Arc : ι → ι → Bool) (i j : ι) : Finset ι := inNbrs Arc i ∩ inNbrs Arc j
def middles (Arc : ι → ι → Bool) (u v : ι) : Finset ι := outNbrs Arc u ∩ inNbrs Arc v
section Common
variable {Arc : ι → ι → Bool} {i j l u v : ι}
namespace IsTournament
variable (h : IsTournament Arc)
include h
end IsTournament
end Common
structure IsDRTournamentWith (Arc : ι → ι → Bool) (d t : ℕ) : Prop extends IsTournament Arc where
  /-- Every vertex has out-degree `d`. -/
  card_outNbrs : ∀ i, (outNbrs Arc i).card = d
  /-- Distinct vertices have `t` common out-neighbours. -/
  card_commonOut : ∀ {i j}, i ≠ j → (commonOut Arc i j).card = t
  /-- Distinct vertices have `t` common in-neighbours. -/
  card_commonIn : ∀ {i j}, i ≠ j → (commonIn Arc i j).card = t
namespace IsDRTournamentWith
variable {Arc : ι → ι → Bool} {d t : ℕ} (h : IsDRTournamentWith Arc d t) {u v : ι}
include h
end IsDRTournamentWith
end BSLambda


