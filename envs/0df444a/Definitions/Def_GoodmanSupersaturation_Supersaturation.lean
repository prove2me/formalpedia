-- Prove2me | Definitions.Def_GoodmanSupersaturation_Supersaturation
-- name    : GoodmanSupersaturation_Supersaturation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:30:42.086287+00:00
-- url     : https://prove2.me/theorems/541c2a34-c492-4232-9c2f-7d39ea89f51b
-- title:
--   Supersaturation
-- statement:
--   Definitions and structural lemmas for Supersaturation, from Brian Sanders (Egly443/lean-goodman-supersaturation; see pinned Apache-2.0 LICENSE and source headers)'s pinned Goodman's formula and supersaturation for two-colourings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace SimpleGraph
variable {V : Type*}
section Recursion
variable [DecidableEq V]
noncomputable def supersaturationBound (k l : ℕ) (x : ℝ) : ℝ :=
  x ^ k * 2 ^ (2 * k + 1) / ((k.factorial : ℝ) * 2 ^ (k * l + (k + 1).choose 2))
variable (G : SimpleGraph V) [DecidableRel G.Adj]
abbrev nbhd (S : Finset V) (v : V) : Finset V := {w ∈ S | G.Adj v w}
def Claim (V : Type*) [DecidableEq V] (k l : ℕ) : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V), 0 < (#S : ℝ) + 1 - 2 ^ (k + l - 3) →
    supersaturationBound k l ((#S : ℝ) + 1 - 2 ^ (k + l - 3)) ≤ G.cliqueCountIn S k ∨
      supersaturationBound l k ((#S : ℝ) + 1 - 2 ^ (k + l - 3)) ≤ Gᶜ.cliqueCountIn S l
end Recursion
end SimpleGraph


