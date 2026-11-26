-- Prove2me | Definitions.Def_ChoosabilityLib_ERTBasic
-- name    : ChoosabilityLib_ERTBasic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:27:20.747723+00:00
-- url     : https://prove2.me/theorems/e32f210a-c8af-47d2-9116-4ddf3ffc4920
-- title:
--   ERTBasic
-- statement:
--   Definitions and structural lemmas for ERTBasic, from Juan Pablo Traverso Gianini (jtraverso/brooks; see pinned Apache-2.0 LICENSE and source headers)'s pinned Erdos-Rubin-Taylor degree-choosability, block-cut trees, and Brooks' theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace ErdosRubinTaylor
variable {V : Type*}
def adjIn (G : SimpleGraph V) (T : Set V) (u v : V) : Prop := u ∈ T ∧ v ∈ T ∧ G.Adj u v
def SConn (G : SimpleGraph V) (T : Set V) : Prop :=
  T.Nonempty ∧ ∀ u ∈ T, ∀ v ∈ T, Relation.ReflTransGen (adjIn G T) u v
def ColIn {C : Type*} (G : SimpleGraph V) (T : Set V) (L : V → Finset C) : Prop :=
  ∃ f : V → C, (∀ v ∈ T, f v ∈ L v) ∧ ∀ u ∈ T, ∀ v ∈ T, G.Adj u v → f u ≠ f v
def IsCliqueOn (G : SimpleGraph V) (T : Set V) : Prop := ∀ x ∈ T, ∀ y ∈ T, x ≠ y → G.Adj x y
section rtg
variable {G : SimpleGraph V} {T T' : Set V}
end rtg
section fintype
variable [Fintype V]
open Classical in
/-- The number of neighbours of `v` lying in `T`. -/
noncomputable def dIn (G : SimpleGraph V) (T : Set V) (v : V) : ℕ :=
  (univ.filter (fun u => u ∈ T ∧ G.Adj v u)).card
end fintype
def near (G : SimpleGraph V) (W Tgt : Set V) : ℕ → V → Prop
  | 0, v => v ∈ Tgt
  | n + 1, v => ∃ u ∈ W, G.Adj v u ∧ near G W Tgt n u
section fintype2
variable [Fintype V]
def DCIn (C : Type*) (G : SimpleGraph V) (T : Set V) : Prop :=
  ∀ L : V → Finset C, (∀ v ∈ T, dIn G T v ≤ (L v).card) → ColIn G T L
end fintype2
end ErdosRubinTaylor


