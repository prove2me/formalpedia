-- Prove2me | Definitions.Def_MatchingPolytope_Multigraph
-- name    : MatchingPolytope_Multigraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:18:33.045415+00:00
-- url     : https://prove2.me/theorems/fc203d4d-b4da-5c44-8207-a5ecaba5882e
-- title:
--   Multigraph
-- statement:
--   Definitions and structural lemmas for Multigraph, from Juan Pablo Traverso Gianini (jtraverso/edmonds-matching-polytope; see pinned Apache-2.0 LICENSE and source headers)'s pinned Edmonds perfect matching polytope and matching polytope theorems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingPolytope.Multi
open Finset
variable {V E : Type*}
open Classical in
/-- The edges of `F` with exactly one endpoint in `S`. -/
noncomputable def gcut (ends : E → Sym2 V) (F : Finset E) (S : Finset V) : Finset E :=
  F.filter fun e => (∃ u ∈ ends e, u ∈ S) ∧ ∃ u ∈ ends e, u ∉ S
open Classical in
/-- The edges of `F` with both endpoints in `S`. -/
noncomputable def inside (ends : E → Sym2 V) (F : Finset E) (S : Finset V) : Finset E :=
  F.filter fun e => ∀ u ∈ ends e, u ∈ S
structure Valid (ends : E → Sym2 V) (W : Finset V) (F : Finset E) : Prop where
  sub : ∀ e ∈ F, ∀ u ∈ ends e, u ∈ W
  nodiag : ∀ e ∈ F, ¬ (ends e).IsDiag
def Poly (ends : E → Sym2 V) (W : Finset V) (F : Finset E) : Set (E → ℝ) :=
  {x | (∀ e, e ∉ F → x e = 0) ∧ (∀ e, 0 ≤ x e) ∧ (∀ v ∈ W, ∑ e ∈ gcut ends F {v}, x e = 1) ∧
    ∀ S ⊆ W, Odd S.card → 1 ≤ ∑ e ∈ gcut ends F S, x e}
def IsPM (ends : E → Sym2 V) (W : Finset V) (F : Finset E) (M : Finset E) : Prop :=
  M ⊆ F ∧ ∀ v ∈ W, (gcut ends M {v}).card = 1
open Classical in
/-- Incidence vector of an edge set. -/
noncomputable def chi (M : Finset E) : E → ℝ := fun e => if e ∈ M then 1 else 0
def InHull [Fintype E] (Q : Finset E → Prop) (x : E → ℝ) : Prop :=
  ∃ w : Finset E → ℝ, (∀ M, 0 ≤ w M) ∧ (∀ M, w M ≠ 0 → Q M) ∧ ∑ M, w M = 1 ∧
    ∑ M, w M • chi M = x
open Classical in
/-- Restriction of a vector to an edge set (zero elsewhere). -/
noncomputable def restr (F : Finset E) (x : E → ℝ) : E → ℝ := fun e => if e ∈ F then x e else 0
def Ker (ends : E → Sym2 V) (W : Finset V) (F : Finset E) (d : E → ℝ) : Prop :=
  (∀ e, e ∉ F → d e = 0) ∧ ∀ v ∈ W, ∑ e ∈ gcut ends F {v}, d e = 0
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
section Hull
variable [Fintype E]
end Hull
end MatchingPolytope.Multi


