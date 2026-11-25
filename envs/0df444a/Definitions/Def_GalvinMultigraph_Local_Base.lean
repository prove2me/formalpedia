-- Prove2me | Definitions.Def_GalvinMultigraph_Local_Base
-- name    : GalvinMultigraph_Local_Base
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:18.102225+00:00
-- url     : https://prove2.me/theorems/d0f412d2-5418-4f81-bda0-36b04580cd42
-- title:
--   Base
-- statement:
--   Definitions and structural lemmas for Base, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Base.lean

module
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
namespace GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]
def IsMatchingOn (left : E → U) (right : E → R) (M : Finset E) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → left e ≠ left f ∧ right e ≠ right f
def degLOn (left : E → U) (S : Finset E) (u : U) : ℕ := (S.filter fun e => left e = u).card
def degROn (right : E → R) (S : Finset E) (r : R) : ℕ := (S.filter fun e => right e = r).card
end GalvinMultigraph.Local


