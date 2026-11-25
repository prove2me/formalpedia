-- Prove2me | Definitions.Def_GalvinMultigraph_Local_Main
-- name    : GalvinMultigraph_Local_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:54:04.317664+00:00
-- url     : https://prove2.me/theorems/04d08d5e-18f7-48e1-a619-cd6fb9e8413a
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Main.lean

module
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Set
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_GalvinMultigraph_Local_Kernel
public import Definitions.Def_GalvinMultigraph_Local_Ranks
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
namespace GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E] [DecidableEq U] [DecidableEq R]
    [DecidableEq E]
def degL (left : E → U) (u : U) : ℕ := (Finset.univ.filter fun e => left e = u).card
def degR (right : E → R) (r : R) : ℕ := (Finset.univ.filter fun e => right e = r).card
end GalvinMultigraph.Local


