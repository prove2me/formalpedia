-- Prove2me | Definitions.Def_GalvinMultigraph_Local_Konig
-- name    : GalvinMultigraph_Local_Konig
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:45:53.471293+00:00
-- url     : https://prove2.me/theorems/2046bcd8-3738-4961-a975-a6317d6e6dfa
-- title:
--   Konig
-- statement:
--   Definitions and structural lemmas for Konig, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean

module
public import Definitions.Def_GalvinMultigraph_Local_Stable
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Set
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
namespace GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]
end GalvinMultigraph.Local


