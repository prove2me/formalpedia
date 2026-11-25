-- Prove2me | Definitions.Def_GalvinMultigraph_Local_Stable
-- name    : GalvinMultigraph_Local_Stable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:41:33.942798+00:00
-- url     : https://prove2.me/theorems/b144fe65-ac03-4aa5-a818-376358d9b6a9
-- title:
--   Stable
-- statement:
--   Definitions and structural lemmas for Stable, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Stable.lean

module
public import Definitions.Def_GalvinMultigraph_Local_Base
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Set
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


