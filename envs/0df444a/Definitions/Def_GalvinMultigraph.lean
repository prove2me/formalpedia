-- Prove2me | Definitions.Def_GalvinMultigraph
-- name    : GalvinMultigraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:21:56.130437+00:00
-- url     : https://prove2.me/theorems/433bc42e-5a4f-417b-9dcd-3d24ad188d41
-- title:
--   Galvin Multigraph
-- statement:
--   Definitions and structural lemmas for Galvin Multigraph, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph.lean

module
public import Definitions.Def_GalvinMultigraph_Main
public import Definitions.Def_GalvinMultigraph_Local_Bridge
set_option autoImplicit true
@[expose] public section


