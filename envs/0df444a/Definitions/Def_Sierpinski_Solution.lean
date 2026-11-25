-- Prove2me | Definitions.Def_Sierpinski_Solution
-- name    : Sierpinski_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:48:24.862782+00:00
-- url     : https://prove2.me/theorems/fa34d913-b113-5d6f-a43e-1e5d98a17d32
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/sierpinski-closed-partition-lean; BoundaryBumping section reused under Apache-2.0 from Arthur742Ramos/boundary-bumping-lean; see pinned LICENSE and PROVENANCE.md)'s pinned Sierpinski Closed Partitions of Continua development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/sierpinski-closed-partition-lean/blob/406069edac48c4845bbf303ecc83ee9ef000b99a/Solution.lean

module
public import Mathlib.Topology.Separation.Regular
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
namespace BoundaryBumping
variable {X : Type*} [TopologicalSpace X]
end BoundaryBumping
universe u v w
namespace Sierpinski
variable {X : Type u} [tX : TopologicalSpace X] [t2X : T2Space X]
end Sierpinski


