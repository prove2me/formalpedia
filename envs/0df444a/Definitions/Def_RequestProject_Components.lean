-- Prove2me | Definitions.Def_RequestProject_Components
-- name    : RequestProject_Components
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:59:18.354702+00:00
-- url     : https://prove2.me/theorems/42f27387-02c1-424b-9bae-663cea004d04
-- title:
--   Components
-- statement:
--   Definitions and structural lemmas for Components, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Components.lean

import Definitions.Def_RequestProject_Defs
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]
end ChromaticReconstruction


