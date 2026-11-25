-- Prove2me | Definitions.Def_RequestProject_TauBound
-- name    : RequestProject_TauBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:45:36.744801+00:00
-- url     : https://prove2.me/theorems/86a2a4bd-9ef3-4636-b348-708e0c2819d7
-- title:
--   Tau Bound
-- statement:
--   Definitions and structural lemmas for Tau Bound, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/TauBound.lean

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
def CloseLeaves {V : Type*} [Fintype V] (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ u v, u ≠ v ∧ G.degree u ≤ 1 ∧ G.degree v ≤ 1 ∧ ∃ w : G.Walk u v, w.length ≤ m
end ChromaticReconstruction


