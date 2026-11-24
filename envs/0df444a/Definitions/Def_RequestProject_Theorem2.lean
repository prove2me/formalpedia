-- Prove2me | Definitions.Def_RequestProject_Theorem2
-- name    : RequestProject_Theorem2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T11:24:24.362397+00:00
-- url     : https://prove2.me/theorems/f7446898-4118-4a81-ae9e-6afde5682279
-- title:
--   Theorem2
-- statement:
--   Definitions and structural lemmas for Theorem2, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theorem2.lean

import Definitions.Def_RequestProject_ChromCoeff
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]
def cFactor (q t : ℕ) : ℚ := (-1) ^ ((q - 1) * t - 1) * ((q - 1 : ℕ) : ℚ)
end ChromaticReconstruction


