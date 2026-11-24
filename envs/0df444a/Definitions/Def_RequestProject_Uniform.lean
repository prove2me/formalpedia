-- Prove2me | Definitions.Def_RequestProject_Uniform
-- name    : RequestProject_Uniform
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T11:22:33.514278+00:00
-- url     : https://prove2.me/theorems/ba3a059d-7fa3-4874-bb33-0dc765a2c3e1
-- title:
--   Uniform
-- statement:
--   Definitions and structural lemmas for Uniform, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Uniform.lean

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
def psiQ (q : ℕ) : MvPolynomial ℕ ℚ →ₐ[ℚ] MvPolynomial ℕ ℚ := rename fun r => q * r
def opD (q N : ℕ) (f : MvPolynomial ℕ ℚ) : MvPolynomial ℕ ℚ :=
  killP1 (∑ r ∈ range N, C (r : ℚ) * X (q * r - 1) * psiQ q (pderiv r f))
variable {V : Type*} [Fintype V]
def innerSum (q : ℕ) (F : Finset (Sym2 V)) : MvPolynomial ℕ ℚ :=
  ∑ C0 ∈ compSets (F : Set (Sym2 V)), (C0.card : ℚ) •
    killP1 (X (q * C0.card - 1) * ∏ C ∈ (compSets (F : Set (Sym2 V))).erase C0, X (q * C.card))
end ChromaticReconstruction


