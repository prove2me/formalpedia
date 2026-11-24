-- Prove2me | Definitions.Def_RequestProject_RecoverP
-- name    : RequestProject_RecoverP
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T11:22:33.146803+00:00
-- url     : https://prove2.me/theorems/5c71b075-76c3-49f9-a882-0c1f0747b406
-- title:
--   Recover P
-- statement:
--   Definitions and structural lemmas for Recover P, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean

import Definitions.Def_RequestProject_CompStructure
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
def mono (μ : Multiset ℕ) : MvPolynomial ℕ ℚ := monomial (Multiset.toFinsupp μ) 1
def lowerAt (W : Multiset ℕ) (a : ℕ) : Multiset ℕ := (a - 1) ::ₘ W.erase a
def bigWeights (W : Multiset ℕ) : Finset ℕ := W.toFinset.filter (3 ≤ ·)
def fP (W : Multiset ℕ) : MvPolynomial ℕ ℚ :=
  ∑ a ∈ bigWeights W, C (((a - 1) * W.count a : ℕ) : ℚ) * mono (lowerAt W a)
def psum (j : ℕ) (μ : Multiset ℕ) : ℤ := (μ.map fun x : ℕ => ((x : ℤ) ^ j)).sum
end ChromaticReconstruction


