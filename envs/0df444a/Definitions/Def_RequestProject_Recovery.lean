-- Prove2me | Definitions.Def_RequestProject_Recovery
-- name    : RequestProject_Recovery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T11:23:56.727006+00:00
-- url     : https://prove2.me/theorems/91a63112-c431-4a37-9486-f0b073096691
-- title:
--   Recovery
-- statement:
--   Definitions and structural lemmas for Recovery, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Recovery.lean

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
section General
variable {V : Type*} [Fintype V]
end General
variable {K : Type*} [Fintype K]
def masterTerm (m : K → ℕ) (F : Finset (Sym2 K)) : MvPolynomial ℕ ℚ :=
  ∑ i, (m i : MvPolynomial ℕ ℚ) * killP1 (∏ C ∈ compSets (F : Set (Sym2 K)),
    X ((∑ j ∈ C, (m j + 1)) - if i ∈ C then 1 else 0))
variable (S : SimpleGraph K) (m : K → ℕ)
def weightMS (m : K → ℕ) : Multiset ℕ := univ.val.map fun i => m i + 1
def edgeTypes (S : SimpleGraph K) (w : K → ℕ) : Multiset (Sym2 ℕ) :=
  S.edgeFinset.val.map (Sym2.map w)
end ChromaticReconstruction


