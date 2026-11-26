-- Prove2me | Definitions.Def_Section5Verified_Section5ModularMatrixPowers
-- name    : Section5Verified_Section5ModularMatrixPowers
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:56.878207+00:00
-- url     : https://prove2.me/theorems/ba0fb7f8-8018-4654-a44a-2b13839c1d99
-- title:
--   Section5ModularMatrixPowers — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ModularMatrixPowers; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ComplexMatrixCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Mathlib
section
set_option autoImplicit false

open QAlgorithms Thm49Primitives

/-! Modular complex matrix powers. Working modulo a fixed output width avoids
an increase in register width at each multiplication. Signed decoding agrees with
the same residues; only the final integer output needs an overflow bound. -/

@[ext] structure Section5ModMatrix (n w : ℕ) where
  re : Matrix (Fin n) (Fin n) (ZMod (2^w))
  im : Matrix (Fin n) (Fin n) (ZMod (2^w))

def Section5ModMatrix.mul {n w : ℕ} (A B : Section5ModMatrix n w) : Section5ModMatrix n w :=
  ⟨A.re*B.re-A.im*B.im,A.re*B.im+A.im*B.re⟩

def Section5ModMatrix.one (n w : ℕ) : Section5ModMatrix n w := ⟨1,0⟩

def Section5ModMatrix.power {n w : ℕ} (A : Section5ModMatrix n w) : ℕ → Section5ModMatrix n w
  | 0 => .one n w
  | k+1 => (A.power k).mul A

def Section5IntegerMatrix.residue {n : ℕ} (A : Section5IntegerMatrix n) (w : ℕ) :
    Section5ModMatrix n w :=
  ⟨fun i j => (A.re i j:ZMod (2^w)),fun i j => (A.im i j:ZMod (2^w))⟩









noncomputable def section5_mod_matrix_from_components {n w : ℕ}
    (v : Fin (2*n*n) → ZMod (2^w)) : Section5ModMatrix n w :=
  ⟨fun i j => v ((section5_complex_entry_index n).symm (false,i,j)),
    fun i j => v ((section5_complex_entry_index n).symm (true,i,j))⟩

noncomputable def section5_mod_matrix_read {m n w : ℕ}
    (p : Fin (2*n*n) → Fin w ↪ Fin m) (z : Qubits m) : Section5ModMatrix n w :=
  section5_mod_matrix_from_components (fun i => (bitsToNatLSB (z ∘ p i):ZMod (2^w)))







end


