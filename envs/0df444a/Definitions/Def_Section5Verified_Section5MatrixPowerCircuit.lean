-- Prove2me | Definitions.Def_Section5Verified_Section5MatrixPowerCircuit
-- name    : Section5Verified_Section5MatrixPowerCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:17.895266+00:00
-- url     : https://prove2.me/theorems/80fc2331-35f3-5344-bf56-a86555e87fb3
-- title:
--   Section5MatrixPowerCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5MatrixPowerCircuit; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5ModularMatrixPowers
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! A complete circuit for repeated matrix multiplication at a fixed precision.
Earlier matrix registers are retained as reversible workspace. -/

def section5_flatten_matrix_register {m n w : ℕ}
    (p : Fin (2*n*n) → Fin w ↪ Fin m) : Fin ((2*n*n)*w) → Fin m :=
  fun j => p (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2



noncomputable def section5_decode_flat_matrix {n w : ℕ}
    (z : Qubits ((2*n*n)*w)) : Section5ModMatrix n w :=
  section5_mod_matrix_from_components (fun i =>
    (bitsToNatLSB (fun j => z (finProdFinEquiv (i,j))):ZMod (2^w)))









end


