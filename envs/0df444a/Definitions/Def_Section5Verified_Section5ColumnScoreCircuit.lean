-- Prove2me | Definitions.Def_Section5Verified_Section5ColumnScoreCircuit
-- name    : Section5Verified_Section5ColumnScoreCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:03.091972+00:00
-- url     : https://prove2.me/theorems/e76a66e2-7338-51fa-a569-d56a387b4dfd
-- title:
--   Section5ColumnScoreCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ColumnScoreCircuit; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Exact squared column norms, computed into unsigned registers before the
maximum-record scan. The matrix input and shared arithmetic workspace are preserved. -/

def section5_complex_column_square {r n b : ℕ}
    (re im : Fin n → Fin n → Fin (b+1) → Fin r) (j : Fin n) (z : Qubits r) : ℤ :=
  ∑ i : Fin n,((section5_integer_bit_value (section5_twos_coefficient (b+1)) (z ∘ re i j))^2+
    (section5_integer_bit_value (section5_twos_coefficient (b+1)) (z ∘ im i j))^2)

def section5_column_score_wires {r n b : ℕ}
    (re im : Fin n → Fin n → Fin (b+1) → Fin r) (j : Fin n) :
    Fin (n+n) → Fin (b+1) → Fin r := Fin.addCases (fun i => re i j) (fun i => im i j)







end


