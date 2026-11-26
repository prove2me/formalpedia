-- Prove2me | Definitions.Def_Section5Verified_Section5ScoredColumnMatrix
-- name    : Section5Verified_Section5ScoredColumnMatrix
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:48:08.395797+00:00
-- url     : https://prove2.me/theorems/02af0838-e842-4e00-bf5f-71b432d96c68
-- title:
--   Section5ScoredColumnMatrix — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ScoredColumnMatrix; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5RealCandidateCircuit
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! The selected payload is an actual maximal column of the original decoded
integer matrix. This connects the score/scan circuit to the direction decoder. -/

def section5_record_integer_matrix {m n R b : ℕ} (p : Fin n → Fin R ↪ Fin m)
    (re im : Fin (n*(b+1)) ↪ Fin R) (z : Qubits m) : Section5IntegerMatrix n :=
  ⟨fun i j => section5_integer_vector_read (re.trans (p j)) z i,
    fun i j => section5_integer_vector_read (im.trans (p j)) z i⟩





end


