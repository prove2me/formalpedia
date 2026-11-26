-- Prove2me | Definitions.Def_Section5Verified_Section5DyadicBitOutput
-- name    : Section5Verified_Section5DyadicBitOutput
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:07:25.399144+00:00
-- url     : https://prove2.me/theorems/f66c8701-3077-4efc-9201-977f8cf64fda
-- title:
--   Section5DyadicBitOutput — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5DyadicBitOutput; mechanically extracted with exact Lean declaration spans.

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
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Power-of-two division and offset-binary conversion by wire selection and
one complemented bit. This avoids general division in the output decoder. -/

def section5_shifted_bits {W : ℕ} (s w : ℕ) (hfit : s+w ≤ W) (z : Qubits W) : Qubits w :=
  fun i => z ⟨s+i.val,by omega⟩



def section5_offset_top_bit (b : ℕ) (z : Qubits (b+1)) : Qubits (b+1) :=
  Function.update z (Fin.last b) (!(z (Fin.last b)))



def section5_dyadic_offset_bits {W : ℕ} (s b : ℕ) (hfit : s+(b+1) ≤ W)
    (z : Qubits W) : Qubits (b+1) :=
  section5_offset_top_bit b (section5_shifted_bits s (b+1) hfit z)





end


