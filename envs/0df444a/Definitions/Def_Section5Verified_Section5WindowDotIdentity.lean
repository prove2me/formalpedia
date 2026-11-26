-- Prove2me | Definitions.Def_Section5Verified_Section5WindowDotIdentity
-- name    : Section5Verified_Section5WindowDotIdentity
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:03.563665+00:00
-- url     : https://prove2.me/theorems/3339fe2e-b95f-466d-99d8-28c8a1e4ab71
-- title:
--   Section5WindowDotIdentity — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5WindowDotIdentity; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5MiddleBits
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm49Primitives

/-! The bounded-precision sign comparison is an exact integer dot product using the
public fixed-point and Gaussian-grid encodings. -/







def section5_window_integer_dot {n q a : ℕ} (u : Fin n → Qubits (a+1))
    (z : Qubits (n*q)) (s b : ℕ) (h : s+(b+1) ≤ q-1) : ℤ :=
  ∑ i, ((bitsToNatLSB (fun j => u i j.rev):ℤ)-(2:ℤ)^a)*
    section5_integer_bit_value (section5_twos_coefficient (b+1))
      (section5_middle_bits (splitReg n q z i) s (b+1) (by omega))





end


