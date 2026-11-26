-- Prove2me | Definitions.Def_Section5Verified_Section5RealCandidateCircuit
-- name    : Section5Verified_Section5RealCandidateCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:13.770936+00:00
-- url     : https://prove2.me/theorems/b1529689-897b-49cd-a79a-e04ee4b6a0ef
-- title:
--   Section5RealCandidateCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5RealCandidateCircuit; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Exact integer-matrix semantics of the larger-part selection circuit.
Equality of squared norms retains the real part, as in realCandidateAt. -/

def section5_integer_vector_read {m n b : ℕ} (A : Fin (n*(b+1)) ↪ Fin m)
    (z : Qubits m) (i : Fin n) : ℤ :=
  section5_integer_bit_value (section5_twos_coefficient (b+1))
    (fun e => z (A (finProdFinEquiv (i,e))))

def section5_integer_vector_coordinate (n b : ℕ) (i : Fin n) :
    Fin (b+1) ↪ Fin (n*(b+1)) :=
  ⟨fun e => finProdFinEquiv (i,e),fun _ _ h => (Prod.mk.inj (finProdFinEquiv.injective h)).2⟩





end


