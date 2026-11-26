-- Prove2me | Definitions.Def_Section5Verified_Section5RealImagSelection
-- name    : Section5Verified_Section5RealImagSelection
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:18.384222+00:00
-- url     : https://prove2.me/theorems/ec038333-986c-516f-9dac-31c3ee7cf86c
-- title:
--   Section5RealImagSelection — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5RealImagSelection; mechanically extracted with exact Lean declaration spans.

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

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! Select the larger real/imaginary vector without square roots. A signed
sum-of-squares difference controls an actual reversible register swap. -/

def section5_signed_vector_square {m n b : ℕ} (A : Fin (n*(b+1)) ↪ Fin m)
    (z : Qubits m) : ℤ :=
  ∑ i : Fin n,(section5_integer_bit_value (section5_twos_coefficient (b+1))
    (fun e => z (A (finProdFinEquiv (i,e)))))^2

def section5_real_imag_wires {m n b : ℕ} (A B : Fin (n*(b+1)) ↪ Fin m) :
    Fin (n+n) → Fin (b+1) → Fin m :=
  Fin.addCases (fun i e => A (finProdFinEquiv (i,e)))
    (fun i e => B (finProdFinEquiv (i,e)))

def section5_real_imag_coefficients (n b : ℕ) : Fin (n+n) → Fin (b+1) → ℤ :=
  Fin.addCases (fun _ => section5_twos_coefficient (b+1))
    (fun _ e => -section5_twos_coefficient (b+1) e)







end


