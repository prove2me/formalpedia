-- Prove2me | Definitions.Def_Section5Verified_Section5ExactMatrixPowerCircuit
-- name    : Section5Verified_Section5ExactMatrixPowerCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:53.1244+00:00
-- url     : https://prove2.me/theorems/7e0bf4cb-0151-4ad3-9381-0e4e8dd1a24f
-- title:
--   Section5ExactMatrixPowerCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ExactMatrixPowerCircuit; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Final signed decoding of the fixed-width matrix-power circuit. The register
width is linear in the number of products and the input/dimension bit bounds. -/



noncomputable def section5_signed_matrix_read {m n b : ℕ}
    (p : Fin (2*n*n) → Fin (b+1) ↪ Fin m) (z : Qubits m) : Section5IntegerMatrix n :=
  ⟨fun i j => section5_integer_bit_value (section5_twos_coefficient (b+1))
      (z ∘ p ((section5_complex_entry_index n).symm (false,i,j))),
    fun i j => section5_integer_bit_value (section5_twos_coefficient (b+1))
      (z ∘ p ((section5_complex_entry_index n).symm (true,i,j)))⟩







end


