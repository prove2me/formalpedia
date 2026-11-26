-- Prove2me | Definitions.Def_Section5Verified_Section5DyadicVectorOutput
-- name    : Section5Verified_Section5DyadicVectorOutput
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:58.222881+00:00
-- url     : https://prove2.me/theorems/addb7315-9790-45e3-b3c6-15532acc9f01
-- title:
--   Section5DyadicVectorOutput — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5DyadicVectorOutput; mechanically extracted with exact Lean declaration spans.

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

/-! The dyadic wire-selection circuit implements the same floor quantization
used in the analytic reconstruction guarantee, including negative coordinates. -/









noncomputable def section5_signed_dyadic_vector {r N d : ℕ}
    (src : Fin N → Fin (d+1) ↪ Fin r) (S : ℕ) (z : Qubits r) :
    EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 fun i => ((2:ℝ)^S)⁻¹*
    (section5_integer_bit_value (section5_twos_coefficient (d+1)) (z ∘ src i):ℝ)



end


