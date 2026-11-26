-- Prove2me | Definitions.Def_Section5Verified_Section5FixedPointQuantization
-- name    : Section5Verified_Section5FixedPointQuantization
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:40:48.266196+00:00
-- url     : https://prove2.me/theorems/76f6d040-132a-5b6a-9085-89a5223416a3
-- title:
--   Section5FixedPointQuantization — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5FixedPointQuantization; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Explicit public fixed-point rounding, with coordinate and normalized-vector
error guarantees. This is an encoding estimate, not an eigensolver circuit. -/

noncomputable def section5_quantize_integer (f : ℕ) (x : ℝ) : ℤ :=
  (2:ℤ)^(f+1)+⌊(2:ℝ)^f*x⌋

noncomputable def section5_quantize_bits (f : ℕ) (x : ℝ) : Qubits (f+2) :=
  section5_lsb_to_msb (Thm49Primitives.natToBitsLSB (f+2)
    (section5_quantize_integer f x).toNat)







noncomputable def section5_quantize_vector {n : ℕ} (f : ℕ)
    (r : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => fpVal (f+2) f (section5_quantize_bits f (r i))







end


