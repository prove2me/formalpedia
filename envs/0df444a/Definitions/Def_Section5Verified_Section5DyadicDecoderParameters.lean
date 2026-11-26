-- Prove2me | Definitions.Def_Section5Verified_Section5DyadicDecoderParameters
-- name    : Section5Verified_Section5DyadicDecoderParameters
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:40:58.698095+00:00
-- url     : https://prove2.me/theorems/dec2d808-06ac-405d-8772-9e4ac35cb3cd
-- title:
--   Section5DyadicDecoderParameters — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5DyadicDecoderParameters; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5ReconstructionPrecision
import Mathlib
section
set_option autoImplicit false

/-! Uniform polynomial-width parameters for integer powers and dyadic output.
The output precision is linear in the iteration count, even though the lower
bound on the unnormalized column is exponentially small in that count. -/

noncomputable def section5_decoder_iterations (n : ℕ) (ε : ℝ) : ℕ :=
  section5_binary_precision (800*n/ε)

noncomputable def section5_decoder_fraction_bits (n : ℕ) (ε : ℝ) : ℕ :=
  2*(section5_decoder_iterations n ε+1)+section5_binary_precision (144*(n:ℝ)^2/ε)

noncomputable def section5_decoder_integer_width (n : ℕ) (ε : ℝ) : ℕ :=
  (section5_decoder_iterations n ε+1)*
    (section5_decoder_fraction_bits n ε+section5_binary_precision n+3)+2







end


