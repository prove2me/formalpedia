-- Prove2me | Definitions.Def_Section5Verified_Section5QuantizedReconstruction
-- name    : Section5Verified_Section5QuantizedReconstruction
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:40:20.289477+00:00
-- url     : https://prove2.me/theorems/a9b325c2-33ce-5dfa-8545-1ecd7ea6fb3e
-- title:
--   Section5QuantizedReconstruction — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5QuantizedReconstruction; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Mathlib
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Operator-norm accuracy gives an explicit finite-bit real output, up to sign.
The spectral choice here is still noncomputable; this does not certify the runtime
of a classical spectral algorithm or construct the tomography measurement. -/

noncomputable def section5_larger_real_part {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  if ‖section5_imag_part v‖ ≤ ‖section5_real_part v‖ then
    section5_real_part v else section5_imag_part v





end


