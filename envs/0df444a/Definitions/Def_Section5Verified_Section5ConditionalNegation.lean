-- Prove2me | Definitions.Def_Section5Verified_Section5ConditionalNegation
-- name    : Section5Verified_Section5ConditionalNegation
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:04:41.082852+00:00
-- url     : https://prove2.me/theorems/15520568-adbf-5dfa-84dc-b1e1738b239e
-- title:
--   Section5ConditionalNegation — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ConditionalNegation; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! Actual linear-size conditional two's-complement negation. The control and all
other registers are preserved, and the adder's workspace is returned to zero. -/







noncomputable def section5_conditional_negate {m w : ℕ} (ctrl : Fin m)
    (p : Fin w ↪ Fin m) (z : Qubits m) : Qubits m :=
  if z ctrl then updateOn p z (natToBitsLSB w (2^w-bitsToNatLSB (z ∘ p))) else z



end


