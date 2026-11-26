-- Prove2me | Definitions.Def_Section5Verified_Section5EmbeddedClassicalArithmetic
-- name    : Section5Verified_Section5EmbeddedClassicalArithmetic
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:38.328852+00:00
-- url     : https://prove2.me/theorems/81fb7e8f-322c-4e4a-a601-7821afc0de58
-- title:
--   Section5EmbeddedClassicalArithmetic — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5EmbeddedClassicalArithmetic; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! Embedding clean reversible arithmetic in an arbitrary postprocessing register. -/







def section5_control_payload_embedding {m w : ℕ} (ctrl : Fin m) (p : Fin w ↪ Fin m)
    (hc : ∀ i, ctrl ≠ p i) : Fin (1+w) ↪ Fin m :=
  combineEmb (section5_boolean_wire1 ctrl) p (fun _ i => hc i)



end


