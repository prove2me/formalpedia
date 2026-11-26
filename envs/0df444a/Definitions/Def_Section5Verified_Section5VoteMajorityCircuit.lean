-- Prove2me | Definitions.Def_Section5Verified_Section5VoteMajorityCircuit
-- name    : Section5Verified_Section5VoteMajorityCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:09.159721+00:00
-- url     : https://prove2.me/theorems/a4360866-e50a-55c8-b98c-e20a8d9067e2
-- title:
--   Section5VoteMajorityCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5VoteMajorityCircuit; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Three label disagreements and their majority require six reversible gates.
The predictor sign bits are reused as the three disagreement bits. -/





def section5_three_vote_xor_circuit {m : ℕ} (labels prediction : Fin 3 ↪ Fin m)
    (hdisj : ∀ i j, labels i ≠ prediction j) : Circuit gatesRev m :=
  [section5_rev_cnot (section5_boolean_wire2 (labels 0) (prediction 0) (hdisj 0 0)),
   section5_rev_cnot (section5_boolean_wire2 (labels 1) (prediction 1) (hdisj 1 1)),
   section5_rev_cnot (section5_boolean_wire2 (labels 2) (prediction 2) (hdisj 2 2))]



end


