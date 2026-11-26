-- Prove2me | Definitions.Def_Section5Verified_Section5MajorityCircuit
-- name    : Section5Verified_Section5MajorityCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:13.761322+00:00
-- url     : https://prove2.me/theorems/d7291f4e-cd03-5bc9-8029-8b004bd3af24
-- title:
--   Section5MajorityCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5MajorityCircuit; mechanically extracted with exact Lean declaration spans.

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

/-! A majority decision compiled to exactly three reversible Toffoli gates. -/



def section5_majority_circuit {m : ℕ} (v : Fin 3 ↪ Fin m) (t : Fin m)
    (ht : t ∉ Set.range v) : Circuit gatesRev m :=
  [section5_rev_toffoli (section5_boolean_wire3 (v 0) (v 1) t
      (v.injective.ne (by decide)) (fun h => ht ⟨0,h⟩) (fun h => ht ⟨1,h⟩)),
    section5_rev_toffoli (section5_boolean_wire3 (v 0) (v 2) t
      (v.injective.ne (by decide)) (fun h => ht ⟨0,h⟩) (fun h => ht ⟨2,h⟩)),
    section5_rev_toffoli (section5_boolean_wire3 (v 1) (v 2) t
      (v.injective.ne (by decide)) (fun h => ht ⟨1,h⟩) (fun h => ht ⟨2,h⟩))]





end


