-- Prove2me | Definitions.Def_Section5Verified_Section5IntegerDotCircuit
-- name    : Section5Verified_Section5IntegerDotCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:28:02.755624+00:00
-- url     : https://prove2.me/theorems/ca8a4b72-060f-4f8e-8323-5560fa625c8d
-- title:
--   Section5IntegerDotCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5IntegerDotCircuit; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5BilinearAccumulator
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! An actual NOT/CNOT/Toffoli circuit for a binary integer dot product. The input
registers are preserved and the arithmetic and AND workspace is cleaned. -/

noncomputable def section5_dot_terms {m n a b : ℕ}
    (u : Fin n → Fin a → Fin m) (x : Fin n → Fin b → Fin m) :
    List (Section5BilinearTerm m) :=
  (Finset.univ : Finset (Fin n × Fin a × Fin b)).toList.map
    (fun j => ⟨u j.1 j.2.1,x j.1 j.2.2,2^(j.2.1.val+j.2.2.val)⟩)







end


