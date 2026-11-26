-- Prove2me | Definitions.Def_Section5Verified_Section5WindowComparator
-- name    : Section5Verified_Section5WindowComparator
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:38:07.527417+00:00
-- url     : https://prove2.me/theorems/b5d9b2a5-77ef-5aed-b37c-0480ede0b3b2
-- title:
--   Section5WindowComparator — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5WindowComparator; mechanically extracted with exact Lean declaration spans.

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
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm49Primitives

/-! Register-level implementation of the public fixed-point/window comparison.
The oracle precision q occurs in wire addresses, not in the circuit size bound. -/

def section5_window_read_wire {n q m : ℕ} (e : Fin (n*q) ↪ Fin m)
    (s b : ℕ) (h : s+(b+1) ≤ q-1) (i : Fin n) (j : Fin (b+1)) : Fin m :=
  e (finProdFinEquiv (i,(⟨s+j.val,by omega⟩ : Fin q).rev))







end


