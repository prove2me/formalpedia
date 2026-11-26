-- Prove2me | Definitions.Def_Section5Verified_Section5OffsetDotCircuit
-- name    : Section5Verified_Section5OffsetDotCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:43:55.642288+00:00
-- url     : https://prove2.me/theorems/b4abfcc3-76c4-5184-a831-b4717cc18785
-- title:
--   Section5OffsetDotCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5OffsetDotCircuit; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! Offset-binary fixed-point estimates need no physical recoding: accumulate their
ordinary binary value, then subtract the fixed midpoint times the second vector. -/

def section5_unsigned_coefficient (a : ℕ) (i : Fin a) : ℤ := (2:ℤ)^i.val



noncomputable def section5_offset_bias_terms {m n b : ℕ} (w a : ℕ)
    (x : Fin n → Fin (b+1) → Fin m) : List (Fin m × ℕ) :=
  (Finset.univ : Finset (Fin n × Fin (b+1))).toList.map
    (fun j => (x j.1 j.2,section5_residue_coefficient w
      (-(2:ℤ)^a*section5_twos_coefficient (b+1) j.2)))













end


