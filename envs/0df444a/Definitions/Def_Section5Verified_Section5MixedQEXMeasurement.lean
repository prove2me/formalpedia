-- Prove2me | Definitions.Def_Section5Verified_Section5MixedQEXMeasurement
-- name    : Section5Verified_Section5MixedQEXMeasurement
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:40:45.7898+00:00
-- url     : https://prove2.me/theorems/f1a6f3f1-ece2-5c60-af28-de2da28a4116
-- title:
--   Section5MixedQEXMeasurement — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5MixedQEXMeasurement; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
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
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement QuantumLTF.Example
open scoped ComplexConjugate

/-! Three independent QEX states tensored with an arbitrary mixed data register.
Classical post-processing depends only on the diagonal data probabilities; the
proof retains all input coherences and does not assume an intermediate measurement. -/

noncomputable def section5_mixed_qex_density {ι α : Type*} {n q : ℕ}
    (E : ι ≃ α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)))
    (σ : Matrix α α ℂ) (w : EuclideanSpace ℝ (Fin n)) : Matrix ι ι ℂ :=
  fun y z => σ (E y).1 (E z).1*section5_three_qex_state (q:=q) w (E y).2*
    conj (section5_three_qex_state (q:=q) w (E z).2)





end


