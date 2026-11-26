-- Prove2me | Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
-- name    : Section5Verified_Section5ThreeQEXMeasurement
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:37:45.630156+00:00
-- url     : https://prove2.me/theorems/d12978f1-e6b4-4e05-a3fa-1de9625a9516
-- title:
--   Section5ThreeQEXMeasurement — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ThreeQEXMeasurement; mechanically extracted with exact Lean declaration spans.

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
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership



noncomputable def section5_three_qex_state {n q : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)) :=
  tensorVec (qexKet (q:=q) w) (tensorVec (qexKet (q:=q) w) (qexKet (q:=q) w))

noncomputable def section5_labelled_qex_outcome {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (x : Qubits (n*q)) : Qubits (n*q+1) :=
  Fin.snoc x (decide (ltf w 0 (gridPoint x)= -1))

noncomputable def section5_labelled_three_qex_outcome {n q : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) (x : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) :
    Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1) :=
  (section5_labelled_qex_outcome w x.1,section5_labelled_qex_outcome w x.2.1,
    section5_labelled_qex_outcome w x.2.2)





end


