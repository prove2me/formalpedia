-- Prove2me | Definitions.Def_Section5Verified_Section5OrientationAmplification
-- name    : Section5Verified_Section5OrientationAmplification
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:21:29.173681+00:00
-- url     : https://prove2.me/theorems/a0b335f4-02f4-4c2a-ae7e-b5dad7c2dd95
-- title:
--   Section5OrientationAmplification — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5OrientationAmplification; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Three finite-QEX votes amplify orientation success, for either sign. -/

noncomputable def section5_qex_distribution (n q : ℕ) (z : Qubits (n*q)) : ℝ :=
  gridWeight z/(∑ x : Qubits (n*q), gridWeight x)





def section5_orientation_error {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n))
    (flip : Bool) (z : Qubits (n*q)) : Prop :=
  if flip then ltf w 0 (gridPoint z)=ltf u 0 (gridPoint z)
  else ltf w 0 (gridPoint z)≠ltf u 0 (gridPoint z)





end


