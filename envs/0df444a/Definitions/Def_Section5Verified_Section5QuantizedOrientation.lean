-- Prove2me | Definitions.Def_Section5Verified_Section5QuantizedOrientation
-- name    : Section5Verified_Section5QuantizedOrientation
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:46:37.929475+00:00
-- url     : https://prove2.me/theorems/ae51eecd-b473-44a7-bc88-8c2a307bd924
-- title:
--   Section5QuantizedOrientation — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5QuantizedOrientation; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Definitions.Def_Section5Verified_Section5RealWindow
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Actual finite-QEX orientation probabilities after the precision-independent
coordinate truncation. The three-vote error remains at most 5/32. -/

noncomputable def section5_bounded_window_vector {n : ℕ} (q : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  let B := section5_window_precision n
  section5_real_window_vec ((2:ℤ)^(q/2-B)) ((2:ℤ)^(2*B+1)) (gridSpacing (2^q)) x

def section5_quantized_orientation_error {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n))
    (flip : Bool) (z : Qubits (n*q)) : Prop :=
  if flip then ltf w 0 (gridPoint z)=ltf u 0 (section5_bounded_window_vector q (gridPoint z))
  else ltf w 0 (gridPoint z)≠ltf u 0 (section5_bounded_window_vector q (gridPoint z))









end


