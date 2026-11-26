-- Prove2me | Definitions.Def_Section5Verified_Section5OrientationDecision
-- name    : Section5Verified_Section5OrientationDecision
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:26.307371+00:00
-- url     : https://prove2.me/theorems/10190687-15c5-48e6-a1f9-0b76c6ba134a
-- title:
--   Section5OrientationDecision — verified interface
-- statement:
--   Defines the actual quantized majority vote and its output direction. Proves orientation success >=27/32 given an estimate within epsilon/6 up to sign. Proves joint tomography/orientation success >=73/96 for any finite tomography transcript distribution whose direction estimate is good with probability >=11/12.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5OrientationDecision; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! The actual majority decision outputs a direction close to w, rather than merely
bounding an abstract error predicate. -/

def section5_majority_bit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

noncomputable def section5_quantized_vote {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n))
    (z : Qubits (n*q)) : Bool :=
  decide (ltf w 0 (gridPoint z) ≠ ltf u 0 (section5_bounded_window_vector q (gridPoint z)))

noncomputable def section5_oriented_direction {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n))
    (z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) : EuclideanSpace ℝ (Fin n) :=
  if section5_majority_bit (section5_quantized_vote w u z.1)
      (section5_quantized_vote w u z.2.1) (section5_quantized_vote w u z.2.2) then -u else u

def section5_quantized_majority_error {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n))
    (flip : Bool) (z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) : Prop :=
  (section5_quantized_orientation_error w u flip z.1 ∧ section5_quantized_orientation_error w u flip z.2.1) ∨
  (section5_quantized_orientation_error w u flip z.1 ∧ section5_quantized_orientation_error w u flip z.2.2) ∨
  (section5_quantized_orientation_error w u flip z.2.1 ∧ section5_quantized_orientation_error w u flip z.2.2)



noncomputable def section5_three_qex_weight (n q : ℕ)
    (z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) : ℝ :=
  section5_qex_distribution n q z.1*section5_qex_distribution n q z.2.1*
    section5_qex_distribution n q z.2.2









end


