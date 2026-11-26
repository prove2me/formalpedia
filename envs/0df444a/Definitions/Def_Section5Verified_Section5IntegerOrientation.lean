-- Prove2me | Definitions.Def_Section5Verified_Section5IntegerOrientation
-- name    : Section5Verified_Section5IntegerOrientation
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:20:59.187821+00:00
-- url     : https://prove2.me/theorems/e373326a-8983-45c1-9605-91bd8282d5d1
-- title:
--   Section5IntegerOrientation — verified interface
-- statement:
--   Proves the fixed-point/grid inner product is a positive scalar times an explicit centered-integer dot product. Thus the orientation label can be computed by integer comparison; normalizing a nonzero hypothesis preserves its homogeneous label.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5IntegerOrientation; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Exact integer comparison for orientation: Gaussian grid scaling and fixed-point denominators
are positive and cancel from the sign test. -/

def section5_centered_integer {ℓ : ℕ} (z : Qubits ℓ) : ℤ :=
  (bitsToNat z : ℤ)-(2^(ℓ-1) : ℕ)







def section5_integer_orientation_dot {n q ℓ : ℕ}
    (u : Fin n → Qubits ℓ) (x : Qubits (n*q)) : ℤ :=
  ∑ i, section5_centered_integer (u i)*section5_centered_integer (splitReg n q x i)







end


