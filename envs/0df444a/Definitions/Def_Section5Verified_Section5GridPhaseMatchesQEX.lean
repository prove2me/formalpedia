-- Prove2me | Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
-- name    : Section5Verified_Section5GridPhaseMatchesQEX
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:21:20.194523+00:00
-- url     : https://prove2.me/theorems/7f8ca992-6c5a-4409-9765-00933d1cfb7f
-- title:
--   Section5GridPhaseMatchesQEX — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5GridPhaseMatchesQEX; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership Aux_w_53_hermite

/-! The sampled phase vector is exactly the phase branch of the public QEX state. -/



noncomputable def section5_register_equiv (n q : ℕ) : (Fin n → Qubits q) ≃ Qubits (n*q) where
  toFun := flatReg n q
  invFun := splitReg n q
  left_inv z := by
    funext i j
    exact congrArg (fun p : Fin n × Fin q => z p.1 p.2) (finProdFinEquiv.symm_apply_apply (i,j))
  right_inv z := by
    funext k
    exact congrArg z (finProdFinEquiv.apply_symm_apply k)

















end


