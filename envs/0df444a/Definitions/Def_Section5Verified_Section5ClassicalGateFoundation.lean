-- Prove2me | Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
-- name    : Section5Verified_Section5ClassicalGateFoundation
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:01:36.998277+00:00
-- url     : https://prove2.me/theorems/a3ce9f11-56da-5ddc-ae1f-4b7fe07cbcb2
-- title:
--   Section5ClassicalGateFoundation — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ClassicalGateFoundation; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QuantumLTF_Membership_gatesRev
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! The three reversible basis permutations, independent of channel estimates. -/

def section5_bit_flip : Equiv.Perm (Qubits 1) where
  toFun z := fun _ => !(z 0)
  invFun z := fun _ => !(z 0)
  left_inv z := by funext i; fin_cases i; simp
  right_inv z := by funext i; fin_cases i; simp

def section5_cnot_perm : Equiv.Perm (Qubits 2) where
  toFun z := ![z 0, xor (z 1) (z 0)]
  invFun z := ![z 0, xor (z 1) (z 0)]
  left_inv z := by funext i; fin_cases i <;> simp
  right_inv z := by funext i; fin_cases i <;> simp

def section5_toffoli_perm : Equiv.Perm (Qubits 3) where
  toFun z := ![z 0, z 1, xor (z 2) (z 0 && z 1)]
  invFun z := ![z 0, z 1, xor (z 2) (z 0 && z 1)]
  left_inv z := by funext i; fin_cases i <;> simp
  right_inv z := by funext i; fin_cases i <;> simp

end


