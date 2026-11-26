-- Prove2me | Definitions.Def_Section5Verified_Section5AffineCopy
-- name    : Section5Verified_Section5AffineCopy
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:05.931361+00:00
-- url     : https://prove2.me/theorems/afc2d20d-4b83-5918-92e4-f7fd159aa462
-- title:
--   Section5AffineCopy — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5AffineCopy; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm410Router

/-! An affine copy of arbitrarily selected input bits into a disjoint register.
Each output takes at most two reversible gates, even if input bits are repeated. -/

def section5_affine_bit {m w : ℕ} (src : Fin w → Fin m) (neg : Fin w → Bool)
    (z : Qubits m) (i : Fin w) : Bool := if neg i then !(z (src i)) else z (src i)

noncomputable def section5_affine_prefix_state {m w : ℕ} (src : Fin w → Fin m)
    (dst : Fin w ↪ Fin m) (neg : Fin w → Bool) (k : ℕ) (z : Qubits m) : Qubits m :=
  updateOn dst z (fun i => if i.val < k then xor (z (dst i)) (section5_affine_bit src neg z i) else z (dst i))

def section5_affine_copy_prefix {m w : ℕ} (src : Fin w → Fin m)
    (dst : Fin w ↪ Fin m) (neg : Fin w → Bool) (hdisj : ∀ i j, src i ≠ dst j) :
    (k : ℕ) → k ≤ w → Circuit gatesRev m
  | 0,_ => []
  | k+1,hk =>
    section5_affine_copy_prefix src dst neg hdisj k (by omega) ++
      section5_boolean_gate_circuit (if neg ⟨k,by omega⟩ then .not else .and)
        (src ⟨k,by omega⟩) (src ⟨k,by omega⟩) (dst ⟨k,by omega⟩)
        (hdisj _ _) (hdisj _ _)







end


