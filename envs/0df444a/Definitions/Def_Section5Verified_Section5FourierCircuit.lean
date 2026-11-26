-- Prove2me | Definitions.Def_Section5Verified_Section5FourierCircuit
-- name    : Section5Verified_Section5FourierCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:08:46.107436+00:00
-- url     : https://prove2.me/theorems/45dcce83-c936-490e-b79b-22aa95afa599
-- title:
--   Section5FourierCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5FourierCircuit; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_gates12
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Exact Fourier transforms in the mission's elementary gate set, reusing the
accepted QFT construction, and the centered Fourier convention for the QHO. -/





def section5_change_gate_set {S T : Set Gate} (h : S ⊆ T) {n : ℕ}
    (c : Circuit S n) : Circuit T n :=
  c.map (fun g => ⟨g.gate,h g.mem,g.wires⟩)







noncomputable def section5_centered_fourier (q : ℕ) : Matrix (Qubits q) (Qubits q) ℂ :=
  fun y z => Complex.exp (2*Real.pi*Complex.I*
    (((bitsToNat y:ℂ)-((2^(q-1):ℕ):ℂ))*((bitsToNat z:ℂ)-((2^(q-1):ℕ):ℂ)))/(2:ℂ)^q)/
      (Real.sqrt ((2:ℕ)^q):ℂ)





end


